"""
PyTorch optimization for K₇ metric parameters.

Uses gradient descent to optimize compactification parameters
that minimize χ² between GIFT predictions and experimental data.

Inspired by S2 (2-sphere) metric optimization in string theory,
adapted to the 7-dimensional K₇ manifold with G₂ holonomy.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Callable
import math

__all__ = [
    'TORCH_AVAILABLE', 'require_torch',
    'DifferentiableObservables', 'ChiSquaredLoss', 'TopologicalConstraintLoss',
    'OptimizationResult', 'K7MetricOptimizer',
    'multi_start_optimization', 'optimize_k7_metric',
    'scan_parameter_space', 'find_optimal_kappa_t',
]

try:
    import torch
    import torch.nn as nn
    import torch.optim as optim
    TORCH_AVAILABLE = True
except ImportError:
    TORCH_AVAILABLE = False
    torch = None
    nn = None
    optim = None

from gift_core.constants import (
    B2, B3, DIM_G2, DIM_K7, DIM_E8, DIM_E8xE8, H_STAR, P2,
    KAPPA_T, SIN2_THETA_W
)
from gift_core.experimental import (
    SIN2_THETA_W_EXP, DELTA_CP_EXP, M_TAU_M_E_EXP, Q_KOIDE_EXP,
    M_S_M_D_EXP
)


def require_torch():
    """Raise ImportError if torch is not available."""
    if not TORCH_AVAILABLE:
        raise ImportError(
            "PyTorch is required for optimization. "
            "Install with: pip install torch"
        )


# =============================================================================
# DIFFERENTIABLE OBSERVABLES
# =============================================================================

# Base class for nn.Module (stub if torch not available)
_ModuleBase = nn.Module if TORCH_AVAILABLE else object


class DifferentiableObservables(_ModuleBase):
    """
    Compute GIFT observables with differentiable parameters.

    The K₇ metric is parameterized by:
    - α: Betti number scaling (b₂, b₃ perturbation)
    - β: G₂ holonomy deformation
    - γ: Torsion coupling strength

    These parameters modify the effective topological invariants
    while preserving the underlying mathematical structure.
    """

    def __init__(self):
        require_torch()
        super().__init__()

        # Learnable metric parameters (small perturbations around 1.0)
        self.alpha = nn.Parameter(torch.tensor(1.0))  # Betti scaling
        self.beta = nn.Parameter(torch.tensor(1.0))   # G₂ deformation
        self.gamma = nn.Parameter(torch.tensor(1.0))  # Torsion coupling

        # Base topological values (fixed)
        self.register_buffer('b2_base', torch.tensor(float(B2)))
        self.register_buffer('b3_base', torch.tensor(float(B3)))
        self.register_buffer('dim_g2_base', torch.tensor(float(DIM_G2)))
        self.register_buffer('dim_e8_base', torch.tensor(float(DIM_E8)))
        self.register_buffer('dim_e8xe8_base', torch.tensor(float(DIM_E8xE8)))
        self.register_buffer('dim_j3o_base', torch.tensor(27.0))
        self.register_buffer('p2_base', torch.tensor(float(P2)))

    @property
    def b2(self) -> torch.Tensor:
        """Effective b₂ with α perturbation."""
        return self.b2_base * self.alpha

    @property
    def b3(self) -> torch.Tensor:
        """Effective b₃ with α perturbation."""
        return self.b3_base * self.alpha

    @property
    def dim_g2(self) -> torch.Tensor:
        """Effective dim(G₂) with β perturbation."""
        return self.dim_g2_base * self.beta

    @property
    def h_star(self) -> torch.Tensor:
        """Effective H* = b₂ + b₃ + 1."""
        return self.b2 + self.b3 + 1

    def sin2_theta_w(self) -> torch.Tensor:
        """sin²θ_W = b₂/(b₃ + dim_G₂)."""
        return self.b2 / (self.b3 + self.dim_g2)

    def kappa_t(self) -> torch.Tensor:
        """κ_T = γ/(b₃ - dim_G₂ - p₂)."""
        denom = self.b3 - self.dim_g2 - self.p2_base
        return self.gamma / denom

    def tau(self) -> torch.Tensor:
        """τ = (dim_E₈×E₈ × b₂)/(dim_J₃(O) × H*)."""
        return (self.dim_e8xe8_base * self.b2) / (self.dim_j3o_base * self.h_star)

    def q_koide(self) -> torch.Tensor:
        """Q_Koide = dim_G₂/b₂."""
        return self.dim_g2 / self.b2

    def delta_cp(self) -> torch.Tensor:
        """δ_CP = 7 × dim_G₂ + H*."""
        return 7 * self.dim_g2 + self.h_star

    def m_tau_m_e(self) -> torch.Tensor:
        """m_τ/m_e = 7 + 10×dim_E₈ + 10×H*."""
        return 7 + 10 * self.dim_e8_base + 10 * self.h_star

    def m_s_m_d(self) -> torch.Tensor:
        """m_s/m_d = 4×5 (topologically fixed, but with β correction)."""
        return 20.0 * self.beta

    def forward(self) -> Dict[str, torch.Tensor]:
        """Compute all observables."""
        return {
            'sin2_theta_w': self.sin2_theta_w(),
            'kappa_t': self.kappa_t(),
            'tau': self.tau(),
            'q_koide': self.q_koide(),
            'delta_cp': self.delta_cp(),
            'm_tau_m_e': self.m_tau_m_e(),
            'm_s_m_d': self.m_s_m_d(),
        }

    def parameter_summary(self) -> str:
        """Return current parameter values."""
        return (
            f"α (Betti): {self.alpha.item():.6f}\n"
            f"β (G₂):    {self.beta.item():.6f}\n"
            f"γ (torsion): {self.gamma.item():.6f}"
        )


# =============================================================================
# LOSS FUNCTIONS
# =============================================================================

class ChiSquaredLoss(_ModuleBase):
    """
    χ² loss comparing predictions to experimental data.

    χ² = Σᵢ [(pred_i - exp_i) / σ_i]²

    Supports weighted observables and regularization.
    """

    def __init__(self, include_regularization: bool = True, reg_strength: float = 0.1):
        require_torch()
        super().__init__()
        self.include_regularization = include_regularization
        self.reg_strength = reg_strength

        # Experimental values and uncertainties
        self.exp_data = {
            'sin2_theta_w': (SIN2_THETA_W_EXP.value, SIN2_THETA_W_EXP.error),
            'q_koide': (Q_KOIDE_EXP.value, Q_KOIDE_EXP.error),
            'delta_cp': (DELTA_CP_EXP.value, DELTA_CP_EXP.error),
            'm_tau_m_e': (M_TAU_M_E_EXP.value, M_TAU_M_E_EXP.error),
            'm_s_m_d': (M_S_M_D_EXP.value, M_S_M_D_EXP.error),
        }

    def forward(self, predictions: Dict[str, torch.Tensor],
                model: Optional[DifferentiableObservables] = None) -> torch.Tensor:
        """
        Compute χ² loss.

        Args:
            predictions: Dict of observable name -> tensor value
            model: Optional model for regularization

        Returns:
            Total χ² loss
        """
        chi2 = torch.tensor(0.0)

        for name, (exp_val, exp_err) in self.exp_data.items():
            if name in predictions:
                pred = predictions[name]
                pull = (pred - exp_val) / exp_err
                chi2 = chi2 + pull ** 2

        # Regularization: keep parameters close to 1.0
        if self.include_regularization and model is not None:
            reg = (
                (model.alpha - 1.0) ** 2 +
                (model.beta - 1.0) ** 2 +
                (model.gamma - 1.0) ** 2
            )
            chi2 = chi2 + self.reg_strength * reg

        return chi2


class TopologicalConstraintLoss(_ModuleBase):
    """
    Loss enforcing topological constraints.

    Ensures optimized parameters don't violate mathematical
    consistency (e.g., Betti numbers must be positive integers
    in the limit).
    """

    def __init__(self, strength: float = 1.0):
        require_torch()
        super().__init__()
        self.strength = strength

    def forward(self, model: DifferentiableObservables) -> torch.Tensor:
        """Compute constraint violation loss."""
        loss = torch.tensor(0.0)

        # b₂ and b₃ should stay positive
        loss = loss + torch.relu(-model.b2) + torch.relu(-model.b3)

        # dim(G₂) should stay positive
        loss = loss + torch.relu(-model.dim_g2)

        # κ_T denominator should not cross zero
        denom = model.b3 - model.dim_g2 - model.p2_base
        loss = loss + torch.relu(1.0 - denom)  # denom > 1

        # Parameters shouldn't deviate too far (0.5 to 2.0)
        for param in [model.alpha, model.beta, model.gamma]:
            loss = loss + torch.relu(0.5 - param)  # param > 0.5
            loss = loss + torch.relu(param - 2.0)   # param < 2.0

        return self.strength * loss


# =============================================================================
# OPTIMIZER
# =============================================================================

@dataclass
class OptimizationResult:
    """Result of K₇ metric optimization."""
    initial_chi2: float
    final_chi2: float
    alpha: float
    beta: float
    gamma: float
    predictions: Dict[str, float]
    history: List[float]
    converged: bool

    def improvement(self) -> float:
        """Percent improvement in χ²."""
        if self.initial_chi2 == 0:
            return 0.0
        return 100 * (self.initial_chi2 - self.final_chi2) / self.initial_chi2

    def summary(self) -> str:
        """Generate summary string."""
        lines = [
            "K₇ Metric Optimization Results",
            "=" * 60,
            f"Initial χ²: {self.initial_chi2:.4f}",
            f"Final χ²:   {self.final_chi2:.4f}",
            f"Improvement: {self.improvement():.2f}%",
            f"Converged: {'Yes' if self.converged else 'No'}",
            "",
            "Optimized Parameters:",
            f"  α (Betti scaling):  {self.alpha:.6f}",
            f"  β (G₂ deformation): {self.beta:.6f}",
            f"  γ (torsion):        {self.gamma:.6f}",
            "",
            "Final Predictions vs Experiment:",
        ]

        exp_data = {
            'sin2_theta_w': (SIN2_THETA_W_EXP.value, SIN2_THETA_W_EXP.error, "sin²θ_W"),
            'q_koide': (Q_KOIDE_EXP.value, Q_KOIDE_EXP.error, "Q_Koide"),
            'delta_cp': (DELTA_CP_EXP.value, DELTA_CP_EXP.error, "δ_CP"),
            'm_tau_m_e': (M_TAU_M_E_EXP.value, M_TAU_M_E_EXP.error, "m_τ/m_e"),
            'm_s_m_d': (M_S_M_D_EXP.value, M_S_M_D_EXP.error, "m_s/m_d"),
        }

        for key, (exp_val, exp_err, name) in exp_data.items():
            if key in self.predictions:
                pred = self.predictions[key]
                pull = (pred - exp_val) / exp_err
                lines.append(f"  {name:<10}: {pred:.6f} (exp: {exp_val:.6f}, pull: {pull:+.2f}σ)")

        lines.append("=" * 60)
        return "\n".join(lines)


class K7MetricOptimizer:
    """
    Gradient-based optimizer for K₇ metric parameters.

    Uses Adam optimizer to minimize χ² between GIFT predictions
    and PDG/NuFIT experimental data.
    """

    def __init__(
        self,
        lr: float = 0.01,
        max_iterations: int = 1000,
        convergence_threshold: float = 1e-6,
        regularization: float = 0.1,
        constraint_strength: float = 1.0,
        verbose: bool = False
    ):
        require_torch()
        self.lr = lr
        self.max_iterations = max_iterations
        self.convergence_threshold = convergence_threshold
        self.regularization = regularization
        self.constraint_strength = constraint_strength
        self.verbose = verbose

        self.model = DifferentiableObservables()
        self.chi2_loss = ChiSquaredLoss(
            include_regularization=True,
            reg_strength=regularization
        )
        self.constraint_loss = TopologicalConstraintLoss(strength=constraint_strength)
        self.optimizer = optim.Adam(self.model.parameters(), lr=lr)

    def optimize(self) -> OptimizationResult:
        """
        Run optimization loop.

        Returns:
            OptimizationResult with final parameters and predictions
        """
        history = []

        # Initial χ²
        with torch.no_grad():
            initial_preds = self.model()
            initial_chi2 = self.chi2_loss(initial_preds, self.model).item()

        prev_loss = float('inf')
        converged = False

        for i in range(self.max_iterations):
            self.optimizer.zero_grad()

            # Forward pass
            predictions = self.model()

            # Compute losses
            chi2 = self.chi2_loss(predictions, self.model)
            constraints = self.constraint_loss(self.model)
            total_loss = chi2 + constraints

            # Backward pass
            total_loss.backward()
            self.optimizer.step()

            # Record history
            current_chi2 = chi2.item()
            history.append(current_chi2)

            # Verbose output
            if self.verbose and (i + 1) % 100 == 0:
                print(f"  Iter {i+1}: χ² = {current_chi2:.6f}")

            # Check convergence
            if abs(prev_loss - current_chi2) < self.convergence_threshold:
                converged = True
                if self.verbose:
                    print(f"  Converged at iteration {i+1}")
                break

            prev_loss = current_chi2

        # Final predictions
        with torch.no_grad():
            final_preds = self.model()
            final_chi2 = self.chi2_loss(final_preds, self.model).item()
            pred_dict = {k: v.item() for k, v in final_preds.items()}

        return OptimizationResult(
            initial_chi2=initial_chi2,
            final_chi2=final_chi2,
            alpha=self.model.alpha.item(),
            beta=self.model.beta.item(),
            gamma=self.model.gamma.item(),
            predictions=pred_dict,
            history=history,
            converged=converged
        )

    def reset(self):
        """Reset parameters to initial values."""
        with torch.no_grad():
            self.model.alpha.fill_(1.0)
            self.model.beta.fill_(1.0)
            self.model.gamma.fill_(1.0)


# =============================================================================
# MULTI-START OPTIMIZATION
# =============================================================================

def multi_start_optimization(
    n_starts: int = 10,
    lr: float = 0.01,
    max_iterations: int = 500,
    seed: Optional[int] = None,
    verbose: bool = False
) -> OptimizationResult:
    """
    Run multiple optimizations from random starting points.

    Returns the best result (lowest final χ²).
    """
    require_torch()

    if seed is not None:
        torch.manual_seed(seed)

    best_result = None
    best_chi2 = float('inf')

    for i in range(n_starts):
        if verbose:
            print(f"\nStart {i+1}/{n_starts}")

        optimizer = K7MetricOptimizer(
            lr=lr,
            max_iterations=max_iterations,
            verbose=verbose
        )

        # Random initialization (small perturbations around 1.0)
        with torch.no_grad():
            optimizer.model.alpha.fill_(0.9 + 0.2 * torch.rand(1).item())
            optimizer.model.beta.fill_(0.9 + 0.2 * torch.rand(1).item())
            optimizer.model.gamma.fill_(0.9 + 0.2 * torch.rand(1).item())

        result = optimizer.optimize()

        if result.final_chi2 < best_chi2:
            best_chi2 = result.final_chi2
            best_result = result

    return best_result


# =============================================================================
# CONVENIENCE FUNCTIONS
# =============================================================================

def optimize_k7_metric(verbose: bool = False) -> OptimizationResult:
    """
    Quick optimization of K₇ metric parameters.

    Returns:
        OptimizationResult with optimized parameters
    """
    require_torch()
    optimizer = K7MetricOptimizer(verbose=verbose)
    return optimizer.optimize()


def scan_parameter_space(
    param: str = 'alpha',
    n_points: int = 50,
    range_min: float = 0.8,
    range_max: float = 1.2
) -> Tuple[List[float], List[float]]:
    """
    Scan χ² as a function of one parameter.

    Args:
        param: Parameter to scan ('alpha', 'beta', or 'gamma')
        n_points: Number of scan points
        range_min: Minimum parameter value
        range_max: Maximum parameter value

    Returns:
        (parameter_values, chi2_values)
    """
    require_torch()

    model = DifferentiableObservables()
    loss_fn = ChiSquaredLoss(include_regularization=False)

    param_values = []
    chi2_values = []

    for i in range(n_points):
        val = range_min + (range_max - range_min) * i / (n_points - 1)
        param_values.append(val)

        with torch.no_grad():
            if param == 'alpha':
                model.alpha.fill_(val)
            elif param == 'beta':
                model.beta.fill_(val)
            elif param == 'gamma':
                model.gamma.fill_(val)

            preds = model()
            chi2 = loss_fn(preds).item()
            chi2_values.append(chi2)

            # Reset
            model.alpha.fill_(1.0)
            model.beta.fill_(1.0)
            model.gamma.fill_(1.0)

    return param_values, chi2_values


def find_optimal_kappa_t() -> Tuple[float, float]:
    """
    Find the γ value that minimizes χ² for κ_T prediction.

    Returns:
        (optimal_gamma, minimal_chi2)
    """
    require_torch()

    gammas, chi2s = scan_parameter_space(
        param='gamma',
        n_points=100,
        range_min=0.5,
        range_max=1.5
    )

    min_idx = chi2s.index(min(chi2s))
    return gammas[min_idx], chi2s[min_idx]


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    if not TORCH_AVAILABLE:
        print("PyTorch not available. Install with: pip install torch")
    else:
        print("Running K₇ metric optimization...\n")

        # Single optimization
        result = optimize_k7_metric(verbose=True)
        print("\n" + result.summary())

        # Multi-start
        print("\nRunning multi-start optimization...")
        best = multi_start_optimization(n_starts=5, verbose=False)
        print(f"\nBest result: χ² = {best.final_chi2:.4f}")
        print(f"Parameters: α={best.alpha:.4f}, β={best.beta:.4f}, γ={best.gamma:.4f}")
