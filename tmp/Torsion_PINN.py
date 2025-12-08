"""
GIFT v3.0 - Phase 3: Torsion PINN and ML Exploration

Physics-Informed Neural Network for torsional flows on T₆₁,
Monte Carlo 13-adic robustness analysis, and Fibonacci hidden mode explorer.

This module implements:
1. TorsionPINN: PINN for geodesic flow with torsion constraint
2. Adic13MonteCarlo: Robustness of Yukawas under 13-adic structure
3. FiboHiddenExplorer: Cascade analysis for hidden modes

Prerequisites: numpy, torch (optional), matplotlib (optional)
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional, Callable
import math
import warnings

# Try to import PyTorch, fall back to NumPy-only mode
try:
    import torch
    import torch.nn as nn
    import torch.optim as optim
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False
    warnings.warn("PyTorch not available. TorsionPINN will use NumPy fallback.")

# Try to import matplotlib for visualization
try:
    import matplotlib.pyplot as plt
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    warnings.warn("Matplotlib not available. Plots will be skipped.")

# Import GIFT Core v3.0 constants
from GIFT_Core_v3 import (
    KAPPA_T_INV, KAPPA_T, H_STAR, DIM_K7, DIM_G2, N_GEN, B2, B3,
    DIM_E8, P2, WEYL_FACTOR, DIM_J3O,
    MassTauElectronTheorem, T61Manifold, FiboLucasTriade, Adic13Structure
)


# =============================================================================
# SECTION 1: TORSION PINN - PHYSICS-INFORMED NEURAL NETWORK
# =============================================================================

if HAS_TORCH:
    class TorsionPINN(nn.Module):
        """
        Physics-Informed Neural Network for torsional geodesic flow.

        The network learns the torsion field T(x,λ) on T₆₁ subject to:
        - Geodesic equation: d²x/dλ² = (1/2) T ⊗ dx ⊗ dx
        - Torsion constraint: κ_T = 1/61
        - Mass constraint: ∫ T dV = m_τ/m_e = 3477

        Architecture:
        - Input: K7 coordinates (7D) + affine parameter λ
        - Output: T₆₁ torsion configuration (61D)
        """

        def __init__(self, input_dim: int = 8, hidden_dims: List[int] = None,
                     output_dim: int = 61, kappa_t: float = 1/61):
            super().__init__()

            if hidden_dims is None:
                hidden_dims = [128, 256, 256, 128]

            self.input_dim = input_dim   # 7 coords + 1 λ
            self.output_dim = output_dim  # dim(T₆₁) = 61
            self.kappa_t = kappa_t

            # Build MLP
            layers = []
            in_dim = input_dim

            for h_dim in hidden_dims:
                layers.append(nn.Linear(in_dim, h_dim))
                layers.append(nn.SiLU())  # Smooth activation
                in_dim = h_dim

            layers.append(nn.Linear(in_dim, output_dim))

            self.net = nn.Sequential(*layers)

            # Target values
            self.target_mass = 3477.0
            self.target_kappa_inv = 61.0

        def forward(self, x_lambda: torch.Tensor) -> torch.Tensor:
            """
            Forward pass: (x, λ) → T(x, λ)

            Args:
                x_lambda: Input tensor (N, 8) - [x1,...,x7, λ]

            Returns:
                Torsion field (N, 61)
            """
            return self.net(x_lambda)

        def torsion_field(self, x: torch.Tensor, lam: torch.Tensor) -> torch.Tensor:
            """Get torsion field at (x, λ)."""
            x_lambda = torch.cat([x, lam.unsqueeze(-1)], dim=-1)
            return self.forward(x_lambda)

        def geodesic_residual(self, x: torch.Tensor, lam: torch.Tensor) -> torch.Tensor:
            """
            Compute geodesic equation residual.

            d²x/dλ² - (1/2) κ_T ⊗ dx ⊗ dx should be zero.
            """
            x.requires_grad_(True)
            lam.requires_grad_(True)

            T = self.torsion_field(x, lam)

            # First derivative dx/dλ (using autograd)
            x_lambda = torch.cat([x, lam.unsqueeze(-1)], dim=-1)
            T_out = self.forward(x_lambda)

            # Simplified: compute norm-based residual
            # Full geodesic eq would require second derivatives
            dx = torch.autograd.grad(T_out.sum(), lam, create_graph=True)[0]

            # Torsion contribution
            torsion_term = self.kappa_t * torch.prod(dx.unsqueeze(-1), dim=-1)

            return torch.mean((T_out - torsion_term) ** 2)

        def physics_loss(self, x: torch.Tensor, lam: torch.Tensor) -> Dict[str, torch.Tensor]:
            """
            Compute physics-informed loss components.

            Returns dict with:
            - torsion_loss: Torsion coefficient constraint
            - mass_loss: Mass ratio constraint
            - geodesic_loss: Geodesic equation residual
            """
            T = self.torsion_field(x, lam)

            # Loss 1: Torsion coefficient κ_T = 1/61
            # Interpreted as mean inverse of T magnitude
            T_mag = torch.mean(torch.abs(T), dim=-1) + 1e-8
            kappa_pred = 1.0 / (torch.mean(T_mag) * self.target_kappa_inv)
            torsion_loss = (kappa_pred - self.kappa_t) ** 2

            # Loss 2: Mass constraint - product ~ 3477
            T_prod = torch.prod(torch.mean(T, dim=0) + 1.0)
            mass_loss = ((T_prod / 1000 - self.target_mass / 1000) ** 2)

            # Loss 3: Geodesic smoothness (simplified)
            # Penalize large second differences
            if T.shape[0] > 2:
                d2T = T[2:] - 2 * T[1:-1] + T[:-2]
                geodesic_loss = torch.mean(d2T ** 2)
            else:
                geodesic_loss = torch.tensor(0.0)

            return {
                'torsion': torsion_loss,
                'mass': mass_loss,
                'geodesic': geodesic_loss,
                'total': torsion_loss + mass_loss + 0.1 * geodesic_loss
            }

        def train_step(self, optimizer: optim.Optimizer, x: torch.Tensor,
                       lam: torch.Tensor) -> float:
            """Single training step."""
            optimizer.zero_grad()
            losses = self.physics_loss(x, lam)
            losses['total'].backward()
            optimizer.step()
            return losses['total'].item()


class TorsionPINNNumPy:
    """
    NumPy fallback for TorsionPINN when PyTorch is not available.

    Uses simple MLP with NumPy operations.
    """

    def __init__(self, input_dim: int = 8, hidden_dim: int = 64,
                 output_dim: int = 61, kappa_t: float = 1/61):
        self.input_dim = input_dim
        self.hidden_dim = hidden_dim
        self.output_dim = output_dim
        self.kappa_t = kappa_t

        # Initialize weights
        self.W1 = np.random.randn(input_dim, hidden_dim) * 0.1
        self.b1 = np.zeros(hidden_dim)
        self.W2 = np.random.randn(hidden_dim, hidden_dim) * 0.1
        self.b2 = np.zeros(hidden_dim)
        self.W3 = np.random.randn(hidden_dim, output_dim) * 0.1
        self.b3 = np.zeros(output_dim)

    def silu(self, x: np.ndarray) -> np.ndarray:
        """SiLU activation: x * sigmoid(x)"""
        return x / (1 + np.exp(-x))

    def forward(self, x_lambda: np.ndarray) -> np.ndarray:
        """Forward pass."""
        h1 = self.silu(x_lambda @ self.W1 + self.b1)
        h2 = self.silu(h1 @ self.W2 + self.b2)
        out = h2 @ self.W3 + self.b3
        return out

    def predict(self, x: np.ndarray, lam: np.ndarray) -> np.ndarray:
        """Predict torsion field."""
        x_lambda = np.concatenate([x, lam.reshape(-1, 1)], axis=-1)
        return self.forward(x_lambda)


# =============================================================================
# SECTION 2: MONTE CARLO 13-ADIC ROBUSTNESS
# =============================================================================

@dataclass
class Adic13MonteCarlo:
    """
    Monte Carlo simulation for 13-adic robustness of Yukawa couplings.

    Tests how Yukawa values propagate under 13-adic structure:
    - Sample residue classes mod 13
    - Propagate through mass relations
    - Check deviation from τ structure (mod 13 ≡ non-QR)

    The hypothesis: physical observables have specific 13-adic signatures
    that are robust under perturbations.
    """

    n_samples: int = 10000
    seed: Optional[int] = 42

    def __post_init__(self):
        if self.seed is not None:
            np.random.seed(self.seed)

        # 13-adic structure
        self.adic = Adic13Structure()
        self.qr_residues = np.array(sorted(self.adic.qr))  # [0,1,3,4,9,10,12]
        self.non_qr_residues = np.array(sorted(self.adic.non_qr))  # [2,5,6,7,8,11]

        # Results storage
        self.results = {
            'samples': [],
            'tau_mod13': [],
            'deviations': [],
            'preserved_structure': []
        }

    def sample_residue(self, mode: str = 'uniform') -> int:
        """
        Sample a residue mod 13.

        Modes:
        - 'uniform': Uniform over all residues
        - 'qr': Quadratic residues only
        - 'non_qr': Non-quadratic residues only
        - 'physical': Weighted by physical significance (τ ~ non-QR)
        """
        if mode == 'uniform':
            return np.random.randint(0, 13)
        elif mode == 'qr':
            return np.random.choice(self.qr_residues)
        elif mode == 'non_qr':
            return np.random.choice(self.non_qr_residues)
        elif mode == 'physical':
            # Weight non-QR residues higher (τ structure)
            weights = np.array([0.5 if r in self.adic.qr else 1.5 for r in range(13)])
            weights /= weights.sum()
            return np.random.choice(13, p=weights)
        else:
            return np.random.randint(0, 13)

    def propagate_yukawa(self, y_base: float, residue: int) -> float:
        """
        Propagate Yukawa coupling through 13-adic structure.

        y_prop = y_base × (1 + ε × residue/13)
        where ε is a small perturbation.
        """
        epsilon = 0.01  # 1% perturbation scale
        return y_base * (1 + epsilon * residue / 13)

    def compute_tau_mod13(self, y_tau: float, y_e: float) -> int:
        """
        Compute (m_τ/m_e) mod 13 from Yukawas.

        m_i ∝ y_i × v, so m_τ/m_e ∝ y_τ/y_e
        We encode: ratio × 1000, then mod 13
        """
        ratio = y_tau / y_e if y_e > 0 else 0
        encoded = int(ratio * 1000) % 13
        return encoded

    def run_simulation(self, y_tau_base: float = 0.0100,
                       y_e_base: float = 2.87e-6) -> Dict:
        """
        Run Monte Carlo simulation.

        Args:
            y_tau_base: Base τ Yukawa coupling
            y_e_base: Base e Yukawa coupling

        Returns:
            Dictionary with simulation results
        """
        for i in range(self.n_samples):
            # Sample perturbation residues
            res_tau = self.sample_residue('physical')
            res_e = self.sample_residue('physical')

            # Propagate Yukawas
            y_tau = self.propagate_yukawa(y_tau_base, res_tau)
            y_e = self.propagate_yukawa(y_e_base, res_e)

            # Compute ratio mod 13
            tau_mod = self.compute_tau_mod13(y_tau, y_e)

            # Check structure preservation
            # Target: τ ratio should maintain non-QR structure
            is_non_qr = tau_mod in self.non_qr_residues

            # Compute deviation from base ratio
            base_ratio = y_tau_base / y_e_base
            new_ratio = y_tau / y_e
            deviation = abs(new_ratio - base_ratio) / base_ratio

            # Store results
            self.results['samples'].append({
                'res_tau': res_tau,
                'res_e': res_e,
                'y_tau': y_tau,
                'y_e': y_e
            })
            self.results['tau_mod13'].append(tau_mod)
            self.results['deviations'].append(deviation)
            self.results['preserved_structure'].append(is_non_qr)

        return self._compute_statistics()

    def _compute_statistics(self) -> Dict:
        """Compute summary statistics."""
        deviations = np.array(self.results['deviations'])
        preserved = np.array(self.results['preserved_structure'])
        tau_mods = np.array(self.results['tau_mod13'])

        return {
            'n_samples': self.n_samples,
            'mean_deviation': np.mean(deviations),
            'std_deviation': np.std(deviations),
            'max_deviation': np.max(deviations),
            'preservation_rate': np.mean(preserved),
            'deviation_under_01pct': np.mean(deviations < 0.001),
            'mod13_distribution': {r: np.sum(tau_mods == r) for r in range(13)},
            'robustness_score': 1 - np.mean(deviations)
        }

    def summary(self) -> str:
        """Generate summary report."""
        stats = self._compute_statistics()

        lines = [
            "=" * 60,
            "Monte Carlo 13-Adic Robustness Analysis",
            "=" * 60,
            f"Samples: {stats['n_samples']}",
            "",
            f"Mean deviation:        {stats['mean_deviation']:.4%}",
            f"Std deviation:         {stats['std_deviation']:.4%}",
            f"Max deviation:         {stats['max_deviation']:.4%}",
            f"Deviation < 0.1%:      {stats['deviation_under_01pct']:.1%} of samples",
            "",
            f"Structure preservation: {stats['preservation_rate']:.1%}",
            f"Robustness score:      {stats['robustness_score']:.4f}",
            "",
            "Mod 13 distribution:",
        ]

        for r, count in stats['mod13_distribution'].items():
            marker = "QR" if r in self.adic.qr else "non-QR"
            lines.append(f"  {r:2d} ({marker:6s}): {count:5d} ({count/self.n_samples:.1%})")

        lines.append("=" * 60)
        return "\n".join(lines)


# =============================================================================
# SECTION 3: FIBONACCI HIDDEN MODE EXPLORER
# =============================================================================

@dataclass
class FiboHiddenExplorer:
    """
    Explorer for hidden modes via Fibonacci/Lucas cascade.

    Uses the triade structure 9-18-34 to predict:
    - Hidden sector masses
    - Sterile neutrino candidates
    - Gap modes in the spectrum

    Key mappings:
    - F₉ = 34 → hidden_dim
    - L₆ = 18 → duality gap
    - L₇ = 29 → sterile neutrino mass (MeV)?
    """

    max_n: int = 15

    def __post_init__(self):
        self.triade = FiboLucasTriade()

    @property
    def fibonacci_sequence(self) -> List[int]:
        """Get Fibonacci sequence up to max_n."""
        return self.triade.fibonacci[:self.max_n]

    @property
    def lucas_sequence(self) -> List[int]:
        """Get Lucas sequence up to max_n."""
        return self.triade.lucas[:self.max_n]

    def golden_ratio_powers(self, n: int = 10) -> List[float]:
        """Compute powers of golden ratio φ^k."""
        phi = (1 + np.sqrt(5)) / 2
        return [phi ** k for k in range(n)]

    def cascade_modes(self) -> List[Dict]:
        """
        Generate cascade of hidden modes from Fibonacci.

        Each mode has:
        - Index n
        - F_n, L_n values
        - Predicted mass scale
        - Physical interpretation
        """
        modes = []
        base_scale = 1.0  # MeV

        for n in range(1, self.max_n):
            F_n = self.fibonacci_sequence[n]
            L_n = self.lucas_sequence[n]

            # Mass predictions from different scalings
            mass_fibo = F_n * base_scale
            mass_lucas = L_n * base_scale

            mode = {
                'n': n,
                'F_n': F_n,
                'L_n': L_n,
                'mass_fibo_MeV': mass_fibo,
                'mass_lucas_MeV': mass_lucas,
                'ratio_L_F': L_n / F_n if F_n > 0 else float('inf'),
                'interpretation': self._interpret_mode(n, F_n, L_n)
            }
            modes.append(mode)

        return modes

    def _interpret_mode(self, n: int, F_n: int, L_n: int) -> str:
        """Physical interpretation of cascade mode."""
        interpretations = {
            3: "N_gen ~ F_4 = 3 (number of generations)",
            6: f"L_6 = {L_n} = duality gap (18)",
            7: f"L_7 = {L_n} → sterile neutrino mass? (~29 MeV)",
            8: f"F_8 = {F_n} = b₂ (second Betti number)",
            9: f"F_9 = {F_n} = hidden_dim (34)",
            12: f"F_12 = {F_n} = α_s denom² (144)",
        }
        return interpretations.get(n, "")

    def predict_sterile_masses(self) -> List[Dict]:
        """
        Predict sterile neutrino masses from Lucas numbers.

        Hypothesis: m_sterile ~ L_k × (1 MeV / N_gen)
        """
        predictions = []

        for k in range(5, 12):
            L_k = self.lucas_sequence[k]
            mass_MeV = L_k / N_GEN  # Scale by N_gen

            predictions.append({
                'k': k,
                'L_k': L_k,
                'mass_MeV': mass_MeV,
                'mass_keV': mass_MeV * 1000,
                'confidence': 'speculative'
            })

        return predictions

    def gap_mode_analysis(self) -> Dict:
        """
        Analyze the 18 GeV gap mode.

        The duality gap = 18 suggests a hidden mode at ~18 GeV.
        """
        gap = self.triade.gap_dual  # = 18

        return {
            'gap_value': gap,
            'gap_is_L6': gap == self.lucas_sequence[6],
            'predicted_mass_GeV': gap,
            'predicted_mass_MeV': gap * 1000,
            'interpretation': "Hidden scalar or pseudo-Nambu-Goldstone boson",
            'detection_channel': "Di-photon or di-tau resonance search"
        }

    def convolution_cascade(self, input_signal: np.ndarray = None) -> np.ndarray:
        """
        Apply Fibonacci convolution to simulate cascade dynamics.

        Uses np.convolve with Fibonacci kernel for spiral-like evolution.
        """
        if input_signal is None:
            # Default: Gaussian peak at hidden_dim
            x = np.linspace(0, 100, 500)
            input_signal = np.exp(-(x - 34)**2 / 10)

        # Fibonacci kernel (normalized)
        kernel = np.array(self.fibonacci_sequence[1:8], dtype=float)
        kernel /= kernel.sum()

        # Convolve
        output = np.convolve(input_signal, kernel, mode='same')

        return output

    def summary(self) -> str:
        """Generate cascade summary."""
        modes = self.cascade_modes()
        sterile = self.predict_sterile_masses()
        gap = self.gap_mode_analysis()

        lines = [
            "=" * 60,
            "Fibonacci/Lucas Hidden Mode Explorer",
            "=" * 60,
            "",
            "Cascade Modes:",
            f"{'n':>3} | {'F_n':>5} | {'L_n':>5} | {'L/F':>6} | Interpretation",
            "-" * 60,
        ]

        for m in modes[:12]:
            interp = m['interpretation'][:30] if m['interpretation'] else ""
            lines.append(
                f"{m['n']:3d} | {m['F_n']:5d} | {m['L_n']:5d} | "
                f"{m['ratio_L_F']:6.3f} | {interp}"
            )

        lines.extend([
            "",
            "Sterile Neutrino Predictions:",
        ])
        for s in sterile:
            lines.append(f"  L_{s['k']} = {s['L_k']:3d} → m_sterile ~ {s['mass_MeV']:.1f} MeV")

        lines.extend([
            "",
            "Gap Mode:",
            f"  Gap = {gap['gap_value']} = L_6",
            f"  Predicted mass: {gap['predicted_mass_GeV']} GeV",
            f"  Interpretation: {gap['interpretation']}",
            "",
            "=" * 60,
        ])

        return "\n".join(lines)


# =============================================================================
# SECTION 4: VISUALIZATION (if matplotlib available)
# =============================================================================

def plot_mc_results(mc: Adic13MonteCarlo, save_path: str = None):
    """Plot Monte Carlo results."""
    if not HAS_MATPLOTLIB:
        print("Matplotlib not available. Skipping plots.")
        return

    fig, axes = plt.subplots(1, 3, figsize=(15, 4))

    # Plot 1: Deviation histogram
    ax1 = axes[0]
    deviations = np.array(mc.results['deviations'])
    ax1.hist(deviations * 100, bins=50, color='steelblue', alpha=0.7)
    ax1.axvline(0.1, color='red', linestyle='--', label='0.1% threshold')
    ax1.set_xlabel('Deviation (%)')
    ax1.set_ylabel('Count')
    ax1.set_title('13-Adic Perturbation Deviations')
    ax1.legend()

    # Plot 2: Mod 13 distribution
    ax2 = axes[1]
    tau_mods = np.array(mc.results['tau_mod13'])
    residues = range(13)
    counts = [np.sum(tau_mods == r) for r in residues]
    colors = ['green' if r in mc.adic.qr else 'orange' for r in residues]
    ax2.bar(residues, counts, color=colors)
    ax2.set_xlabel('Residue mod 13')
    ax2.set_ylabel('Count')
    ax2.set_title('τ mod 13 Distribution\n(green=QR, orange=non-QR)')

    # Plot 3: Structure preservation over samples
    ax3 = axes[2]
    preserved = np.array(mc.results['preserved_structure'])
    cumulative_rate = np.cumsum(preserved) / (np.arange(len(preserved)) + 1)
    ax3.plot(cumulative_rate, color='purple')
    ax3.axhline(0.5, color='gray', linestyle='--', alpha=0.5)
    ax3.set_xlabel('Sample')
    ax3.set_ylabel('Cumulative Preservation Rate')
    ax3.set_title('Non-QR Structure Preservation')
    ax3.set_ylim(0, 1)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved plot to {save_path}")
    else:
        plt.show()

    plt.close()


def plot_fibo_cascade(explorer: FiboHiddenExplorer, save_path: str = None):
    """Plot Fibonacci cascade analysis."""
    if not HAS_MATPLOTLIB:
        print("Matplotlib not available. Skipping plots.")
        return

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: Fibonacci vs Lucas
    ax1 = axes[0, 0]
    n_vals = list(range(len(explorer.fibonacci_sequence)))
    ax1.semilogy(n_vals, explorer.fibonacci_sequence, 'o-', label='Fibonacci F_n')
    ax1.semilogy(n_vals, explorer.lucas_sequence, 's-', label='Lucas L_n')
    ax1.axhline(34, color='red', linestyle='--', alpha=0.5, label='hidden_dim = 34')
    ax1.axhline(18, color='orange', linestyle='--', alpha=0.5, label='gap = 18')
    ax1.set_xlabel('n')
    ax1.set_ylabel('Value')
    ax1.set_title('Fibonacci and Lucas Sequences')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Plot 2: Ratio L_n/F_n convergence to φ
    ax2 = axes[0, 1]
    ratios = []
    phi = (1 + np.sqrt(5)) / 2
    for i in range(1, len(explorer.fibonacci_sequence)):
        if explorer.fibonacci_sequence[i] > 0:
            ratios.append(explorer.lucas_sequence[i] / explorer.fibonacci_sequence[i])
        else:
            ratios.append(np.nan)
    ax2.plot(range(1, len(ratios)+1), ratios, 'o-', color='purple')
    ax2.axhline(phi, color='gold', linestyle='--', label=f'φ = {phi:.6f}')
    ax2.set_xlabel('n')
    ax2.set_ylabel('L_n / F_n')
    ax2.set_title('Ratio Convergence to Golden Ratio')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # Plot 3: Convolution cascade
    ax3 = axes[1, 0]
    x = np.linspace(0, 100, 500)
    input_signal = np.exp(-(x - 34)**2 / 20)
    output = explorer.convolution_cascade(input_signal)
    ax3.plot(x, input_signal, label='Input (peak at 34)', alpha=0.7)
    ax3.plot(x, output, label='Fibonacci convolved', alpha=0.7)
    ax3.axvline(34, color='red', linestyle='--', alpha=0.3)
    ax3.axvline(18, color='orange', linestyle='--', alpha=0.3)
    ax3.set_xlabel('Mode number')
    ax3.set_ylabel('Amplitude')
    ax3.set_title('Fibonacci Cascade Convolution')
    ax3.legend()

    # Plot 4: Mass predictions
    ax4 = axes[1, 1]
    modes = explorer.cascade_modes()
    n_vals = [m['n'] for m in modes]
    fibo_masses = [m['mass_fibo_MeV'] for m in modes]
    lucas_masses = [m['mass_lucas_MeV'] for m in modes]
    ax4.bar(np.array(n_vals) - 0.2, fibo_masses, 0.4, label='Fibo mass', alpha=0.7)
    ax4.bar(np.array(n_vals) + 0.2, lucas_masses, 0.4, label='Lucas mass', alpha=0.7)
    ax4.set_xlabel('n')
    ax4.set_ylabel('Mass (MeV)')
    ax4.set_title('Predicted Hidden Masses')
    ax4.legend()
    ax4.set_yscale('log')

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved plot to {save_path}")
    else:
        plt.show()

    plt.close()


# =============================================================================
# SECTION 5: MAIN EXECUTION
# =============================================================================

def run_torsion_pinn_demo(n_epochs: int = 100, n_samples: int = 256):
    """Run TorsionPINN demonstration."""
    print("\n" + "=" * 60)
    print("TorsionPINN Demonstration")
    print("=" * 60)

    if HAS_TORCH:
        print("Using PyTorch backend")

        # Create model
        model = TorsionPINN()

        # Generate training data (K7 coords + λ)
        x = torch.randn(n_samples, 7)  # K7 coordinates
        lam = torch.rand(n_samples)    # Affine parameter

        # Optimizer
        optimizer = optim.Adam(model.parameters(), lr=1e-3)

        # Training loop
        print(f"\nTraining for {n_epochs} epochs...")
        losses = []
        for epoch in range(n_epochs):
            loss = model.train_step(optimizer, x, lam)
            losses.append(loss)

            if (epoch + 1) % 20 == 0:
                print(f"  Epoch {epoch+1:4d}: Loss = {loss:.6f}")

        # Final evaluation
        with torch.no_grad():
            T = model.torsion_field(x[:10], lam[:10])
            print(f"\nSample torsion field shape: {T.shape}")
            print(f"Mean torsion magnitude: {T.abs().mean().item():.4f}")
            print(f"Final loss: {losses[-1]:.6f}")

    else:
        print("Using NumPy fallback")

        model = TorsionPINNNumPy()

        # Generate data
        x = np.random.randn(n_samples, 7)
        lam = np.random.rand(n_samples)

        # Forward pass only (no training in NumPy mode)
        T = model.predict(x[:10], lam[:10])
        print(f"\nSample torsion field shape: {T.shape}")
        print(f"Mean torsion magnitude: {np.abs(T).mean():.4f}")


def main():
    """Main execution of Phase 3."""
    print("=" * 70)
    print("GIFT v3.0 - Phase 3: Torsion PINN and ML Exploration")
    print("=" * 70)

    # 1. TorsionPINN Demo
    run_torsion_pinn_demo(n_epochs=50, n_samples=128)

    # 2. Monte Carlo 13-Adic
    print("\n" + "=" * 60)
    print("Monte Carlo 13-Adic Robustness")
    print("=" * 60)

    mc = Adic13MonteCarlo(n_samples=5000, seed=42)
    results = mc.run_simulation()
    print(mc.summary())

    # Plot if available
    if HAS_MATPLOTLIB:
        plot_mc_results(mc, save_path='mc_13adic_results.png')

    # 3. Fibonacci Hidden Explorer
    print("\n")
    explorer = FiboHiddenExplorer(max_n=15)
    print(explorer.summary())

    # Plot if available
    if HAS_MATPLOTLIB:
        plot_fibo_cascade(explorer, save_path='fibo_cascade.png')

    # 4. Generate predictions
    print("\n" + "=" * 60)
    print("Phase 3 Predictions Summary")
    print("=" * 60)

    predictions = [
        f"1. Sterile neutrino mass: ~{explorer.lucas_sequence[7]/N_GEN:.1f} MeV (from L_7/N_gen)",
        f"2. Hidden scalar at: ~18 GeV (gap mode L_6)",
        f"3. 13-adic robustness: {results['robustness_score']:.4f}",
        f"4. Structure preservation: {results['preservation_rate']:.1%}",
        f"5. Deviation < 0.1%: {results['deviation_under_01pct']:.1%} of samples"
    ]

    for p in predictions:
        print(f"  {p}")

    print("\n" + "=" * 70)
    print("Phase 3 Complete - Ready for Phase 4 (Global Simulations)")
    print("=" * 70)


if __name__ == "__main__":
    main()
