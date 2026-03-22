"""
Monte Carlo simulation for GIFT dimensional observables.

Implements stochastic sampling of S7/K7 geometry parameters
to test robustness of κ_T torsion predictions across scale variations.
"""
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional, Callable
from fractions import Fraction
import math
import random

__all__ = [
    'Observable', 'OBSERVABLES', 'ScalePerturbation', 'MCResult',
    'MonteCarloEngine', 'KappaTRobustness',
    'run_quick_mc', 'run_kappa_analysis', 'compare_predictions_to_experiment',
    'planck_string_perturbation',
]

from gift_core.constants import (
    B2, B3, DIM_G2, DIM_K7, DIM_E8, DIM_E8xE8, H_STAR, P2,
    KAPPA_T, SIN2_THETA_W, TAU, Q_KOIDE, DELTA_CP, M_TAU_M_E, M_S_M_D
)
from gift_core.scales import (
    M_PLANCK, M_STRING_DEFAULT, M_STRING_MIN, M_STRING_MAX, M_GUT,
    ScaleHierarchy, S7Parameters
)


# =============================================================================
# OBSERVABLE DEFINITIONS
# =============================================================================

@dataclass
class Observable:
    """A physical observable derived from topological data."""
    name: str
    symbol: str
    nominal_value: float
    formula: str
    compute: Callable[[Dict[str, float]], float]
    experimental: Optional[float] = None
    exp_error: Optional[float] = None


def compute_sin2_theta_w(params: Dict[str, float]) -> float:
    """sin²θ_W = b₂/(b₃ + dim_G₂) with perturbations."""
    b2 = params.get('b2', B2)
    b3 = params.get('b3', B3)
    dim_g2 = params.get('dim_g2', DIM_G2)
    return b2 / (b3 + dim_g2)


def compute_kappa_t(params: Dict[str, float]) -> float:
    """κ_T = 1/(b₃ - dim_G₂ - p₂) with perturbations."""
    b3 = params.get('b3', B3)
    dim_g2 = params.get('dim_g2', DIM_G2)
    p2 = params.get('p2', P2)
    denom = b3 - dim_g2 - p2
    return 1.0 / denom if denom != 0 else float('inf')


def compute_tau(params: Dict[str, float]) -> float:
    """τ = (dim_E₈×E₈ × b₂)/(dim_J₃(O) × H*)."""
    dim_e8xe8 = params.get('dim_e8xe8', DIM_E8xE8)
    b2 = params.get('b2', B2)
    dim_j3o = params.get('dim_j3o', 27)
    h_star = params.get('h_star', H_STAR)
    return (dim_e8xe8 * b2) / (dim_j3o * h_star)


def compute_q_koide(params: Dict[str, float]) -> float:
    """Q_Koide = dim_G₂/b₂."""
    dim_g2 = params.get('dim_g2', DIM_G2)
    b2 = params.get('b2', B2)
    return dim_g2 / b2


def compute_delta_cp(params: Dict[str, float]) -> float:
    """δ_CP = 7 × dim_G₂ + H* (degrees)."""
    dim_g2 = params.get('dim_g2', DIM_G2)
    h_star = params.get('h_star', H_STAR)
    return 7 * dim_g2 + h_star


def compute_m_tau_m_e(params: Dict[str, float]) -> float:
    """m_τ/m_e = 7 + 10×dim_E₈ + 10×H*."""
    dim_e8 = params.get('dim_e8', DIM_E8)
    h_star = params.get('h_star', H_STAR)
    return 7 + 10 * dim_e8 + 10 * h_star


def compute_h_star(params: Dict[str, float]) -> float:
    """H* = b₂ + b₃ + 1."""
    b2 = params.get('b2', B2)
    b3 = params.get('b3', B3)
    return b2 + b3 + 1


# Standard observables
OBSERVABLES = [
    Observable(
        name="Weinberg angle",
        symbol="sin²θ_W",
        nominal_value=float(SIN2_THETA_W),
        formula="b₂/(b₃ + dim_G₂)",
        compute=compute_sin2_theta_w,
        experimental=0.23122,
        exp_error=0.00003
    ),
    Observable(
        name="Torsion coefficient",
        symbol="κ_T",
        nominal_value=float(KAPPA_T),
        formula="1/(b₃ - dim_G₂ - p₂)",
        compute=compute_kappa_t
    ),
    Observable(
        name="Hierarchy parameter",
        symbol="τ",
        nominal_value=float(TAU),
        formula="(496×21)/(27×99)",
        compute=compute_tau
    ),
    Observable(
        name="Koide parameter",
        symbol="Q_Koide",
        nominal_value=float(Q_KOIDE),
        formula="dim_G₂/b₂",
        compute=compute_q_koide,
        experimental=0.666661,
        exp_error=0.000007
    ),
    Observable(
        name="CP phase",
        symbol="δ_CP",
        nominal_value=float(DELTA_CP),
        formula="7×dim_G₂ + H*",
        compute=compute_delta_cp,
        experimental=197.0,
        exp_error=42.0
    ),
    Observable(
        name="Tau/electron ratio",
        symbol="m_τ/m_e",
        nominal_value=float(M_TAU_M_E),
        formula="7 + 10×248 + 10×99",
        compute=compute_m_tau_m_e,
        experimental=3477.23,
        exp_error=0.24
    ),
    Observable(
        name="Effective DOF",
        symbol="H*",
        nominal_value=float(H_STAR),
        formula="b₂ + b₃ + 1",
        compute=compute_h_star
    ),
]


# =============================================================================
# SCALE PERTURBATION MODELS
# =============================================================================

@dataclass
class ScalePerturbation:
    """
    Model for perturbing physical scales.

    The perturbation models how topological constants might
    receive corrections from scale-dependent physics.
    """
    name: str
    # Relative perturbation to apply
    delta_b2: float = 0.0  # Perturbation to b₂
    delta_b3: float = 0.0  # Perturbation to b₃
    delta_g2: float = 0.0  # Perturbation to dim(G₂)

    def apply(self, base_params: Dict[str, float]) -> Dict[str, float]:
        """Apply perturbations to base parameters."""
        params = base_params.copy()
        params['b2'] = params.get('b2', B2) * (1 + self.delta_b2)
        params['b3'] = params.get('b3', B3) * (1 + self.delta_b3)
        params['dim_g2'] = params.get('dim_g2', DIM_G2) * (1 + self.delta_g2)
        # Recompute derived quantities
        params['h_star'] = params['b2'] + params['b3'] + 1
        params['p2'] = params['dim_g2'] / DIM_K7
        return params


def planck_string_perturbation(m_string: float,
                                m_planck: float = M_PLANCK) -> ScalePerturbation:
    """
    Compute perturbation from string/Planck scale ratio.

    Higher string scale -> smaller perturbations (closer to Planck).
    Lower string scale -> larger perturbations (more stringy).
    """
    ratio = m_string / m_planck  # 0 < ratio < 1

    # Log ratio controls perturbation magnitude
    log_ratio = math.log10(ratio)  # Negative for M_s < M_P

    # String corrections scale as (M_s/M_P)^2
    correction = ratio ** 2

    # Perturbations are O(M_s²/M_P²)
    return ScalePerturbation(
        name=f"M_s/M_P = {ratio:.2e}",
        delta_b2=correction * 0.01,  # 1% correction at M_s = M_P
        delta_b3=correction * 0.02,  # b₃ more sensitive
        delta_g2=correction * 0.005  # G₂ most robust
    )


# =============================================================================
# MONTE CARLO ENGINE
# =============================================================================

@dataclass
class MCResult:
    """Result of Monte Carlo sampling for one observable."""
    observable: Observable
    samples: List[float] = field(default_factory=list)
    n_samples: int = 0

    @property
    def mean(self) -> float:
        return sum(self.samples) / len(self.samples) if self.samples else 0

    @property
    def std(self) -> float:
        if len(self.samples) < 2:
            return 0
        mean = self.mean
        variance = sum((x - mean) ** 2 for x in self.samples) / (len(self.samples) - 1)
        return math.sqrt(variance)

    @property
    def min_val(self) -> float:
        return min(self.samples) if self.samples else 0

    @property
    def max_val(self) -> float:
        return max(self.samples) if self.samples else 0

    def percentile(self, p: float) -> float:
        """Compute p-th percentile (0-100)."""
        if not self.samples:
            return 0
        sorted_samples = sorted(self.samples)
        idx = int(len(sorted_samples) * p / 100)
        return sorted_samples[min(idx, len(sorted_samples) - 1)]

    @property
    def robustness(self) -> float:
        """
        Robustness = 1 - (std / |mean|).
        1.0 = perfectly robust, 0.0 = highly variable.
        """
        if self.mean == 0:
            return 0
        return max(0, 1 - self.std / abs(self.mean))


@dataclass
class MonteCarloEngine:
    """
    Monte Carlo engine for S7 dimensional observables.

    Samples scale variations between Planck and string scales
    to test robustness of topological predictions.
    """
    n_samples: int = 10000
    seed: Optional[int] = None
    m_string_range: Tuple[float, float] = (M_STRING_MIN, M_STRING_MAX)
    observables: List[Observable] = field(default_factory=lambda: OBSERVABLES.copy())

    def __post_init__(self):
        self.results: Dict[str, MCResult] = {}

    def sample_string_scale(self) -> float:
        """Sample string scale uniformly in log space."""
        log_min = math.log10(self.m_string_range[0])
        log_max = math.log10(self.m_string_range[1])
        log_m = random.uniform(log_min, log_max)
        return 10 ** log_m

    def run(self, verbose: bool = False) -> Dict[str, MCResult]:
        """
        Run Monte Carlo simulation.

        For each sample:
        1. Draw random string scale M_s
        2. Compute perturbation from M_s/M_P ratio
        3. Apply perturbation to topological parameters
        4. Compute all observables
        """
        # Set seed at run time for reproducibility
        if self.seed is not None:
            random.seed(self.seed)

        # Initialize results
        for obs in self.observables:
            self.results[obs.symbol] = MCResult(observable=obs, n_samples=self.n_samples)

        # Base parameters (unperturbed)
        base_params = {
            'b2': float(B2),
            'b3': float(B3),
            'dim_g2': float(DIM_G2),
            'dim_e8': float(DIM_E8),
            'dim_e8xe8': float(DIM_E8xE8),
            'dim_j3o': 27.0,
            'dim_k7': float(DIM_K7),
            'h_star': float(H_STAR),
            'p2': float(P2),
        }

        # Monte Carlo loop
        for i in range(self.n_samples):
            # Sample string scale
            m_s = self.sample_string_scale()

            # Compute perturbation
            pert = planck_string_perturbation(m_s)

            # Apply to get perturbed parameters
            params = pert.apply(base_params)

            # Compute each observable
            for obs in self.observables:
                value = obs.compute(params)
                self.results[obs.symbol].samples.append(value)

            if verbose and (i + 1) % 1000 == 0:
                print(f"  Completed {i + 1}/{self.n_samples} samples")

        return self.results

    def summary(self) -> str:
        """Generate summary report."""
        lines = [
            "Monte Carlo Simulation Results",
            "=" * 80,
            f"Samples: {self.n_samples}",
            f"String scale range: [{self.m_string_range[0]:.2e}, {self.m_string_range[1]:.2e}] GeV",
            "",
            f"{'Observable':<20} {'Nominal':<12} {'MC Mean':<12} {'MC Std':<10} {'Robust':<8}",
            "-" * 80,
        ]

        for symbol, result in self.results.items():
            obs = result.observable
            lines.append(
                f"{obs.symbol:<20} {obs.nominal_value:<12.6f} "
                f"{result.mean:<12.6f} {result.std:<10.6f} {result.robustness:>6.1%}"
            )

        lines.append("=" * 80)
        return "\n".join(lines)


# =============================================================================
# κ_T ROBUSTNESS ANALYSIS
# =============================================================================

@dataclass
class KappaTRobustness:
    """
    Specialized analysis for torsion coefficient κ_T robustness.

    Tests how κ_T = 1/61 responds to:
    1. Scale variations (Planck vs string)
    2. Perturbations to b₃, dim(G₂), p₂
    3. Compactification geometry changes
    """
    n_samples: int = 10000
    seed: Optional[int] = 42

    def __post_init__(self):
        random.seed(self.seed)
        self.results: Dict[str, List[float]] = {
            'kappa_t': [],
            'm_string': [],
            'b3_eff': [],
            'g2_eff': [],
        }

    def run_scale_scan(self, n_points: int = 100) -> Dict[str, List[float]]:
        """
        Scan κ_T vs string scale.

        Returns dict with M_s values and corresponding κ_T.
        """
        m_s_values = []
        kappa_values = []

        for i in range(n_points):
            # Log-spaced scan from M_STRING_MIN to M_PLANCK
            frac = i / (n_points - 1)
            log_m = math.log10(M_STRING_MIN) + frac * (
                math.log10(M_PLANCK) - math.log10(M_STRING_MIN)
            )
            m_s = 10 ** log_m

            # Compute perturbation
            pert = planck_string_perturbation(m_s)
            params = pert.apply({'b3': B3, 'dim_g2': DIM_G2, 'p2': P2})

            # Compute κ_T
            kappa = compute_kappa_t(params)

            m_s_values.append(m_s)
            kappa_values.append(kappa)

        return {'m_string': m_s_values, 'kappa_t': kappa_values}

    def run_monte_carlo(self) -> None:
        """
        Full Monte Carlo for κ_T with random scale sampling.
        """
        for _ in range(self.n_samples):
            # Random string scale (log-uniform)
            log_m = random.uniform(
                math.log10(M_STRING_MIN),
                math.log10(M_PLANCK)
            )
            m_s = 10 ** log_m

            # Perturbation
            pert = planck_string_perturbation(m_s)
            params = pert.apply({
                'b3': float(B3),
                'dim_g2': float(DIM_G2),
                'p2': float(P2)
            })

            # Record
            self.results['m_string'].append(m_s)
            self.results['kappa_t'].append(compute_kappa_t(params))
            self.results['b3_eff'].append(params['b3'])
            self.results['g2_eff'].append(params['dim_g2'])

    def summary(self) -> str:
        """Generate κ_T robustness summary."""
        kappa = self.results['kappa_t']
        if not kappa:
            return "No results (run simulation first)"

        mean_k = sum(kappa) / len(kappa)
        std_k = math.sqrt(sum((x - mean_k) ** 2 for x in kappa) / (len(kappa) - 1))
        nominal = float(KAPPA_T)

        lines = [
            "κ_T Robustness Analysis",
            "=" * 60,
            f"Samples: {len(kappa)}",
            f"Nominal κ_T: {nominal:.6f} (1/61)",
            "",
            f"MC Mean:     {mean_k:.6f}",
            f"MC Std:      {std_k:.6f}",
            f"MC Min:      {min(kappa):.6f}",
            f"MC Max:      {max(kappa):.6f}",
            "",
            f"Deviation from nominal: {abs(mean_k - nominal) / nominal * 100:.2f}%",
            f"Robustness score: {max(0, 1 - std_k / abs(mean_k)) * 100:.1f}%",
            "=" * 60,
        ]
        return "\n".join(lines)


# =============================================================================
# CONVENIENCE FUNCTIONS
# =============================================================================

def run_quick_mc(n_samples: int = 1000, seed: int = 42) -> MonteCarloEngine:
    """Run a quick Monte Carlo simulation."""
    engine = MonteCarloEngine(n_samples=n_samples, seed=seed)
    engine.run()
    return engine


def run_kappa_analysis(n_samples: int = 10000, seed: int = 42) -> KappaTRobustness:
    """Run κ_T robustness analysis."""
    analysis = KappaTRobustness(n_samples=n_samples, seed=seed)
    analysis.run_monte_carlo()
    return analysis


def compare_predictions_to_experiment() -> str:
    """Compare all GIFT predictions to experimental values."""
    lines = [
        "GIFT Predictions vs Experiment (PDG 2024 / NuFIT 5.3)",
        "=" * 80,
        f"{'Observable':<20} {'GIFT':<12} {'Exp':<12} {'Exp σ':<10} {'Pull (σ)'}",
        "-" * 80,
    ]

    for obs in OBSERVABLES:
        if obs.experimental is not None:
            pull = (obs.nominal_value - obs.experimental) / obs.exp_error
            status = "✓" if abs(pull) < 3 else "✗"
            lines.append(
                f"{obs.symbol:<20} {obs.nominal_value:<12.6f} "
                f"{obs.experimental:<12.6f} {obs.exp_error:<10.6f} {pull:>+6.2f} {status}"
            )

    lines.append("=" * 80)
    return "\n".join(lines)


if __name__ == "__main__":
    print("Running GIFT Monte Carlo simulation...\n")

    # Quick MC
    engine = run_quick_mc(n_samples=5000)
    print(engine.summary())
    print()

    # κ_T analysis
    kappa = run_kappa_analysis(n_samples=5000)
    print(kappa.summary())
    print()

    # Comparison
    print(compare_predictions_to_experiment())
