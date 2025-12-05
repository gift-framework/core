"""
GIFT Core - Formally verified mathematical constants.

All values are proven in Lean 4 and Coq proof assistants.
Zero domain-specific axioms. Zero sorry/Admitted.

Includes Monte Carlo simulation for testing robustness of
dimensional observables across Planck/string scale variations.
"""

from gift_core.constants import (
    # Fundamental constants
    DIM_E8, RANK_E8, DIM_E8xE8, DIM_G2, DIM_K7,
    B2, B3, WEYL_FACTOR, WEYL_SQ, DIM_J3O,
    D_BULK, DIM_SU3, DIM_SU2, DIM_U1, DIM_SM_GAUGE,
    # Original 13 proven relations
    SIN2_THETA_W, TAU, DET_G, KAPPA_T, DELTA_CP,
    M_TAU_M_E, M_S_M_D, Q_KOIDE, LAMBDA_H_NUM,
    H_STAR, P2, N_GEN,
    # Extension: 12 topological relations (v1.1.0)
    ALPHA_S_DENOM, ALPHA_S_SQ_NUM, ALPHA_S_SQ_DENOM,
    ALPHA_INV_ALGEBRAIC, ALPHA_INV_BULK, ALPHA_INV_BASE,
    GAMMA_GIFT_NUM, GAMMA_GIFT_DEN, GAMMA_GIFT,
    DELTA_PENTAGONAL_DENOM,
    THETA_23_NUM, THETA_23_DEN, THETA_23,
    THETA_13_DENOM, THETA_12_RATIO_FACTOR,
    M_MU_M_E_BASE,
    LAMBDA_H_SQ_NUM, LAMBDA_H_SQ_DEN, LAMBDA_H_SQ,
    N_S_ZETA_BULK, N_S_ZETA_WEYL,
    OMEGA_DE_NUM, OMEGA_DE_DEN, OMEGA_DE_FRACTION,
    # Yukawa duality relations (v1.3.0)
    VISIBLE_DIM, HIDDEN_DIM,
    ALPHA_SQ_LEPTON_A, ALPHA_SQ_UP_A, ALPHA_SQ_DOWN_A,
    ALPHA_SUM_A, ALPHA_PROD_A,
    ALPHA_SQ_LEPTON_B, ALPHA_SQ_UP_B, ALPHA_SQ_DOWN_B,
    ALPHA_SUM_B, ALPHA_PROD_B,
    DUALITY_GAP, DUALITY_GAP_FROM_COLOR, KAPPA_T_INV,
    # Irrational sector relations (v1.4.0)
    THETA_13_DIVISOR, THETA_13_DEGREES_NUM, THETA_13_DEGREES_DEN,
    THETA_13_DEGREES_SIMPLIFIED,
    ALPHA_INV_TORSION_NUM, ALPHA_INV_TORSION_DEN,
    ALPHA_INV_COMPLETE_NUM, ALPHA_INV_COMPLETE_DEN, ALPHA_INV_COMPLETE,
    PHI_LOWER_BOUND, PHI_UPPER_BOUND,
    SQRT5_LOWER_BOUND, SQRT5_UPPER_BOUND,
    M_MU_M_E_LOWER, M_MU_M_E_UPPER, M_MU_M_E_BASE_CUBE,
)
from gift_core.relations import PROVEN_RELATIONS, get_relation
from gift_core.topology import K7, G2, E8
from gift_core.scales import (
    M_PLANCK, M_STRING_DEFAULT, M_GUT, M_EW,
    ScaleHierarchy, S7Parameters,
)
from gift_core.experimental import (
    Measurement, Comparison, GIFT_COMPARISONS,
    SIN2_THETA_W_EXP, DELTA_CP_EXP, M_TAU_M_E_EXP, Q_KOIDE_EXP,
)
from gift_core.monte_carlo import (
    Observable, OBSERVABLES,
    MonteCarloEngine, KappaTRobustness,
    run_quick_mc, run_kappa_analysis, compare_predictions_to_experiment,
)
from gift_core._version import __version__

# Optional torch integration (requires: pip install torch)
try:
    from gift_core.torch_optim import (
        TORCH_AVAILABLE,
        DifferentiableObservables,
        K7MetricOptimizer,
        OptimizationResult,
        optimize_k7_metric,
        multi_start_optimization,
        scan_parameter_space,
    )
except ImportError:
    TORCH_AVAILABLE = False
    DifferentiableObservables = None
    K7MetricOptimizer = None
    OptimizationResult = None
    optimize_k7_metric = None
    multi_start_optimization = None
    scan_parameter_space = None

# =============================================================================
# K7 METRIC MODULES (v1.2.0) - Requires numpy
# =============================================================================
# These modules provide numerical computation of G2 metrics on K7
# pip install numpy scipy torch (optional)

NUMPY_AVAILABLE = False

try:
    import numpy as np
    NUMPY_AVAILABLE = True

    # Geometry: TCS construction and K7 metric
    from gift_core.geometry import (
        KummerK3,
        ACylCY3,
        TCSManifold,
        K7Metric,
    )

    # G2 structure: 3-form, holonomy, torsion, constraints
    from gift_core.g2 import (
        G2Form,
        G2Form4,
        standard_g2_form,
        G2Holonomy,
        compute_holonomy,
        G2Torsion,
        torsion_classes,
        G2Constraints,
        GIFT_CONSTRAINTS,
    )

    # Harmonic forms: Hodge Laplacian, Betti numbers
    from gift_core.harmonic import (
        HodgeLaplacian,
        laplacian_eigenvalues,
        HarmonicExtractor,
        HarmonicBasis,
        validate_betti,
        BettiValidator,
    )

    # Physics: Yukawa couplings, mass spectrum
    from gift_core.physics import (
        YukawaTensor,
        compute_yukawa,
        MassSpectrum,
        compute_masses,
        GaugeCouplings,
        GIFT_COUPLINGS,
    )

    # Verification: certificates, Lean/Coq export
    from gift_core.verification import (
        IntervalArithmetic,
        certified_interval,
        G2Certificate,
        generate_certificate,
        LeanExporter,
        export_to_lean,
    )

    # Pipeline: end-to-end computation
    from gift_core.pipeline import (
        PipelineConfig,
        default_config,
        GIFTPipeline,
        PipelineResult,
        run_pipeline,
    )

except ImportError:
    # numpy not available - K7 metric modules disabled
    KummerK3 = None
    ACylCY3 = None
    TCSManifold = None
    K7Metric = None
    G2Form = None
    G2Form4 = None
    standard_g2_form = None
    G2Holonomy = None
    compute_holonomy = None
    G2Torsion = None
    torsion_classes = None
    G2Constraints = None
    GIFT_CONSTRAINTS = None
    HodgeLaplacian = None
    laplacian_eigenvalues = None
    HarmonicExtractor = None
    HarmonicBasis = None
    validate_betti = None
    BettiValidator = None
    YukawaTensor = None
    compute_yukawa = None
    MassSpectrum = None
    compute_masses = None
    GaugeCouplings = None
    GIFT_COUPLINGS = None
    IntervalArithmetic = None
    certified_interval = None
    G2Certificate = None
    generate_certificate = None
    LeanExporter = None
    export_to_lean = None
    PipelineConfig = None
    default_config = None
    GIFTPipeline = None
    PipelineResult = None
    run_pipeline = None

__all__ = [
    # Fundamental topological constants
    'DIM_E8', 'RANK_E8', 'DIM_E8xE8', 'DIM_G2', 'DIM_K7',
    'B2', 'B3', 'WEYL_FACTOR', 'WEYL_SQ', 'DIM_J3O',
    'D_BULK', 'DIM_SU3', 'DIM_SU2', 'DIM_U1', 'DIM_SM_GAUGE',
    # Original 13 proven relations
    'SIN2_THETA_W', 'TAU', 'DET_G', 'KAPPA_T', 'DELTA_CP',
    'M_TAU_M_E', 'M_S_M_D', 'Q_KOIDE', 'LAMBDA_H_NUM',
    'H_STAR', 'P2', 'N_GEN',
    # Extension: 12 topological relations (v1.1.0)
    'ALPHA_S_DENOM', 'ALPHA_S_SQ_NUM', 'ALPHA_S_SQ_DENOM',
    'ALPHA_INV_ALGEBRAIC', 'ALPHA_INV_BULK', 'ALPHA_INV_BASE',
    'GAMMA_GIFT_NUM', 'GAMMA_GIFT_DEN', 'GAMMA_GIFT',
    'DELTA_PENTAGONAL_DENOM',
    'THETA_23_NUM', 'THETA_23_DEN', 'THETA_23',
    'THETA_13_DENOM', 'THETA_12_RATIO_FACTOR',
    'M_MU_M_E_BASE',
    'LAMBDA_H_SQ_NUM', 'LAMBDA_H_SQ_DEN', 'LAMBDA_H_SQ',
    'N_S_ZETA_BULK', 'N_S_ZETA_WEYL',
    'OMEGA_DE_NUM', 'OMEGA_DE_DEN', 'OMEGA_DE_FRACTION',
    # Yukawa duality relations (v1.3.0)
    'VISIBLE_DIM', 'HIDDEN_DIM',
    'ALPHA_SQ_LEPTON_A', 'ALPHA_SQ_UP_A', 'ALPHA_SQ_DOWN_A',
    'ALPHA_SUM_A', 'ALPHA_PROD_A',
    'ALPHA_SQ_LEPTON_B', 'ALPHA_SQ_UP_B', 'ALPHA_SQ_DOWN_B',
    'ALPHA_SUM_B', 'ALPHA_PROD_B',
    'DUALITY_GAP', 'DUALITY_GAP_FROM_COLOR', 'KAPPA_T_INV',
    # Irrational sector relations (v1.4.0)
    'THETA_13_DIVISOR', 'THETA_13_DEGREES_NUM', 'THETA_13_DEGREES_DEN',
    'THETA_13_DEGREES_SIMPLIFIED',
    'ALPHA_INV_TORSION_NUM', 'ALPHA_INV_TORSION_DEN',
    'ALPHA_INV_COMPLETE_NUM', 'ALPHA_INV_COMPLETE_DEN', 'ALPHA_INV_COMPLETE',
    'PHI_LOWER_BOUND', 'PHI_UPPER_BOUND',
    'SQRT5_LOWER_BOUND', 'SQRT5_UPPER_BOUND',
    'M_MU_M_E_LOWER', 'M_MU_M_E_UPPER', 'M_MU_M_E_BASE_CUBE',
    # Structures
    'K7', 'G2', 'E8', 'PROVEN_RELATIONS', 'get_relation',
    # Scales
    'M_PLANCK', 'M_STRING_DEFAULT', 'M_GUT', 'M_EW',
    'ScaleHierarchy', 'S7Parameters',
    # Experimental data
    'Measurement', 'Comparison', 'GIFT_COMPARISONS',
    'SIN2_THETA_W_EXP', 'DELTA_CP_EXP', 'M_TAU_M_E_EXP', 'Q_KOIDE_EXP',
    # Monte Carlo
    'Observable', 'OBSERVABLES',
    'MonteCarloEngine', 'KappaTRobustness',
    'run_quick_mc', 'run_kappa_analysis', 'compare_predictions_to_experiment',
    # Torch optimization (optional)
    'TORCH_AVAILABLE',
    'DifferentiableObservables', 'K7MetricOptimizer', 'OptimizationResult',
    'optimize_k7_metric', 'multi_start_optimization', 'scan_parameter_space',
    # K7 Metric modules (v1.2.0, requires numpy)
    'NUMPY_AVAILABLE',
    # Geometry
    'KummerK3', 'ACylCY3', 'TCSManifold', 'K7Metric',
    # G2 structure
    'G2Form', 'G2Form4', 'standard_g2_form',
    'G2Holonomy', 'compute_holonomy',
    'G2Torsion', 'torsion_classes',
    'G2Constraints', 'GIFT_CONSTRAINTS',
    # Harmonic forms
    'HodgeLaplacian', 'laplacian_eigenvalues',
    'HarmonicExtractor', 'HarmonicBasis',
    'validate_betti', 'BettiValidator',
    # Physics
    'YukawaTensor', 'compute_yukawa',
    'MassSpectrum', 'compute_masses',
    'GaugeCouplings', 'GIFT_COUPLINGS',
    # Verification
    'IntervalArithmetic', 'certified_interval',
    'G2Certificate', 'generate_certificate',
    'LeanExporter', 'export_to_lean',
    # Pipeline
    'PipelineConfig', 'default_config',
    'GIFTPipeline', 'PipelineResult', 'run_pipeline',
    # Version
    '__version__',
]
