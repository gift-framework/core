"""
GIFT Core - Formally verified mathematical constants.

All values are proven in Lean 4 and Coq proof assistants.
Zero domain-specific axioms. Zero sorry/Admitted.

V3.0 adds Joyce's perturbation theorem proving that K7 admits
a torsion-free G2 structure, with verified PINN bounds.

Includes Monte Carlo simulation for testing robustness of
dimensional observables across Planck/string scale variations.
"""

from gift_core.constants import (
    # Fundamental constants
    DIM_E8, RANK_E8, DIM_E8xE8, DIM_G2, RANK_G2, DIM_K7,
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
    # Exceptional groups relations (v1.5.0)
    DIM_F4, DIM_E6, DIM_J3O_TRACELESS, WEYL_E8_ORDER,
    ALPHA_SQ_B_SUM, ALPHA_S_SQUARED, ALPHA_S_SQUARED_NUM, ALPHA_S_SQUARED_DEN,
    DIM_F4_FROM_STRUCTURE_B, DELTA_PENTA, JORDAN_TRACELESS,
    WEYL_E8_FORMULA, EXCEPTIONAL_CHAIN,
    # Base decomposition relations (v1.6.0)
    KAPPA_T_INV_FROM_F4, B2_BASE_DECOMPOSITION,
    B3_INTERMEDIATE, B3_BASE_DECOMPOSITION,
    H_STAR_INTERMEDIATE, H_STAR_BASE_DECOMPOSITION,
    QUOTIENT_SUM, OMEGA_DE_PRODUCT,
    # Extended decomposition relations (v1.5.0)
    TAU_NUM_VALUE, TAU_DEN_VALUE, TAU_NUM_BASE13, to_base_13,
    N_OBSERVABLES, E6_DUAL_OBSERVABLES, H0_TOPOLOGICAL,
    # Mass factorization theorem (v1.6.0)
    PRIME_8, MASS_FACTOR_NGEN, MASS_FACTOR_PRIME, MASS_FACTOR_TORSION,
    MASS_FACTORIZATION, B_18_DENOM, B_18_INDEX,
    # T_61 manifold structure (v1.6.0)
    T61_DIM, W1_DIM, W7_DIM, W14_DIM, W27_DIM, W_SUM,
    T61_RESIDUE, T61_RESIDUE_INTERPRETATION,
    # Triade 9-18-34 structure (v1.6.0)
    IMPEDANCE, DUALITY_GAP_LUCAS, HIDDEN_DIM_FIBO,
    fibonacci, lucas, F_8, F_9, F_12, L_6, L_7,
    FIBO_8_IS_B2, LUCAS_6_IS_GAP,
    # Alpha A/B duality (v1.6.0)
    ALPHA_A_SUM_IS_SM, ALPHA_B_SUM_IS_EXCEPTIONAL, GAP_COLOR_FORMULA,
    # Predictions (v1.6.0)
    STERILE_MASS_LUCAS_NUM, STERILE_MASS_LUCAS_SCALE,
    HIDDEN_SCALAR_MASS_GEV, N_HIDDEN_STATES,
    # Exceptional chain relations (v1.7.0)
    DIM_E7, DIM_FUND_E7, PRIME_6, PRIME_11,
    TAU_NUM_FROM_E8xE8, DIM_E7_FROM_K7_PRIME, DIM_E7_FROM_TOPOLOGY,
    MASS_RATIO_FROM_E7, FUND_E7_FROM_ALGEBRA,
    to_base_7, E6_BASE7, E6_IS_PALINDROME_BASE7,
    DIM_E8_FROM_PRIME, MASS_RATIO_U1_INTERPRETATION,
    B3_BASE7, E6_FROM_B3,
    E6_CHAIN, E7_CHAIN, E8_CHAIN,
    CHAIN_PRIME_INDEX_E6, CHAIN_PRIME_INDEX_E7, CHAIN_PRIME_INDEX_E8,
    E7_E6_GAP, E8_E7_GAP, E7_FUND_J3O_SUM,
    # V2.0 new constants
    HUBBLE_CMB, HUBBLE_LOCAL, HUBBLE_TENSION,
    MONSTER_DIM, MONSTER_FACTOR_47, MONSTER_FACTOR_59, MONSTER_FACTOR_71,
    J_CONSTANT, J_COEFF_1,
    COXETER_E8, ICOSAHEDRON_VERTICES, ICOSAHEDRON_EDGES, ICOSAHEDRON_FACES,
    BINARY_ICOSAHEDRAL_ORDER, E8_KISSING_NUMBER,
    PHI_SQUARED_NUM, PHI_SQUARED_DEN,
    HEEGNER_NUMBERS, T_CMB_mK, AGE_UNIVERSE_UNIT,
)

# V2.0 New modules
from gift_core.sequences import (
    fib, lucas,
    FIBONACCI_GIFT, LUCAS_GIFT,
    fibonacci_index, lucas_index,
    RECURRENCE_CHAIN, verify_fibonacci_recurrence,
    PHI_RATIOS, phi_deviation,
)

from gift_core.primes import (
    TIER1_PRIMES, TIER2_PRIMES, TIER3_PRIMES, TIER4_PRIMES,
    HEEGNER_NUMBERS as HEEGNER_DICT, SPECIAL_PRIMES, GENERATORS,
    prime_expression, prime_generator, is_gift_prime,
    is_heegner, verify_prime_coverage,
)

from gift_core.monster import (
    MONSTER_DIM as MONSTER_DIMENSION,
    MONSTER_FACTORS, MONSTER_FACTOR_EXPRESSIONS,
    verify_monster_factorization, monster_factor_arithmetic_progression,
    J_CONSTANT as J_INVARIANT_CONSTANT, J_CONSTANT_FACTORED, J_COEFF_1 as J_FIRST_COEFF,
    verify_j_constant, verify_moonshine, j_E8_relations,
)

from gift_core.mckay import (
    COXETER_E8 as MCKAY_COXETER, ICOSAHEDRON, BINARY_GROUPS, E8_KISSING_NUMBER as MCKAY_KISSING,
    verify_mckay_coxeter, verify_euler_icosahedron, verify_E8_kissing,
    ICOSAHEDRAL_ANGLE, PENTAGON_ANGLE, PHI_APPROX,
    golden_emergence_chain, PHI_RATIOS as MCKAY_PHI_RATIOS,
    ADE_BINARY_ORDERS,
)

# V3.0: Joyce existence theorem module
from gift_core.analysis import (
    Interval, IntervalBound,
    TORSION_BOUND, JOYCE_THRESHOLD, LIPSCHITZ_BOUND,
    DET_G_BOUND, DET_G_TARGET, CONTRACTION_K,
    JoyceCertificate, verify_pinn_bounds,
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

# V3.1.4: GIFT-Native PINN (requires: pip install torch)
try:
    from gift_core.nn.gift_native_pinn import (
        GIFTNativePINN,
        GIFTNativeLoss,
        GIFTTrainConfig,
        GIFTTrainResult,
        create_gift_native_pinn,
        train_gift_native_pinn,
        extract_fourier_coefficients,
        export_analytical_form,
        phi0_standard,
        FANO_LINES,
    )
    HAS_GIFT_NATIVE_PINN = True
except ImportError:
    GIFTNativePINN = None
    GIFTNativeLoss = None
    GIFTTrainConfig = None
    GIFTTrainResult = None
    create_gift_native_pinn = None
    train_gift_native_pinn = None
    extract_fourier_coefficients = None
    export_analytical_form = None
    phi0_standard = None
    FANO_LINES = None
    HAS_GIFT_NATIVE_PINN = False

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
    'DIM_E8', 'RANK_E8', 'DIM_E8xE8', 'DIM_G2', 'RANK_G2', 'DIM_K7',
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
    # Exceptional groups relations (v1.5.0)
    'DIM_F4', 'DIM_E6', 'DIM_J3O_TRACELESS', 'WEYL_E8_ORDER',
    'ALPHA_SQ_B_SUM', 'ALPHA_S_SQUARED', 'ALPHA_S_SQUARED_NUM', 'ALPHA_S_SQUARED_DEN',
    'DIM_F4_FROM_STRUCTURE_B', 'DELTA_PENTA', 'JORDAN_TRACELESS',
    'WEYL_E8_FORMULA', 'EXCEPTIONAL_CHAIN',
    # Base decomposition relations (v1.6.0)
    'KAPPA_T_INV_FROM_F4', 'B2_BASE_DECOMPOSITION',
    'B3_INTERMEDIATE', 'B3_BASE_DECOMPOSITION',
    'H_STAR_INTERMEDIATE', 'H_STAR_BASE_DECOMPOSITION',
    'QUOTIENT_SUM', 'OMEGA_DE_PRODUCT',
    # Extended decomposition relations (v1.5.0)
    'TAU_NUM_VALUE', 'TAU_DEN_VALUE', 'TAU_NUM_BASE13', 'to_base_13',
    'N_OBSERVABLES', 'E6_DUAL_OBSERVABLES', 'H0_TOPOLOGICAL',
    # Mass factorization theorem (v1.6.0)
    'PRIME_8', 'MASS_FACTOR_NGEN', 'MASS_FACTOR_PRIME', 'MASS_FACTOR_TORSION',
    'MASS_FACTORIZATION', 'B_18_DENOM', 'B_18_INDEX',
    # T_61 manifold structure (v1.6.0)
    'T61_DIM', 'W1_DIM', 'W7_DIM', 'W14_DIM', 'W27_DIM', 'W_SUM',
    'T61_RESIDUE', 'T61_RESIDUE_INTERPRETATION',
    # Triade 9-18-34 structure (v1.6.0)
    'IMPEDANCE', 'DUALITY_GAP_LUCAS', 'HIDDEN_DIM_FIBO',
    'fibonacci', 'lucas', 'F_8', 'F_9', 'F_12', 'L_6', 'L_7',
    'FIBO_8_IS_B2', 'LUCAS_6_IS_GAP',
    # Alpha A/B duality (v1.6.0)
    'ALPHA_A_SUM_IS_SM', 'ALPHA_B_SUM_IS_EXCEPTIONAL', 'GAP_COLOR_FORMULA',
    # Predictions (v1.6.0)
    'STERILE_MASS_LUCAS_NUM', 'STERILE_MASS_LUCAS_SCALE',
    'HIDDEN_SCALAR_MASS_GEV', 'N_HIDDEN_STATES',
    # Exceptional chain relations (v1.7.0)
    'DIM_E7', 'DIM_FUND_E7', 'PRIME_6', 'PRIME_11',
    'TAU_NUM_FROM_E8xE8', 'DIM_E7_FROM_K7_PRIME', 'DIM_E7_FROM_TOPOLOGY',
    'MASS_RATIO_FROM_E7', 'FUND_E7_FROM_ALGEBRA',
    'to_base_7', 'E6_BASE7', 'E6_IS_PALINDROME_BASE7',
    'DIM_E8_FROM_PRIME', 'MASS_RATIO_U1_INTERPRETATION',
    'B3_BASE7', 'E6_FROM_B3',
    'E6_CHAIN', 'E7_CHAIN', 'E8_CHAIN',
    'CHAIN_PRIME_INDEX_E6', 'CHAIN_PRIME_INDEX_E7', 'CHAIN_PRIME_INDEX_E8',
    'E7_E6_GAP', 'E8_E7_GAP', 'E7_FUND_J3O_SUM',
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
    # V3.0: Analysis module (Joyce existence)
    'Interval', 'IntervalBound',
    'TORSION_BOUND', 'JOYCE_THRESHOLD', 'LIPSCHITZ_BOUND',
    'DET_G_BOUND', 'DET_G_TARGET', 'CONTRACTION_K',
    'JoyceCertificate', 'verify_pinn_bounds',
    # V3.1.4: GIFT-Native PINN
    'GIFTNativePINN', 'GIFTNativeLoss',
    'GIFTTrainConfig', 'GIFTTrainResult',
    'create_gift_native_pinn', 'train_gift_native_pinn',
    'extract_fourier_coefficients', 'export_analytical_form',
    'phi0_standard', 'FANO_LINES',
    # Version
    '__version__',
]
