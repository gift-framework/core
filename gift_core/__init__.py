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
    # Version
    '__version__',
]
