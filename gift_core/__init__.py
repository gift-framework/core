"""
GIFT Core - Formally verified mathematical constants.

All values are proven in Lean 4 and Coq proof assistants.
Zero domain-specific axioms. Zero sorry/Admitted.

Includes Monte Carlo simulation for testing robustness of
dimensional observables across Planck/string scale variations.
"""

from gift_core.constants import (
    DIM_E8, RANK_E8, DIM_E8xE8, DIM_G2, DIM_K7,
    B2, B3, WEYL_FACTOR, DIM_J3O,
    SIN2_THETA_W, TAU, DET_G, KAPPA_T, DELTA_CP,
    M_TAU_M_E, M_S_M_D, Q_KOIDE, LAMBDA_H_NUM,
    H_STAR, P2, N_GEN,
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

__all__ = [
    # Topological constants
    'DIM_E8', 'RANK_E8', 'DIM_E8xE8', 'DIM_G2', 'DIM_K7',
    'B2', 'B3', 'WEYL_FACTOR', 'DIM_J3O',
    # Physical relations
    'SIN2_THETA_W', 'TAU', 'DET_G', 'KAPPA_T', 'DELTA_CP',
    'M_TAU_M_E', 'M_S_M_D', 'Q_KOIDE', 'LAMBDA_H_NUM',
    'H_STAR', 'P2', 'N_GEN',
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
    # Version
    '__version__',
]
