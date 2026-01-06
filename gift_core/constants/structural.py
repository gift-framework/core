"""
Structural Identities (v3.2).

Weyl Triple Identity, PSL(2,7) relations, and deep structural connections.
All values proven in Lean 4 (GIFT.Relations.Structural).
"""
from .algebra import DIM_G2, RANK_E8, WEYL_FACTOR, DIM_K7
from .topology import B2, B3, P2

# =============================================================================
# NUMBER OF GENERATIONS
# =============================================================================

N_GEN = 3             # Fermion generations (from K4 matchings, index theory)

# =============================================================================
# WEYL TRIPLE IDENTITY (v3.2)
# Three independent derivations of Weyl = 5
# =============================================================================

# Path 1: (dim_G2 + 1) / N_gen = 15 / 3 = 5
WEYL_PATH_1 = (DIM_G2 + 1) // N_GEN  # = 5

# Path 2: b2 / N_gen - p2 = 21 / 3 - 2 = 5
WEYL_PATH_2 = B2 // N_GEN - P2       # = 5

# Path 3: dim_G2 - rank_E8 - 1 = 14 - 8 - 1 = 5
WEYL_PATH_3 = DIM_G2 - RANK_E8 - 1   # = 5

# Verification
assert WEYL_PATH_1 == WEYL_PATH_2 == WEYL_PATH_3 == WEYL_FACTOR

# =============================================================================
# PSL(2,7) = 168 (v3.2)
# Automorphism group of the Fano plane
# =============================================================================

PSL27_ORDER = 168     # |PSL(2,7)| = 168

# Three derivations:
# Path 1: (b3 + dim_G2) + b3 = 91 + 77 = 168
PSL27_PATH_1 = (B3 + DIM_G2) + B3    # = 168

# Path 2: rank_E8 * b2 = 8 * 21 = 168
PSL27_PATH_2 = RANK_E8 * B2          # = 168

# Path 3: N_gen * (b3 - b2) = 3 * 56 = 168
PSL27_PATH_3 = N_GEN * (B3 - B2)     # = 168

# Verification
assert PSL27_PATH_1 == PSL27_PATH_2 == PSL27_PATH_3 == PSL27_ORDER

# =============================================================================
# FUND(E7) = 56 CONNECTION
# =============================================================================

FUND_E7 = B3 - B2     # = 56 = fundamental representation of E7
                      # Also: rank_E8 * dim_K7 = 8 * 7 = 56

# =============================================================================
# DUALITY GAP
# =============================================================================

DUALITY_GAP = 18      # = 61 - 43 = p2 * N_gen^2 (colored sector correction)

# =============================================================================
# EXTENDED DECOMPOSITION RELATIONS
# =============================================================================

# Structure B sum
ALPHA_SUM_B = 2 + 5 + 6   # = 13 (lepton + up + down from Structure B)
ALPHA_SQ_B_SUM = 13       # = ALPHA_SUM_B

# Weyl group of E8 formula
WEYL_E8_FORMULA = (P2 ** DIM_G2) * (N_GEN ** WEYL_FACTOR) * (WEYL_FACTOR ** P2) * DIM_K7

# F4 from Structure B
DIM_F4_FROM_STRUCTURE_B = P2 ** 2 * ALPHA_SQ_B_SUM  # = 4 * 13 = 52

# Kappa_T inverse from F4
KAPPA_T_INV_FROM_F4 = 52 + N_GEN ** 2  # = 61

# B2 decomposition
B2_BASE_DECOMPOSITION = ALPHA_SQ_B_SUM + RANK_E8  # = 13 + 8 = 21

# B3 decomposition
B3_INTERMEDIATE = ALPHA_SQ_B_SUM * WEYL_FACTOR  # = 13 * 5 = 65
B3_BASE_DECOMPOSITION = B3_INTERMEDIATE + 12    # = 65 + 12 = 77

# H* decomposition
H_STAR_INTERMEDIATE = ALPHA_SQ_B_SUM * DIM_K7   # = 13 * 7 = 91
H_STAR_BASE_DECOMPOSITION = H_STAR_INTERMEDIATE + RANK_E8  # = 91 + 8 = 99

# Quotient sum: U1 + Weyl + K7
from .algebra import DIM_U1
QUOTIENT_SUM = DIM_U1 + WEYL_FACTOR + DIM_K7    # = 1 + 5 + 7 = 13

# Number of observables
N_OBSERVABLES = N_GEN * ALPHA_SQ_B_SUM          # = 3 * 13 = 39

# E6 dual observables
E6_DUAL_OBSERVABLES = 2 * N_OBSERVABLES         # = 2 * 39 = 78
