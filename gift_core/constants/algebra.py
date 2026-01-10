"""
Exceptional Lie Algebra Constants.

E8, G2, F4, E6, E7 dimensions, ranks, and Weyl group properties.
All values proven in Lean 4 (GIFT.Algebra, GIFT.Foundations.RootSystems).
"""

# =============================================================================
# E8 EXCEPTIONAL LIE ALGEBRA
# =============================================================================

DIM_E8 = 248          # dim(E8) = 240 roots + 8 rank
RANK_E8 = 8           # Cartan subalgebra dimension
DIM_E8xE8 = 496       # dim(E8 x E8) heterotic

# Weyl group W(E8)
WEYL_FACTOR = 5       # From |W(E8)| = 2^14 * 3^5 * 5^2 * 7
WEYL_SQ = 25          # Weyl^2 (pentagonal structure)
WEYL_E8_ORDER = 696729600  # |W(E8)| = 2^14 * 3^5 * 5^2 * 7

# =============================================================================
# G2 EXCEPTIONAL HOLONOMY
# =============================================================================

DIM_G2 = 14           # dim(G2) = 12 roots + 2 rank
RANK_G2 = 2           # Cartan subalgebra dimension
DIM_K7 = 7            # Real dimension of K7 manifold (G2 holonomy)

# =============================================================================
# OTHER EXCEPTIONAL LIE ALGEBRAS
# =============================================================================

DIM_F4 = 52           # dim(F4)
DIM_E6 = 78           # dim(E6) = 6 * 13
DIM_E7 = 133          # dim(E7) = 7 * 19
DIM_FUND_E7 = 56      # Fundamental representation of E7

# =============================================================================
# JORDAN ALGEBRA
# =============================================================================

DIM_J3O = 27          # dim(J3(O)) - Exceptional Jordan algebra
DIM_J3O_TRACELESS = 26  # Traceless part

# =============================================================================
# STANDARD MODEL GAUGE GROUPS
# =============================================================================

DIM_SU3 = 8           # SU(3) color
DIM_SU2 = 3           # SU(2) weak isospin
DIM_U1 = 1            # U(1) hypercharge
DIM_SM_GAUGE = 12     # Total = 8 + 3 + 1

# =============================================================================
# EXCEPTIONAL CHAIN: E_n = n * prime(g(n))
# =============================================================================

PRIME_6 = 13          # 6th prime (for E6)
PRIME_8 = 19          # 8th prime (for E7)
PRIME_11 = 31         # 11th prime (for E8)

# Verification: E6 = 6*13, E7 = 7*19, E8 = 8*31
E6_CHAIN = 6 * PRIME_6   # = 78
E7_CHAIN = 7 * PRIME_8   # = 133
E8_CHAIN = 8 * PRIME_11  # = 248

# Gaps in exceptional chain
E7_E6_GAP = DIM_E7 - DIM_E6  # = 55 = 5 * 11 = Weyl * D_bulk
E8_E7_GAP = DIM_E8 - DIM_E7  # = 115

# F4 -> E6 -> E7 -> E8 chain
EXCEPTIONAL_CHAIN = DIM_E8 - DIM_F4 - DIM_J3O  # = 169 = 13^2

# Jordan traceless connection
JORDAN_TRACELESS = DIM_E6 - DIM_F4  # = 26 = dim(J3O) - 1
DELTA_PENTA = DIM_F4 - DIM_J3O      # = 25 = Weyl^2

# =============================================================================
# V3.3 ADDITIONS: E-SERIES FORMULA FOR JORDAN ALGEBRA
# =============================================================================

# E-series derivation of dim(J3(O)):
#   dim(J3(O)) = (dim(E8) - dim(E6) - dim(SU3)) / 6
#              = (248 - 78 - 8) / 6 = 162 / 6 = 27
# This shows dim(J3(O)) EMERGES from the E-series chain
E_SERIES_DIFF = DIM_E8 - DIM_E6 - DIM_SU3  # = 162
J3O_FROM_E_SERIES = E_SERIES_DIFF // 6      # = 27

# Verification: J3O derived from E-series matches definition
assert J3O_FROM_E_SERIES == DIM_J3O, "E-series J3O derivation failed"
assert E_SERIES_DIFF % 6 == 0, "E-series divisibility check failed"

# =============================================================================
# V3.3 ADDITIONS: MAGIC NUMBER 42
# =============================================================================

# The "magic number" 42 appears in multiple GIFT contexts:
#   42 = 2 x 3 x 7 = p2 x N_gen x dim(K7)
#   42 = 2 x b2 = 2 x 21
# For a compact oriented 7-manifold, chi = 0 by Poincare duality,
# so 42 is NOT the Euler characteristic but rather a structural constant.
MAGIC_42 = 42
N_GEN = 3  # Number of generations (from K4 matchings)
P2 = 2     # Pontryagin class contribution

# Verification
assert MAGIC_42 == P2 * N_GEN * DIM_K7, "Magic 42 GIFT form failed"
assert MAGIC_42 == 2 * 21, "Magic 42 = 2*b2 check failed"

# =============================================================================
# V3.3 ADDITIONS: EXCEPTIONAL RANKS SUM
# =============================================================================

# Sum of exceptional Lie algebra ranks: 8 + 7 + 6 + 4 + 2 = 27 = dim(J3(O))
RANK_E7 = 7
RANK_E6 = 6
RANK_F4 = 4
EXCEPTIONAL_RANKS_SUM = RANK_E8 + RANK_E7 + RANK_E6 + RANK_F4 + RANK_G2  # = 27

assert EXCEPTIONAL_RANKS_SUM == DIM_J3O, "Exceptional ranks sum check failed"
