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
