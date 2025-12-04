-- GIFT Algebra module
-- E8, G2 Lie algebra formalizations

namespace GIFT.Algebra

/-- Dimension of the exceptional Lie algebra E8 -/
def dim_E8 : Nat := 248

/-- Rank of E8 -/
def rank_E8 : Nat := 8

/-- Dimension of E8 x E8 -/
def dim_E8xE8 : Nat := 2 * dim_E8

theorem E8xE8_dim_certified : dim_E8xE8 = 496 := rfl

/-- Dimension of the exceptional Lie group G2 -/
def dim_G2 : Nat := 14

/-- Rank of G2 -/
def rank_G2 : Nat := 2

-- =============================================================================
-- ADDITIONAL CONSTANTS FOR TOPOLOGICAL EXTENSION
-- =============================================================================

/-- Weyl factor from |W(E8)| = 2^14 × 3^5 × 5^2 × 7 -/
def Weyl_factor : Nat := 5

/-- Weyl squared (pentagonal structure) -/
def Weyl_sq : Nat := Weyl_factor * Weyl_factor

theorem Weyl_sq_certified : Weyl_sq = 25 := rfl

/-- Bulk dimension D = 11 (M-theory) -/
def D_bulk : Nat := 11

/-- Standard Model gauge group dimensions -/
def dim_SU3 : Nat := 8   -- SU(3) color
def dim_SU2 : Nat := 3   -- SU(2) weak isospin
def dim_U1 : Nat := 1    -- U(1) hypercharge

/-- Total SM gauge dimension -/
def dim_SM_gauge : Nat := dim_SU3 + dim_SU2 + dim_U1

theorem SM_gauge_certified : dim_SM_gauge = 12 := rfl

end GIFT.Algebra
