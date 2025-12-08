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

-- =============================================================================
-- EXCEPTIONAL GROUPS F4, E6 (v1.5.0)
-- =============================================================================

/-- Dimension of the exceptional Lie group F4 -/
def dim_F4 : Nat := 52

/-- Dimension of the exceptional Lie group E6 -/
def dim_E6 : Nat := 78

/-- Order of the Weyl group of E8: |W(E8)| = 2^14 * 3^5 * 5^2 * 7 -/
def weyl_E8_order : Nat := 696729600

/-- Dimension of traceless Jordan algebra J3(O)_0 -/
def dim_J3O_traceless : Nat := 26

theorem dim_F4_certified : dim_F4 = 52 := rfl
theorem dim_E6_certified : dim_E6 = 78 := rfl
theorem weyl_E8_order_certified : weyl_E8_order = 696729600 := rfl
theorem dim_J3O_traceless_certified : dim_J3O_traceless = 26 := rfl

-- =============================================================================
-- EXCEPTIONAL GROUP E7 (v1.7.0)
-- =============================================================================

/-- Dimension of the exceptional Lie group E7 -/
def dim_E7 : Nat := 133

/-- Fundamental representation of E7 (56-dimensional) -/
def dim_fund_E7 : Nat := 56

theorem dim_E7_certified : dim_E7 = 133 := rfl
theorem dim_fund_E7_certified : dim_fund_E7 = 56 := rfl

-- =============================================================================
-- PRIME SEQUENCE (for exceptional chain)
-- =============================================================================

/-- The 6th prime number (for E6) -/
def prime_6 : Nat := 13

/-- The 8th prime number (for E7) -/
def prime_8 : Nat := 19

/-- The 11th prime number (for E8) -/
def prime_11 : Nat := 31

theorem prime_6_certified : prime_6 = 13 := rfl
theorem prime_8_certified : prime_8 = 19 := rfl
theorem prime_11_certified : prime_11 = 31 := rfl

end GIFT.Algebra
