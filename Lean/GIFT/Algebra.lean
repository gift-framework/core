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

end GIFT.Algebra
