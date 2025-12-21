-- GIFT Hierarchy: E6 Cascade
-- The symmetry breaking cascade: E8 → E6 → SM
--
-- The exceptional chain E8 ⊃ E7 ⊃ E6 ⊃ F4 ⊃ G2 provides
-- the gauge symmetry breaking pattern from M-theory to SM.
--
-- Key role of E6:
-- - dim(E6) = 78
-- - rank(E6) = 6
-- - Fundamental representation = 27 = dim(J₃(O))

import GIFT.Core

namespace GIFT.Hierarchy.E6Cascade

open GIFT.Core

/-!
## Exceptional Group Dimensions

The exceptional Lie groups form a chain:
E8 ⊃ E7 ⊃ E6 ⊃ F4 ⊃ G2

Each plays a role in the GIFT framework.
-/

/-- dim(E8) = 248 = 240 roots + 8 Cartan -/
theorem dim_E8_value : dim_E8 = 248 := rfl

/-- dim(E7) = 133 -/
theorem dim_E7_value : dim_E7 = 133 := rfl

/-- dim(E6) = 78 -/
theorem dim_E6_value : dim_E6 = 78 := rfl

/-- dim(F4) = 52 -/
theorem dim_F4_value : dim_F4 = 52 := rfl

/-- dim(G2) = 14 -/
theorem dim_G2_value : dim_G2 = 14 := rfl

/-!
## Rank Structure
-/

/-- rank(E8) = 8 -/
def rank_E8_val : ℕ := rank_E8

/-- rank(E7) = 7 -/
def rank_E7 : ℕ := 7

/-- rank(E6) = 6 -/
def rank_E6 : ℕ := 6

/-- rank(F4) = 4 -/
def rank_F4 : ℕ := 4

/-- rank(G2) = 2 -/
theorem rank_G2_value : rank_G2 = 2 := rfl

/-- Sum of exceptional ranks = 8 + 7 + 6 + 4 + 2 = 27 = dim(J₃(O)) -/
theorem sum_exceptional_ranks : rank_E8 + rank_E7 + rank_E6 + rank_F4 + rank_G2 = dim_J3O := by
  native_decide

/-!
## The E6 Fundamental Representation

The 27-dimensional fundamental representation of E6 is crucial.
It equals dim(J₃(O)), the exceptional Jordan algebra.

This connects gauge theory to the Jordan structure.
-/

/-- Fundamental representation of E6 = 27 -/
def fund_E6 : ℕ := 27

theorem fund_E6_value : fund_E6 = 27 := rfl

/-- fund(E6) = dim(J₃(O)) -/
theorem fund_E6_eq_J3O : fund_E6 = dim_J3O := rfl

/-- The Jordan algebra J₃(O) underlies the E6 representation -/
theorem J3O_underlies_E6 : dim_J3O = 27 := rfl

/-- J₃(O) decomposition: 3 diagonal + 3×8 off-diagonal -/
theorem J3O_dim_decomposition : dim_J3O = 3 + 3 * 8 := by native_decide

/-- Alternative: 27 = 3³ (perfect cube) -/
theorem J3O_cube : dim_J3O = 3 ^ 3 := by native_decide

/-!
## Containment Relations

E8 contains the smaller exceptional groups.
These embeddings define the cascade structure.
-/

/-- E8 contains E6 (dimensionally) -/
theorem E8_contains_E6_dim : dim_E6 < dim_E8 := by native_decide

/-- E8 contains E7 (dimensionally) -/
theorem E8_contains_E7_dim : dim_E7 < dim_E8 := by native_decide

/-- E7 contains E6 (dimensionally) -/
theorem E7_contains_E6_dim : dim_E6 < dim_E7 := by native_decide

/-- E6 contains F4 (dimensionally) -/
theorem E6_contains_F4_dim : dim_F4 < dim_E6 := by native_decide

/-- F4 contains G2 (dimensionally) -/
theorem F4_contains_G2_dim : dim_G2 < dim_F4 := by native_decide

/-- The cascade is strictly decreasing -/
theorem cascade_decreasing :
    dim_G2 < dim_F4 ∧ dim_F4 < dim_E6 ∧ dim_E6 < dim_E7 ∧ dim_E7 < dim_E8 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-!
## E8 → E6 Branching

Under E8 → E6 × SU(3), the adjoint 248 decomposes as:
248 = (78,1) + (1,8) + (27,3) + (27̄,3̄)

Dimension check: 78 + 8 + 27×3 + 27×3 = 78 + 8 + 162 = 248 ✓
-/

/-- E8 branching dimension check -/
theorem E8_E6_SU3_branching :
    dim_E6 + dim_SU3 + 2 * fund_E6 * 3 = dim_E8 := by
  -- 78 + 8 + 2 × 27 × 3 = 78 + 8 + 162 = 248
  native_decide

/-- (27,3) contribution: 27 × 3 = 81 -/
theorem branching_27_3 : fund_E6 * 3 = 81 := by native_decide

/-- Total matter content: 2 × 81 = 162 -/
theorem branching_matter_total : 2 * fund_E6 * 3 = 162 := by native_decide

/-- Adjoint contributions: 78 + 8 = 86 -/
theorem branching_adjoint_total : dim_E6 + dim_SU3 = 86 := by native_decide

/-- Consistency: 86 + 162 = 248 -/
theorem branching_total : dim_E6 + dim_SU3 + 2 * fund_E6 * 3 = 248 := by native_decide

/-!
## Mass Scale Structure

The cascade provides two mass scales:
1. M_Pl → M_GUT: exp(-H*/rank_E8) ~ exp(-99/8)
2. M_GUT → M_EW: φ⁻⁵⁴ ~ (φ⁻²)^27

The exponent 27 = fund(E6) = dim(J₃(O)) appears naturally.
-/

/-- The Jordan exponent in the hierarchy -/
theorem jordan_exponent_structure :
    54 = 2 * fund_E6 ∧
    fund_E6 = dim_J3O ∧
    dim_J3O = 27 := by
  repeat (first | constructor | native_decide | rfl)

/-- Hierarchy suppression uses Jordan dimension -/
theorem hierarchy_uses_jordan : 54 = 2 * dim_J3O := by native_decide

/-!
## Standard Model Emergence

E6 contains the SM gauge group:
E6 ⊃ SO(10) ⊃ SU(5) ⊃ SU(3) × SU(2) × U(1)

dim(SM) = 8 + 3 + 1 = 12
-/

/-- SM gauge group dimension -/
theorem SM_gauge_dim : dim_SM_gauge = 12 := rfl

/-- SM dimension from components -/
theorem SM_decomposition : dim_SU3 + dim_SU2 + dim_U1 = dim_SM_gauge := rfl

/-- E6 → SM reduction: 78 → 12 -/
theorem E6_to_SM_reduction : dim_E6 - dim_SM_gauge = 66 := by native_decide

/-- 66 = 78 - 12 broken generators -/
theorem broken_generators : dim_E6 = dim_SM_gauge + 66 := by native_decide

/-!
## Exceptional Chain Summary

The complete cascade:
E8(248) → E7(133) → E6(78) → F4(52) → G2(14)

Each step corresponds to a symmetry breaking scale.
-/

/-- Dimension differences in the cascade -/
theorem cascade_differences :
    dim_E8 - dim_E7 = 115 ∧
    dim_E7 - dim_E6 = 55 ∧
    dim_E6 - dim_F4 = 26 ∧
    dim_F4 - dim_G2 = 38 := by
  repeat (first | constructor | native_decide)

/-- E8 - E7 = 115 = 5 × 23 -/
theorem E8_E7_diff : dim_E8 - dim_E7 = 115 := by native_decide

/-- E7 - E6 = 55 = F_10 (10th Fibonacci) -/
theorem E7_E6_diff : dim_E7 - dim_E6 = 55 := by native_decide

/-- E6 - F4 = 26 = dim(J₃(O)) - 1 = traceless Jordan -/
theorem E6_F4_diff : dim_E6 - dim_F4 = 26 := by native_decide

/-- 26 = dim_J3O_traceless -/
theorem E6_F4_is_traceless_jordan : dim_E6 - dim_F4 = dim_J3O_traceless := by native_decide

/-- F4 - G2 = 38 = 2 × 19 (uses 8th prime) -/
theorem F4_G2_diff : dim_F4 - dim_G2 = 38 := by native_decide

/-- Total: 248 = 14 + 38 + 26 + 55 + 115 -/
theorem cascade_reconstruction :
    dim_G2 + (dim_F4 - dim_G2) + (dim_E6 - dim_F4) + (dim_E7 - dim_E6) + (dim_E8 - dim_E7) = dim_E8 := by
  native_decide

end GIFT.Hierarchy.E6Cascade
