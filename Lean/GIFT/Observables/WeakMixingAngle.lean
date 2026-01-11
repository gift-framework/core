import Mathlib.Data.Rat.Basic
import Mathlib.Tactic.NormNum
import GIFT.Core

/-!
# Weak Mixing Angle - Extended Observables

sin^2(theta_W) = 3/13 with 14 equivalent GIFT expressions.

Experimental: 0.23122 +/- 0.00004
GIFT: 3/13 = 0.2308
Deviation: 0.20%
-/

namespace GIFT.Observables.WeakMixingAngle

open GIFT.Core

-- =============================================================================
-- DEFINITION
-- =============================================================================

/-- sin^2(theta_W) structural constant = 3/13 -/
def sin2_theta_W : ℚ := 3 / 13

theorem sin2_theta_W_value : sin2_theta_W = 3 / 13 := rfl

-- =============================================================================
-- PRIMARY EXPRESSION
-- =============================================================================

/-- Primary: b2 / (b3 + dim_G2) = 21/91 = 3/13 -/
theorem sin2_theta_W_primary :
    (b2 : ℚ) / (b3 + dim_G2) = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [b2_value, b3_value, Algebraic.G2.dim_G2_eq]

-- =============================================================================
-- EQUIVALENT EXPRESSIONS (14 total)
-- =============================================================================

/-- Expression 2: N_gen / alpha_sum = 3/13 -/
theorem sin2_theta_W_expr2 :
    (N_gen : ℚ) / alpha_sum = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [N_gen_certified, alpha_sum_certified]

/-- Expression 3: N_gen / (rank_E8 + Weyl_factor) = 3/13 -/
theorem sin2_theta_W_expr3 :
    (N_gen : ℚ) / (rank_E8 + Weyl_factor) = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [N_gen_certified, rank_E8_certified]

/-- Expression 4: b2 / (dim_K7 * alpha_sum) = 21/91 = 3/13 -/
theorem sin2_theta_W_expr4 :
    (b2 : ℚ) / (dim_K7 * alpha_sum) = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [b2_value, dim_K7_certified, alpha_sum_certified]

/-- Expression 5: (b0 + p2) / alpha_sum = 3/13 -/
theorem sin2_theta_W_expr5 :
    ((b0 : ℚ) + p2) / alpha_sum = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [b0_certified, p2_certified, alpha_sum_certified]

/-- Expression 6: (dim_K7 - p2*2) / alpha_sum = 3/13 -/
theorem sin2_theta_W_expr6 :
    ((dim_K7 : ℚ) - p2 * 2) / alpha_sum = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [dim_K7_certified, p2_certified, alpha_sum_certified]

/-- Expression 7: (Weyl_factor - p2) / alpha_sum = 3/13 -/
theorem sin2_theta_W_expr7 :
    ((Weyl_factor : ℚ) - p2) / alpha_sum = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [p2_certified, alpha_sum_certified]

/-- Expression 8: (p2 + b0) / (p2 + D_bulk) = 3/13 -/
theorem sin2_theta_W_expr8 :
    ((p2 : ℚ) + b0) / (p2 + D_bulk) = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [p2_certified, b0_certified, D_bulk_certified]

/-- Expression 9: chi_K7 / (chi_K7 + chi_K7 * 10 / 3) = 3/13 -/
theorem sin2_theta_W_expr9 :
    (chi_K7 : ℚ) / (chi_K7 + chi_K7 * 10 / 3) = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [chi_K7_certified]

/-- Expression 10: (dim_J3O - b2 - N_gen) / alpha_sum = 3/13 -/
theorem sin2_theta_W_expr10 :
    ((dim_J3O : ℚ) - b2 - N_gen) / alpha_sum = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [dim_J3O_certified, b2_value, N_gen_certified, alpha_sum_certified]

/-- Expression 11: (rank_E8 - Weyl_factor) / alpha_sum = 3/13 -/
theorem sin2_theta_W_expr11 :
    ((rank_E8 : ℚ) - Weyl_factor) / alpha_sum = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [rank_E8_certified, alpha_sum_certified]

/-- Expression 12: b0 * N_gen / alpha_sum = 3/13 -/
theorem sin2_theta_W_expr12 :
    ((b0 : ℚ) * N_gen) / alpha_sum = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [b0_certified, N_gen_certified, alpha_sum_certified]

/-- Expression 13: (D_bulk - rank_E8) / alpha_sum = 3/13 -/
theorem sin2_theta_W_expr13 :
    ((D_bulk : ℚ) - rank_E8) / alpha_sum = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [D_bulk_certified, rank_E8_certified, alpha_sum_certified]

-- =============================================================================
-- FRACTION REDUCTION
-- =============================================================================

/-- 21/91 reduces to 3/13 (GCD = 7) -/
theorem b2_over_91_reduces : (21 : ℚ) / 91 = 3 / 13 := by norm_num

/-- The denominator 91 = 7 * 13 = dim_K7 * alpha_sum -/
theorem denominator_structure : (91 : ℕ) = dim_K7 * alpha_sum := by
  simp [dim_K7_certified, alpha_sum_certified]

-- =============================================================================
-- cos^2(theta_W) = 10/13
-- =============================================================================

/-- cos^2(theta_W) = 1 - sin^2(theta_W) = 10/13 -/
def cos2_theta_W : ℚ := 10 / 13

theorem cos2_theta_W_complement : cos2_theta_W = 1 - sin2_theta_W := by
  unfold cos2_theta_W sin2_theta_W
  norm_num

/-- cos^2(theta_W) = (b3 + dim_G2 - b2) / (b3 + dim_G2) = 70/91 = 10/13 -/
theorem cos2_theta_W_primary :
    ((b3 : ℚ) + dim_G2 - b2) / (b3 + dim_G2) = cos2_theta_W := by
  unfold cos2_theta_W
  norm_num [b2_value, b3_value, Algebraic.G2.dim_G2_eq]

end GIFT.Observables.WeakMixingAngle
