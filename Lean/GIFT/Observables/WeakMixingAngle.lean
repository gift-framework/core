import Mathlib.Data.Rat.Defs
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

/-- sin^2(theta_W) structural constant = 3/13 -/
def sin2_theta_W : ℚ := 3 / 13

theorem sin2_theta_W_value : sin2_theta_W = 3 / 13 := rfl

/-- Primary: b2 / (b3 + dim_G2) = 21/91 = 3/13 -/
theorem sin2_theta_W_primary :
    (b2 : ℚ) / (b3 + dim_G2) = sin2_theta_W := by
  unfold sin2_theta_W
  norm_num [b2_value, b3_value, Algebraic.G2.dim_G2_eq]

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

/-- 21/91 reduces to 3/13 (GCD = 7) -/
theorem b2_over_91_reduces : (21 : ℚ) / 91 = 3 / 13 := by norm_num

/-- cos^2(theta_W) = 1 - sin^2(theta_W) = 10/13 -/
def cos2_theta_W : ℚ := 10 / 13

theorem cos2_theta_W_complement : cos2_theta_W = 1 - sin2_theta_W := by
  unfold cos2_theta_W sin2_theta_W
  norm_num

end GIFT.Observables.WeakMixingAngle
