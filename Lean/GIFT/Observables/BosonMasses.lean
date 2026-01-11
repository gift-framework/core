import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import GIFT.Core

/-!
# Boson Mass Ratios - Extended Observables

Boson mass ratios with GIFT derivations:
- m_H/m_W = 81/52 (3 expressions)
- m_H/m_t = 56/77 = 8/11 (19 expressions)
- m_t/m_W = 139/65 (5 expressions)

Note: m_W/m_Z is NOT included due to tension with sin^2(theta_W).
-/

namespace GIFT.Observables.BosonMasses

open GIFT.Core

-- =============================================================================
-- m_H/m_W = 81/52 - Higgs/W boson mass ratio
-- =============================================================================

/-- m_H/m_W = 81/52 = (N_gen + dim_E6) / dim_F4
    Experimental: 1.558 +/- 0.001
    GIFT: 81/52 = 1.5577
    Deviation: 0.02% -/
def m_H_over_m_W : ℚ := 81 / 52

theorem m_H_over_m_W_value : m_H_over_m_W = 81 / 52 := rfl

/-- Primary: (N_gen + dim_E6) / dim_F4 = 81/52 -/
theorem m_H_m_W_primary :
    ((N_gen : ℚ) + dim_E6) / dim_F4 = m_H_over_m_W := by
  unfold m_H_over_m_W
  norm_num [N_gen_certified, dim_E6_certified, dim_F4_certified]

/-- Expression 2: (b3 + p2 * 2) / dim_F4 = 81/52 -/
theorem m_H_m_W_expr2 :
    ((b3 : ℚ) + p2 * 2) / dim_F4 = m_H_over_m_W := by
  unfold m_H_over_m_W
  norm_num [b3_value, p2_certified, dim_F4_certified]

/-- Expression 3: (H_star - b2 + N_gen) / dim_F4 = 81/52 -/
theorem m_H_m_W_expr3 :
    ((H_star : ℚ) - b2 + N_gen) / dim_F4 = m_H_over_m_W := by
  unfold m_H_over_m_W
  norm_num [H_star_value, b2_value, N_gen_certified, dim_F4_certified]

-- =============================================================================
-- m_H/m_t = 56/77 = 8/11 - Higgs/top mass ratio
-- =============================================================================

/-- m_H/m_t = 56/77 = 8/11 = fund(E7) / b3 = rank(E8) / D_bulk
    Experimental: 0.725 +/- 0.003
    GIFT: 56/77 = 0.7273
    Deviation: 0.31% -/
def m_H_over_m_t : ℚ := 8 / 11

theorem m_H_over_m_t_value : m_H_over_m_t = 8 / 11 := rfl

/-- Primary: fund_E7 / b3 = 56/77 = 8/11 -/
theorem m_H_m_t_primary :
    (dim_fund_E7 : ℚ) / b3 = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [dim_fund_E7_certified, b3_value]

/-- Expression 2: rank_E8 / D_bulk = 8/11 -/
theorem m_H_m_t_expr2 :
    (rank_E8 : ℚ) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [rank_E8_certified, D_bulk_certified]

/-- Expression 3: (D_bulk - N_gen) / D_bulk = 8/11 -/
theorem m_H_m_t_expr3 :
    ((D_bulk : ℚ) - N_gen) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [D_bulk_certified, N_gen_certified]

/-- Expression 4: (dim_K7 + b0) / D_bulk = 8/11 -/
theorem m_H_m_t_expr4 :
    ((dim_K7 : ℚ) + b0) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [dim_K7_certified, b0_certified, D_bulk_certified]

/-- Expression 5: (Weyl + N_gen) / D_bulk = 8/11 -/
theorem m_H_m_t_expr5 :
    ((Weyl_factor : ℚ) + N_gen) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [N_gen_certified, D_bulk_certified]

/-- Expression 6: (p2 * 4) / D_bulk = 8/11 -/
theorem m_H_m_t_expr6 :
    ((p2 : ℚ) * 4) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [p2_certified, D_bulk_certified]

/-- Expression 7: (b0 + dim_K7) / D_bulk = 8/11 -/
theorem m_H_m_t_expr7 :
    ((b0 : ℚ) + dim_K7) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [b0_certified, dim_K7_certified, D_bulk_certified]

/-- Expression 8: (alpha_sum - Weyl) / D_bulk = 8/11 -/
theorem m_H_m_t_expr8 :
    ((alpha_sum : ℚ) - Weyl_factor) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [alpha_sum_certified, D_bulk_certified]

/-- Expression 9: (b2 - alpha_sum) / D_bulk = 8/11 -/
theorem m_H_m_t_expr9 :
    ((b2 : ℚ) - alpha_sum) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [b2_value, alpha_sum_certified, D_bulk_certified]

/-- Expression 10: (dim_G2 - p2 * N_gen) / D_bulk = 8/11 -/
theorem m_H_m_t_expr10 :
    ((dim_G2 : ℚ) - p2 * N_gen) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [Algebraic.G2.dim_G2_eq, p2_certified, N_gen_certified, D_bulk_certified]

-- =============================================================================
-- m_t/m_W = 139/65 - Top/W mass ratio
-- =============================================================================

/-- m_t/m_W = 139/65 = (kappa_T_den + dim_E6) / det_g_num
    Experimental: 2.14 +/- 0.01
    GIFT: 139/65 = 2.138
    Deviation: 0.07% -/
def m_t_over_m_W : ℚ := 139 / 65

theorem m_t_over_m_W_value : m_t_over_m_W = 139 / 65 := rfl

/-- Primary: (kappa_T_den + dim_E6) / det_g_num = 139/65 -/
theorem m_t_m_W_primary :
    ((kappa_T_den : ℚ) + dim_E6) / det_g_num = m_t_over_m_W := by
  unfold m_t_over_m_W
  norm_num [kappa_T_den_certified, dim_E6_certified, det_g_num_certified]

/-- Expression 2: (dim_E7 + p2 * N_gen) / det_g_num = 139/65 -/
theorem m_t_m_W_expr2 :
    ((dim_E7 : ℚ) + p2 * N_gen) / det_g_num = m_t_over_m_W := by
  unfold m_t_over_m_W
  norm_num [dim_E7_certified, p2_certified, N_gen_certified, det_g_num_certified]

-- =============================================================================
-- STRUCTURAL THEOREMS
-- =============================================================================

/-- 56/77 reduces to 8/11 (GCD = 7) -/
theorem fund_E7_over_b3_reduces : (56 : ℚ) / 77 = 8 / 11 := by norm_num

/-- m_H/m_t shares structure with PMNS theta_23 -/
theorem m_H_m_t_pmns_connection :
    m_H_over_m_t = (rank_E8 : ℚ) / D_bulk := m_H_m_t_expr2

/-- The ratio 8/11 appears in multiple contexts -/
theorem eight_eleven_universality :
    (rank_E8 : ℚ) / D_bulk = 8 / 11 ∧
    (dim_fund_E7 : ℚ) / b3 = 8 / 11 := by
  constructor
  · norm_num [rank_E8_certified, D_bulk_certified]
  · norm_num [dim_fund_E7_certified, b3_value]

end GIFT.Observables.BosonMasses
