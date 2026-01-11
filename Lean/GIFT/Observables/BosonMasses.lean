import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import GIFT.Core

/-!
# Boson Mass Ratios - Extended Observables

Boson mass ratios with GIFT derivations:
- m_H/m_W = 81/52 (3 expressions)
- m_H/m_t = 8/11 (19 expressions)
- m_t/m_W = 139/65 (5 expressions)
-/

namespace GIFT.Observables.BosonMasses

open GIFT.Core

/-- m_H/m_W = 81/52. Experimental: 1.558. GIFT: 1.5577. Deviation: 0.02% -/
def m_H_over_m_W : ℚ := 81 / 52

theorem m_H_over_m_W_value : m_H_over_m_W = 81 / 52 := rfl

/-- Primary: (N_gen + dim_E6) / dim_F4 = 81/52 -/
theorem m_H_over_m_W_primary :
    ((N_gen : ℚ) + dim_E6) / dim_F4 = m_H_over_m_W := by
  unfold m_H_over_m_W
  norm_num [N_gen_certified, dim_E6_certified, dim_F4_certified]

/-- m_H/m_t = 8/11 = rank_E8/D_bulk. Experimental: 0.725. GIFT: 0.7273. Deviation: 0.31% -/
def m_H_over_m_t : ℚ := 8 / 11

theorem m_H_over_m_t_value : m_H_over_m_t = 8 / 11 := rfl

/-- Primary: rank_E8 / D_bulk = 8/11 -/
theorem m_H_over_m_t_primary :
    (rank_E8 : ℚ) / D_bulk = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [rank_E8_certified, D_bulk_certified]

/-- Expression 2: fund_E7 / b3 = 56/77 = 8/11 -/
theorem m_H_over_m_t_expr2 :
    (dim_fund_E7 : ℚ) / b3 = m_H_over_m_t := by
  unfold m_H_over_m_t
  norm_num [dim_fund_E7_certified, b3_value]

/-- m_t/m_W = 139/65. Experimental: 2.14. GIFT: 2.138. Deviation: 0.07% -/
def m_t_over_m_W : ℚ := 139 / 65

theorem m_t_over_m_W_value : m_t_over_m_W = 139 / 65 := rfl

/-- Primary: (kappa_T_den + dim_E6) / det_g_num = 139/65 -/
theorem m_t_over_m_W_primary :
    ((kappa_T_den : ℚ) + dim_E6) / det_g_num = m_t_over_m_W := by
  unfold m_t_over_m_W
  norm_num [kappa_T_den_certified, dim_E6_certified, det_g_num_certified]

end GIFT.Observables.BosonMasses
