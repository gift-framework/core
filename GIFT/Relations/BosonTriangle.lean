-- GIFT Relations: Boson triangle assembly (R1c test, m_H/m_W)
--
-- R1c follow-on to KoideAssembly. Core (GIFT.Observables.BosonMasses) carries
-- THREE independent direct formulas approximating the same physical masses:
--
--     m_H / m_W  = (N_gen + dim_E6) / dim_F4         = 81 / 52
--     m_H / m_t  = rank_E8 / D_bulk                  =  8 / 11
--     m_t / m_W  = (kappa_T_den + dim_E6) / det_g_num = 139 / 65
--
-- If these are all approximations to the same physical ratios, the triangle
-- closure (m_H/m_t) * (m_t/m_W) = m_H/m_W must hold. This module checks it.
--
-- Results proven here (machine-checked, no sorry):
--   * `boson_triangle_gap` — the exact rational gap
--         81/52 - (8/11) * (139/65) = 7/2860.
--   * `boson_triangle_not_closed` — the strict inequality
--         (8/11) * (139/65)  <  81/52.
--   * `mt_mw_assembled_ne_direct` and `mh_mt_assembled_ne_direct` — the two
--     companion inconsistencies when one fixes the direct m_H/m_W and tries to
--     recover m_t/m_W or m_H/m_t from it.
--
-- HONEST READING. The three direct ratios cannot ALL be exact derivations of
-- the physical masses: their product triangle fails to close by 7/2860 (about
-- 0.157 %), which is ~5x the deviation of the best direct ratio (m_H/m_W, 0.04%
-- off experiment) from experiment. As with KoideAssembly, R1c ("phenomenon
-- assembled from independent topological inputs") fails on the boson side: the
-- direct fit is sharper than what the framework's own internal routes produce
-- when composed. Unlike Koide, the gap is purely rational and decided by
-- `native_decide` -- no transcendental chain is needed.
-- See private script canonical/scripts/boson_triangle_assembly.py.

import Mathlib
import GIFT.Observables.BosonMasses

namespace GIFT.Relations.BosonTriangle

open GIFT.Observables.BosonMasses

-- The three GIFT direct rationals (re-exported for clarity).

/-- GIFT direct: m_H/m_W = 81/52. -/
theorem mh_mw_direct_value : m_H_over_m_W = (81 : ℚ) / 52 := m_H_over_m_W_value

/-- GIFT direct: m_H/m_t = 8/11. -/
theorem mh_mt_direct_value : m_H_over_m_t = (8 : ℚ) / 11 := m_H_over_m_t_value

/-- GIFT direct: m_t/m_W = 139/65. -/
theorem mt_mw_direct_value : m_t_over_m_W = (139 : ℚ) / 65 := m_t_over_m_W_value

-- =============================================================================
-- The triangle assembly
-- =============================================================================

/-- The assembled m_H/m_W obtained by composing the two other direct ratios. -/
def mh_mw_assembled : ℚ := m_H_over_m_t * m_t_over_m_W

/-- Closed form of the assembly: (8/11) * (139/65) = 1112/715. -/
theorem mh_mw_assembled_value : mh_mw_assembled = (1112 : ℚ) / 715 := by
  unfold mh_mw_assembled
  rw [m_H_over_m_t_value, m_t_over_m_W_value]
  norm_num

-- =============================================================================
-- Triangle does NOT close: exact gap
-- =============================================================================

/-- Exact rational gap of the triangle: 81/52 - 1112/715 = 7/2860. -/
theorem boson_triangle_gap :
    m_H_over_m_W - mh_mw_assembled = (7 : ℚ) / 2860 := by
  rw [m_H_over_m_W_value, mh_mw_assembled_value]
  norm_num

/-- The triangle does NOT close: the assembled m_H/m_W is strictly smaller
    than the direct one. -/
theorem boson_triangle_not_closed : mh_mw_assembled < m_H_over_m_W := by
  rw [m_H_over_m_W_value, mh_mw_assembled_value]
  norm_num

/-- Equivalent statement: equality fails. -/
theorem boson_triangle_neq : mh_mw_assembled ≠ m_H_over_m_W := by
  exact ne_of_lt boson_triangle_not_closed

-- =============================================================================
-- Companion inconsistencies (the two other corners of the triangle)
-- =============================================================================

/-- If the direct m_H/m_W and m_H/m_t are taken as primary, the implied m_t/m_W
    is 891/416, NOT the direct 139/65. -/
theorem mt_mw_from_others :
    m_H_over_m_W / m_H_over_m_t = (891 : ℚ) / 416 := by
  rw [m_H_over_m_W_value, m_H_over_m_t_value]
  norm_num

/-- The implied m_t/m_W disagrees with the direct GIFT formula. -/
theorem mt_mw_assembled_ne_direct :
    m_H_over_m_W / m_H_over_m_t ≠ m_t_over_m_W := by
  rw [mt_mw_from_others, m_t_over_m_W_value]
  norm_num

/-- If the direct m_H/m_W and m_t/m_W are taken as primary, the implied m_H/m_t
    is 405/556, NOT the direct 8/11. -/
theorem mh_mt_from_others :
    m_H_over_m_W / m_t_over_m_W = (405 : ℚ) / 556 := by
  rw [m_H_over_m_W_value, m_t_over_m_W_value]
  norm_num

/-- The implied m_H/m_t disagrees with the direct GIFT formula. -/
theorem mh_mt_assembled_ne_direct :
    m_H_over_m_W / m_t_over_m_W ≠ m_H_over_m_t := by
  rw [mh_mt_from_others, m_H_over_m_t_value]
  norm_num

-- =============================================================================
-- Summary
-- =============================================================================

/-- The R1c verdict for the boson sector: the three direct GIFT rationals
    do NOT form a closed triangle. Concretely, the product of two of them
    differs from the third by the exact rational 7/2860 (~0.157 %). -/
theorem boson_R1c_fails :
    m_H_over_m_t * m_t_over_m_W ≠ m_H_over_m_W ∧
    m_H_over_m_W - m_H_over_m_t * m_t_over_m_W = (7 : ℚ) / 2860 := by
  refine ⟨?_, ?_⟩
  · -- the assembly is not the direct value
    have h := boson_triangle_not_closed
    unfold mh_mw_assembled at h
    exact ne_of_lt h
  · -- the gap is exactly 7/2860
    have h := boson_triangle_gap
    unfold mh_mw_assembled at h
    exact h

end GIFT.Relations.BosonTriangle
