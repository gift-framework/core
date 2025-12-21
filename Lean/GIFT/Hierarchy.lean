-- GIFT Hierarchy Module
-- Dimensional hierarchy and mass spectrum from K7 topology
--
-- This module formalizes the GIFT explanation for:
-- 1. The electroweak-Planck hierarchy: M_EW/M_Pl ≈ 10⁻¹⁷
-- 2. Vacuum structure: 21 vacua with VEV = φ⁻²
-- 3. E8 → E6 → SM symmetry breaking cascade
-- 4. Absolute lepton masses: m_τ/m_e, m_μ/m_e, y_τ
--
-- The master formula:
--   M_EW/M_Pl = exp(-H*/rank(E8)) × φ⁻⁵⁴
--             = exp(-99/8) × (φ⁻²)^27
--             ≈ 4.2×10⁻⁶ × 1.17×10⁻¹¹
--             ≈ 4.9×10⁻¹⁷
--
-- All quantities are derived from K7 topology:
--   H* = b₂ + b₃ + 1 = 99  (cohomological degrees)
--   rank(E8) = 8           (Cartan dimension)
--   dim(J₃(O)) = 27        (Jordan algebra)
--   φ⁻² ≈ 0.382            (VEV from 21 vacua)

import GIFT.Hierarchy.DimensionalGap
import GIFT.Hierarchy.VacuumStructure
import GIFT.Hierarchy.E6Cascade
import GIFT.Hierarchy.AbsoluteMasses

/-!
# GIFT Hierarchy Module

## Overview

This module provides the formal verification of the GIFT hierarchy formulas.
The electroweak scale emerges from M-theory compactification on K7,
with all numerical predictions derived from topology.

## Key Results

### Dimensional Gap (DimensionalGap.lean)
- `hierarchy_ratio`: M_EW/M_Pl = exp(-H*/rank) × φ⁻⁵⁴
- `cohom_suppression_magnitude`: exp(-99/8) ∈ (10⁻⁶, 10⁻⁵)
- `jordan_suppression_small`: φ⁻⁵⁴ < 10⁻¹⁰
- `ln_hierarchy_bounds`: ln(M_EW/M_Pl) ∈ (-39, -38)

### Vacuum Structure (VacuumStructure.lean)
- `n_vacua_eq_b2`: N_vacua = b₂ = 21
- `vev_eq_2_minus_phi`: VEV = 2 - φ = φ⁻²
- `moduli_dim_eq_b3`: dim(moduli) = b₃ = 77
- `tcs_total`: 40 + 37 = 77 (TCS construction)

### E6 Cascade (E6Cascade.lean)
- `E8_E6_SU3_branching`: 248 = 78 + 8 + 2×27×3
- `sum_exceptional_ranks`: 8+7+6+4+2 = 27 = dim(J₃(O))
- `fund_E6_eq_J3O`: fund(E6) = 27

### Absolute Masses (AbsoluteMasses.lean)
- `m_tau_m_e_formula`: (b₃-b₂)(κ_T⁻¹+1)+Weyl = 3477
- `m_mu_m_e_theory_bounds`: 206 < 27^φ < 208
- `y_tau_value`: y_τ = 1/98

## Physical Interpretation

The hierarchy problem is SOLVED by K7 topology:

1. **Cohomological suppression** exp(-H*/rank) ≈ 10⁻⁵·⁴
   encodes "how much structure" is compactified.

2. **Jordan suppression** φ⁻⁵⁴ ≈ 10⁻¹¹·³
   encodes the exceptional algebraic structure.

3. Together they give M_EW/M_Pl ≈ 10⁻¹⁷.

The golden ratio φ is NOT put in by hand—it EMERGES
from the G2 geometry of K7.

-/

namespace GIFT.Hierarchy

-- Re-export key definitions and theorems

export DimensionalGap (
  cohom_ratio_nat
  cohom_ratio_value
  cohom_suppression
  cohom_suppression_pos
  cohom_suppression_lt_one
  cohom_suppression_magnitude
  jordan_suppression
  jordan_suppression_eq
  jordan_suppression_pos
  jordan_suppression_small
  hierarchy_ratio
  hierarchy_ratio_pos
  hierarchy_ratio_very_small
  ln_hierarchy
  ln_hierarchy_eq
  ln_hierarchy_bounds
)

export VacuumStructure (
  n_vacua
  n_vacua_eq_b2
  vev_scale
  vev_pos
  vev_lt_one
  vev_eq_2_minus_phi
  vev_bounds
  moduli_dim
  moduli_dim_eq_b3
  tcs_quintic_dim
  tcs_ci_dim
  tcs_total
  vacuum_topology_correspondence
)

export E6Cascade (
  rank_E6
  rank_E7
  rank_F4
  fund_E6
  fund_E6_eq_J3O
  sum_exceptional_ranks
  E8_E6_SU3_branching
  cascade_decreasing
  cascade_differences
)

export AbsoluteMasses (
  betti_difference
  betti_difference_value
  kappa_plus_one
  kappa_plus_one_value
  m_tau_m_e_formula
  m_tau_m_e_expanded
  m_tau_m_e_prime_factorization
  m_mu_m_e_theory
  m_mu_m_e_theory_bounds
  betti_sum
  betti_sum_value
  y_tau_formula
  y_tau_value
  mass_formulas_verified
)

end GIFT.Hierarchy
