/-
GIFT Spectral Module
====================

Spectral theory foundations for the Yang-Mills mass gap.

## Overview

This module formalizes the spectral gap result:
  lambda_1(K7) = dim(G2)/H* = 14/99

The key insight: the mass gap is determined by TOPOLOGY, not dynamics.

## Contents (v3.3.12)

### Spectral Theory Foundation
- `SpectralTheory`: Laplacian, spectral theorem, mass gap definition

### G₂ Holonomy Manifolds
- `G2Manifold`: G₂ holonomy, K7 construction, TCS connection

### Universal Spectral Law
- `UniversalLaw`: λ₁ × H* = dim(G₂), the KEY theorem
- `MassGapRatio`: The 14/99 theorem (algebraic)

### TCS Spectral Bounds (NEW in v3.3.12)
- `NeckGeometry`: TCS manifold structure and hypotheses (H1)-(H6)
- `TCSBounds`: Model Theorem - λ₁ ~ 1/L² for TCS manifolds

### Applications
- `CheegerInequality`: Cheeger-Buser bounds
- `YangMills`: Connection to Clay Millennium Prize

## References

- Joyce, D.D. (2000). Compact Manifolds with Special Holonomy
- Cheeger, J. (1970). A lower bound for the smallest eigenvalue of the Laplacian
- Jaffe, A. & Witten, E. (2000). Yang-Mills Existence and Mass Gap
- Kovalev, A. (2003). Twisted connected sums and special Riemannian holonomy
- GIFT Framework v3.3.12: TCS spectral bounds

Version: 2.1.0
-/

-- Spectral theory foundations
import GIFT.Spectral.SpectralTheory

-- G₂ holonomy manifolds
import GIFT.Spectral.G2Manifold

-- Universal law and mass gap ratio
import GIFT.Spectral.UniversalLaw
import GIFT.Spectral.MassGapRatio

-- TCS Spectral Bounds (NEW)
import GIFT.Spectral.NeckGeometry
import GIFT.Spectral.TCSBounds

-- Applications
import GIFT.Spectral.CheegerInequality
import GIFT.Spectral.YangMills

namespace GIFT.Spectral

-- ============================================================================
-- RE-EXPORTS: SPECTRAL THEORY
-- ============================================================================

export SpectralTheory (
  CompactManifold
  LaplaceBeltrami
  Eigenvalue
  Spectrum
  MassGap
  mass_gap_positive
)

-- ============================================================================
-- RE-EXPORTS: G₂ MANIFOLD
-- ============================================================================

export G2Manifold (
  G2HolonomyManifold
  K7_Manifold
  K7
  K7_betti_2
  K7_betti_3
  K7_H_star
  G2_manifold_certificate
)

-- ============================================================================
-- RE-EXPORTS: UNIVERSAL LAW
-- ============================================================================

export UniversalLaw (
  K7_mass_gap_eq_gift_ratio
  product_formula
  ratio_irreducible
  ratio_coprime
  physical_mass_gap_MeV
  universal_law_certificate
)

-- ============================================================================
-- RE-EXPORTS: MASS GAP RATIO
-- ============================================================================

export MassGapRatio (
  -- Core definitions
  mass_gap_ratio
  mass_gap_ratio_num
  mass_gap_ratio_den
  cheeger_lower_bound
  -- Key theorems
  mass_gap_ratio_value
  mass_gap_ratio_irreducible
  mass_gap_coprime
  mass_gap_from_holonomy_cohomology
  mass_gap_tight_bound
  cheeger_bound_value
  cheeger_bound_positive
  -- Yang-Mills connection
  GIFT_mass_gap_MeV
  mass_gap_prediction
  mass_gap_exact
  -- Master certificate
  mass_gap_ratio_certified
)

-- ============================================================================
-- RE-EXPORTS: NECK GEOMETRY (TCS)
-- ============================================================================

export NeckGeometry (
  TCSManifold
  BoundedNeckVolume
  ProductNeckMetric
  BlockCheegerBound
  BalancedBlocks
  NeckMinimality
  TCSHypotheses
  L₀
  L₀_pos
  typical_parameters
  neck_geometry_certificate
)

-- ============================================================================
-- RE-EXPORTS: TCS BOUNDS
-- ============================================================================

export TCSBounds (
  c₁
  c₁_pos
  c₂_robust
  c₂_robust_pos
  c₂_symmetric
  spectral_upper_bound
  spectral_lower_bound
  tcs_spectral_bounds
  spectral_gap_scales_as_inverse_L_squared
  typical_tcs_bounds_algebraic
  tcs_bounds_certificate
)

-- ============================================================================
-- RE-EXPORTS: CHEEGER INEQUALITY
-- ============================================================================

export CheegerInequality (
  CheegerConstant
  K7_cheeger_lower_bound
  mass_gap_exceeds_cheeger
  cheeger_certificate
)

-- ============================================================================
-- RE-EXPORTS: YANG-MILLS
-- ============================================================================

export YangMills (
  CompactSimpleGroup
  YangMillsAction
  YangMillsMassGap
  GIFT_prediction
  mass_gap_in_MeV
  mass_gap_exact_MeV
  ClayMillenniumStatement
  GIFT_provides_candidate
  topological_origin
  yang_mills_certificate
)

/-!
## Quick Reference

| Quantity | Value | GIFT Origin |
|----------|-------|-------------|
| Numerator | 14 | dim(G₂) |
| Denominator | 99 | H* = b₂ + b₃ + 1 |
| Ratio | 14/99 | 0.1414... |
| Cheeger bound | 49/9801 | (14/99)²/4 |
| PINN measurement | 0.1406 | Numerical verification |
| Deviation | 0.57% | < 1% agreement |
| Mass gap | 28.28 MeV | (14/99) × 200 MeV |

## Module Hierarchy

```
Spectral/
├── SpectralTheory.lean     # Laplacian, spectral theorem
├── G2Manifold.lean         # G₂ holonomy, K7
├── UniversalLaw.lean       # λ₁ × H* = 14
├── MassGapRatio.lean       # 14/99 algebraic
├── NeckGeometry.lean       # TCS structure, hypotheses (H1)-(H6)
├── TCSBounds.lean          # Model Theorem: λ₁ ~ 1/L²
├── CheegerInequality.lean  # Cheeger-Buser bounds
└── YangMills.lean          # Clay Prize connection
```

## Axiom Summary

| Axiom | Purpose | Elimination Path |
|-------|---------|------------------|
| `spectral_theorem_discrete` | Discrete spectrum | Full Mathlib Riemannian geometry |
| `K7_spectral_law` | λ₁ × 99 = 14 | Heat kernel + trace formula |
| `K7_cheeger_constant` | h(K7) = 14/99 | Isoperimetric analysis |
| `GIFT_mass_gap_relation` | Δ = λ₁ × Λ_QCD | M-theory compactification |
| `ProductNeckMetric` | Product metric on TCS neck | Differential geometry |
| `NeckMinimality` | Isoperimetric bound on neck | Coarea formula |
| `spectral_upper_bound` | Rayleigh quotient bound | L² space formalization |
| `neck_dominates` | Neck controls Cheeger | Cut classification |
-/

end GIFT.Spectral
