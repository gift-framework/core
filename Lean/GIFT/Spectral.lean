/-
GIFT Spectral Module
====================

Spectral theory foundations for the Yang-Mills mass gap.

## Overview

This module formalizes the spectral gap result:
  ev₁(K7) = (dim(G₂) − h) / H* = 13/99

The key insight: the mass gap is determined by TOPOLOGY, not dynamics.

## Contents (v3.3.16)

### Spectral Theory Foundation
- `SpectralTheory`: Laplacian, spectral theorem, mass gap definition

### G₂ Holonomy Manifolds
- `G2Manifold`: G₂ holonomy, K7 construction, TCS connection, parallel spinors

### Universal Spectral Law
- `UniversalLaw`: ev₁ × H* = dim(G₂) − h, the universal identity
- `MassGapRatio`: The 14/99 bare ratio (algebraic)
- `PhysicalSpectralGap`: The 13/99 physical ratio (zero axioms)

### TCS Spectral Bounds (v3.3.12)
- `NeckGeometry`: TCS manifold structure and hypotheses (H1)-(H6)
- `TCSBounds`: Model Theorem - ev₁ ~ 1/L² for TCS manifolds

### Selection Principle (v3.3.14)
- `SelectionPrinciple`: kappa = pi^2/14, building blocks, L^2 = kappa*H*
- `RefinedSpectralBounds`: Refined bounds with H7 hypothesis, pi^2 coefficient

### Literature Axioms (Langlais 2024, CGN 2024)
- `LiteratureAxioms`: Spectral density formula, no small eigenvalues

### Selberg Bridge (v3.3.16)
- `SelbergBridge`: Trace formula connecting MollifiedSum to Spectral

### Applications
- `CheegerInequality`: Cheeger-Buser bounds
- `YangMills`: Connection to Clay Millennium Prize

## References

- Joyce, D.D. (2000). Compact Manifolds with Special Holonomy
- Cheeger, J. (1970). A lower bound for the smallest eigenvalue of the Laplacian
- Jaffe, A. & Witten, E. (2000). Yang-Mills Existence and Mass Gap
- Kovalev, A. (2003). Twisted connected sums and special Riemannian holonomy
- Selberg, A. (1956). Harmonic analysis and discontinuous groups
- Duistermaat, J.J. & Guillemin, V. (1975). Invent. Math. 29:39-79

Version: 2.3.0
-/

-- Spectral theory foundations
import GIFT.Spectral.SpectralTheory

-- G₂ holonomy manifolds
import GIFT.Spectral.G2Manifold

-- Universal law, mass gap ratio, physical spectral gap
import GIFT.Spectral.UniversalLaw
import GIFT.Spectral.MassGapRatio
import GIFT.Spectral.PhysicalSpectralGap

-- TCS Spectral Bounds
import GIFT.Spectral.NeckGeometry
import GIFT.Spectral.TCSBounds

-- Selection Principle (NEW in v3.3.14)
import GIFT.Spectral.SelectionPrinciple
import GIFT.Spectral.RefinedSpectralBounds

-- Literature Axioms (Langlais 2024, CGN 2024)
import GIFT.Spectral.LiteratureAxioms

-- Selberg Bridge: MollifiedSum <-> Spectral connection (v3.3.16)
import GIFT.Spectral.SelbergBridge

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
-- RE-EXPORTS: SELECTION PRINCIPLE (NEW in v3.3.14)
-- ============================================================================

export SelectionPrinciple (
  -- Pi bounds (documented numerical axioms - see PiBounds.lean)
  -- Selection constant
  pi_squared
  pi_squared_pos
  pi_squared_gt_9
  pi_squared_lt_10
  kappa
  kappa_pos
  kappa_rough_bounds
  -- Building blocks
  QuinticBlock
  CIBlock
  M1
  M2
  -- Mayer-Vietoris
  mayer_vietoris_b2
  mayer_vietoris_b3
  building_blocks_match_K7
  building_blocks_sum
  -- Neck length
  L_squared_canonical
  L_squared_canonical_pos
  L_canonical
  L_canonical_pos
  L_canonical_rough_bounds
  -- Spectral gap
  lambda1_gift
  lambda1_gift_eq
  spectral_gap_from_selection
  -- Spectral-Holonomy Principle
  spectral_holonomy_principle
  spectral_holonomy_alt
  spectral_holonomy_numerical
  spectral_geometric_identity
  -- Axioms
  selection_principle_holds
  universality_conjecture
  -- Certificate
  selection_principle_certificate
)

-- ============================================================================
-- RE-EXPORTS: REFINED SPECTRAL BOUNDS (NEW in v3.3.14)
-- ============================================================================

export RefinedSpectralBounds (
  -- H7 hypothesis
  CrossSectionGap
  TCSHypothesesExt
  -- Decay parameter
  decayParameter
  decayParameter_pos
  -- Spectral coefficient
  spectralCoefficient
  spectralCoefficient_pos
  spectralCoefficient_approx
  -- Main theorem
  refined_spectral_bounds
  spectral_gap_vanishes_at_rate
  coefficient_is_pi_squared
  -- GIFT connection
  gift_connection_algebraic
  gift_neck_length_algebraic
  refined_bounds_certificate
  -- Backwards compatibility
  tier1_spectral_bounds
  tier1_bounds_certificate
)

-- ============================================================================
-- RE-EXPORTS: LITERATURE AXIOMS (Langlais 2024, CGN 2024)
-- ============================================================================

export LiteratureAxioms (
  CrossSection
  K3_betti
  K3_S1
  K3_S1_dim
  eigenvalue_count
  langlais_spectral_density
  density_coefficient_K3S1
  K3_S1_density_coeff_2
  K3_S1_density_coeff_3
  cgn_no_small_eigenvalues
  cgn_cheeger_lower_bound
  torsion_free_correction
  canonical_neck_length_conjecture
  gift_prediction_structure
  gift_prediction_in_range
  literature_axioms_certificate
)

-- ============================================================================
-- RE-EXPORTS: PHYSICAL SPECTRAL GAP (v3.3.16, zero axioms)
-- ============================================================================

export PhysicalSpectralGap (
  -- Core definitions
  physical_gap_num
  physical_gap_den
  physical_gap_ratio
  -- Derivation from topology
  physical_gap_num_eq
  physical_gap_den_eq
  physical_gap_ratio_value
  physical_gap_from_topology
  -- Algebraic properties
  physical_gap_irreducible
  physical_gap_coprime
  numerator_prime
  -- Spectral-holonomy identity
  spectral_holonomy_corrected
  spectral_holonomy_from_topology
  -- Bare vs physical
  bare_minus_physical
  correction_from_spinors
  -- Cross-holonomy
  SU3_spectral_product
  cross_holonomy_integers
  -- Pell connection
  pell_equation
  -- Certificate
  physical_spectral_gap_certificate
)

-- ============================================================================
-- RE-EXPORTS: SELBERG BRIDGE (v3.3.16)
-- ============================================================================

export SelbergBridge (
  -- Trace formula types
  LengthSpectrum
  geodesicLength
  geodesicAmplitude
  -- Cross-module identities
  kmax_equals_N_gen
  physical_spectral_equals_alpha_sum
  spectral_gap_in_kernel_support
  -- Certificate
  selberg_bridge_certificate
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
| Bare ratio | 14/99 | dim(G₂) / H* |
| Physical ratio | 13/99 | (dim(G₂) − h) / H* |
| Spinor correction | 1/99 | h / H* (Berger) |
| Denominator | 99 | H* = b₂ + b₃ + 1 |
| Cheeger bound | 49/9801 | (14/99)²/4 |
| Graph Laplacian (N=50K) | 0.1313 | Numerical confirmation |
| Physical mass gap | 26.26 MeV | (13/99) x 200 MeV |

## Module Hierarchy

```
Spectral/
├── SpectralTheory.lean          # Laplacian, spectral theorem
├── G2Manifold.lean              # G₂ holonomy, K7, parallel spinors
├── UniversalLaw.lean            # ev₁ x H* = dim(G₂) - h
├── MassGapRatio.lean            # 14/99 bare algebraic
├── PhysicalSpectralGap.lean     # 13/99 physical (zero axioms)
├── NeckGeometry.lean            # TCS structure, hypotheses (H1)-(H6)
├── TCSBounds.lean               # Model Theorem: ev₁ ~ 1/L^2
├── SelectionPrinciple.lean      # kappa = pi^2/14, building blocks
├── RefinedSpectralBounds.lean   # H7 hypothesis, pi^2 coefficient
├── LiteratureAxioms.lean        # Literature axioms (Langlais, CGN)
├── SelbergBridge.lean           # Trace formula: MollifiedSum <-> Spectral
├── CheegerInequality.lean       # Cheeger-Buser bounds
└── YangMills.lean               # Clay Prize connection
```

## Axiom Summary

**DOCUMENTED NUMERICAL AXIOMS (v3.3.15):**
These bounds are computationally trivial but Mathlib 4.27 doesn't export them directly.
- `pi_gt_three` → π > 3 (needs sqrtTwoAddSeries or future Mathlib)
- `pi_lt_four` → π < 4 (needs sqrtTwoAddSeries or future Mathlib)
- `pi_lt_sqrt_ten` → π < √10 (needs π < 3.16 bound)

See `GIFT/Foundations/PiBounds.lean` for full documentation and elimination paths.

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
| `langlais_spectral_density` | Spectral counting formula | Langlais 2024 |
| `cgn_no_small_eigenvalues` | No small eigenvalues | CGN 2024 |
| `cgn_cheeger_lower_bound` | Cheeger lower bound | CGN 2024 |
| `canonical_neck_length_conjecture` | L² ~ H* conjecture | GIFT conjecture |
| `selection_principle_holds` | L² = κ·H* selection | Variational proof |
| `universality_conjecture` | λ₁·H* = dim(G₂) for all TCS | Geometric analysis |
| `localization_lemma` | Eigenfunction localization | Mazzeo-Melrose |
| `spectral_lower_bound_refined` | pi^2/L^2 - exp correction | Poincare + localization |
| `trace_formula` | Selberg trace formula | Microlocal analysis |
| `geodesic_prime_correspondence` | l_gamma = c log(p) | TCS geodesic analysis |
| `geometric_side_matches_mollified` | Geom. side ~ S_w(T) | Stationary phase on K7 |
-/

end GIFT.Spectral
