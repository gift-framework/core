# giftpy Usage Guide

Complete documentation for the `giftpy` Python package (v3.3.23).

## Installation

```bash
pip install giftpy
```

For visualization (optional):
```bash
pip install giftpy matplotlib numpy
```

## Quick Start (v3.3.15)

```python
from gift_core import *

# Certified constants
print(SIN2_THETA_W)      # Fraction(3, 13)
print(B2, B3, H_STAR)    # 21, 77, 99 (all DERIVED from TCS!)

# E8 root system (240 actual vectors in R^8)
from gift_core.roots import E8_ROOTS, E8_SIMPLE_ROOTS
print(len(E8_ROOTS))     # 240

# Fano plane / G2 cross product
from gift_core.fano import cross_product, FANO_LINES
u = (1, 0, 0, 0, 0, 0, 0)
v = (0, 1, 0, 0, 0, 0, 0)
print(cross_product(u, v))  # 7D cross product

# K7 topology (v3.3 corrected!)
from gift_core.topology import K7
print(K7.euler_characteristic)  # 0 (NOT 42!)
print(K7.two_b2)                # 42 (structural invariant)

# Verify all relations
from gift_core import verify
print(verify())          # True
```

## New in v3.3.23

### Certificate Modularization

The monolithic `Certificate.lean` (2281 lines, 55 theorems, 233 abbrevs) has been restructured into domain-organized sub-certificates:

```
GIFT/Certificate/
├── Core.lean         # Master: Foundations ∧ Predictions ∧ Spectral
├── Foundations.lean  # E₈, G₂, octonions, K₇, Joyce, conformal rigidity
├── Predictions.lean  # 33+ published relations, V5.0 observables, hierarchy
└── Spectral.lean     # Mass gap 14/99, TCS bounds, selection principle
```

**Lean 4 usage:**

```lean
-- Import the master certificate
import GIFT.Certificate.Core

-- Access sub-certificates
#check GIFT.Certificate.gift_master_certificate
-- : Foundations.statement ∧ Predictions.statement ∧ Spectral.statement

-- Or import individual pillars
import GIFT.Certificate.Predictions
#check GIFT.Certificate.Predictions.observables_certified
```

**Adding new relations:** Add imports and abbrevs to the appropriate sub-module (`Foundations.lean`, `Predictions.lean`, or `Spectral.lean`), then add conjuncts to its `def statement : Prop`.

**Backward compatibility:** `import GIFT.Certificate` still works and provides legacy aliases (`all_relations_certified`, etc.).

---

## New in v3.3.18

### Connes Bridge: Weil Positivity ↔ GIFT Mollified Sum

Connects Alain Connes' Weil positivity approach to RH (arXiv:2602.04022, Feb 2026) with the GIFT mollified sum framework. Connes shows that 6 primes {2, 3, 5, 7, 11, 13} recover 50 zeta zeros via Weil quadratic form minimization — GIFT independently uses the same primes through the mollified Dirichlet polynomial.

```lean
import GIFT.Spectral.ConnesBridge

-- Connes' 6 primes and their GIFT connections
#check connes_primes_list                -- [2, 3, 5, 7, 11, 13]
#check connes_primes_all_prime           -- all 6 are prime
#check connes_count_eq_coxeter_G2        -- |primes| = 6 = h(G₂)
#check largest_connes_prime_eq_gap_num   -- 13 = physical spectral gap numerator
#check all_connes_primes_below_dimG2     -- all < 14 = dim(G₂)
#check connes_sum_minus_dimG2_eq_jordan  -- 41 - 14 = 27 = dim(J₃(O))

-- Primorial connections
#check first_3_connes_product_eq_coxeter_E8              -- 2×3×5 = 30 = h(E₈)
#check first_4_connes_product_eq_dimK7_times_coxeter     -- 2×3×5×7 = 210 = 7×30

-- Pell equation bridge
#check pell_and_connes                   -- 99² - 50×14² = 1 and 14-1 = 13

-- Master certificate (19 proven conjuncts)
#check connes_bridge_certificate
```

### Topological Adaptive Cutoff: θ(T) = 10/7 − (14/3)/log(T)

The GIFT-derived adaptive cutoff parameters come from topology, not curve fitting:

- θ\_∞ = (dim(K₇) + N\_gen) / dim(K₇) = (7 + 3)/7 = **10/7**
- Correction = dim(G₂) / N\_gen = **14/3**

```lean
import GIFT.MollifiedSum.AdaptiveGIFT

-- Parameters derived from topology
#check gift_theta_inf_from_topology   -- 10/7 = (dim(K₇) + N_gen) / dim(K₇)
#check gift_theta_corr_from_topology  -- 14/3 = dim(G₂) / N_gen

-- Algebraic properties (all proven, zero axioms)
#check gift_theta_inf_irreducible     -- gcd(10, 7) = 1
#check gift_theta_corr_irreducible    -- gcd(14, 3) = 1
#check gift_theta_inf_gt_one          -- 10/7 > 1
#check gift_theta_inf_lt_three_halves -- 10/7 < 3/2
#check gift_corr_over_inf             -- (14/3) / (10/7) = 49/15
#check numerator_two_perspectives     -- dim(K₇) + N_gen = 2 × Weyl

-- Real-valued function
#check giftTheta                      -- T ↦ 10/7 - (14/3)/log(T)
#check S_gift                         -- GIFT adaptive mollified sum

-- Comparison with empirical fit
#check gift_theta_inf_close_to_empirical  -- |10/7 - 1.4091| < 2%

-- Master certificate (12 proven conjuncts)
#check adaptive_gift_certificate
```

## New in v3.3.17

### Physical Spectral Gap (13/99) & Selberg Bridge

The corrected spectral gap accounts for the parallel spinor from Berger classification:

```lean
import GIFT.Spectral.PhysicalSpectralGap
import GIFT.Spectral.SelbergBridge

-- Physical spectral gap: ev₁ = (dim(G₂) − h) / H* = 13/99
-- where h = 1 parallel spinor for G₂ holonomy (Berger)
#check physical_gap_from_topology   -- (13 : Rat) / 99 = (dim_G2 - parallel_spinors_G2) / H_star
#check physical_gap_irreducible     -- gcd(13, 99) = 1
#check spectral_holonomy_corrected  -- (13 : Rat) / 99 * 99 = 13
#check bare_minus_physical          -- 14/99 - 13/99 = 1/99 = h/H*

-- Cross-holonomy universality
#check SU3_spectral_product         -- dim(SU(3)) - 2 = 6
#check pell_equation                -- 99² - 50 × 14² = 1

-- Selberg Bridge: MollifiedSum <-> Spectral
#check trace_formula                -- Selberg-Duistermaat-Guillemin (Category B)
#check geodesic_prime_correspondence -- l_γ = c · log(p) (Category E)
#check kmax_equals_N_gen            -- standardKMax = N_gen = 3
#check physical_spectral_equals_alpha_sum -- dim(G₂) - h = rank(E₈) + Weyl = 13
#check selberg_bridge_certificate   -- Master certificate
```

**Key identity:** `ev₁ × H* = dim(G₂) − h = 14 − 1 = 13`

| Prediction | Value | ev₁ × H* | Source |
|-----------|-------|----------|--------|
| Bare algebraic | 14/99 = 0.1414 | 14 | Pell equation |
| Physical (corrected) | 13/99 = 0.1313 | 13 | Spectral-holonomy |
| Graph Laplacian (N=50K) | 0.1313 | 13.0 | Numerical |

## New in v3.3.15

### Axiom Classification System

All spectral module axioms now have category labels and academic citations:

```lean
import GIFT.Foundations.PiBounds
import GIFT.Spectral.CheegerInequality

-- π bounds (Category F: Numerical)
#check pi_gt_three              -- π > 3 (numerically verified)
#check pi_lt_four               -- π < 4 (numerically verified)
#check pi_lt_sqrt_ten           -- π < √10 (numerically verified)

-- Derived bounds (proven from axioms)
#check pi_squared_gt_9          -- π² > 9
#check pi_squared_lt_10         -- π² < 10
#check pi_between_3_and_4       -- 3 < π < 4

-- Cheeger inequality (Category B: Standard result)
#check cheeger_inequality       -- λ₁ ≥ h²/4 (Cheeger 1970)
#check buser_inequality         -- λ₁ ≤ C(n)·h (Buser 1982)
#check K7_cheeger_constant      -- h(K7) = 14/99 (Category E: GIFT claim)
```

**Axiom Categories:**

| Category | Description | Example |
|----------|-------------|---------|
| A | Definitions | `CheegerConstant`, `CompactSimpleGroup` |
| B | Standard results | `cheeger_inequality` (Cheeger 1970) |
| C | Geometric structure | `ProductNeckMetric`, `NeckMinimality` |
| D | Literature axioms | `langlais_spectral_density` |
| E | GIFT claims | `K7_cheeger_constant`, `GIFT_mass_gap_relation` |
| F | Numerical (verified) | `pi_gt_three`, `pi_lt_sqrt_ten` |

### Mathlib 4.27 π Bounds Limitation

Note: Mathlib 4.27 does NOT export `Real.pi_gt_314` or `Real.pi_lt_315` directly.
Available bounds:
- `Real.pi_pos` : 0 < π
- `Real.two_le_pi` : 2 ≤ π
- `Real.pi_le_four` : π ≤ 4 (non-strict)

The tighter bounds (π > 3, π < √10) are kept as Category F numerical axioms until
Mathlib exports them or we implement sqrtTwoAddSeries computation.

## New in v3.3.14

### Selection Principle & Refined Spectral Bounds

New modules formalizing the TCS selection principle and refined spectral bounds:

```lean
import GIFT.Spectral.SelectionPrinciple
import GIFT.Spectral.RefinedSpectralBounds

-- Selection constant κ = π²/14
#check kappa                    -- π²/dim(G₂)
#check kappa_pos                -- κ > 0
#check kappa_rough_bounds       -- 9/14 < κ < 10/14

-- Building blocks for K7
#check QuinticBlock             -- Quintic 3-fold (b2=11, b3=40)
#check CIBlock                  -- CI(2,2,2) (b2=10, b3=37)
#check M1                       -- Canonical quintic
#check M2                       -- Canonical CI
#check mayer_vietoris_b2        -- 11 + 10 = 21
#check mayer_vietoris_b3        -- 40 + 37 = 77

-- Canonical neck length
#check L_squared_canonical      -- L*² = κ × H*
#check L_canonical              -- L* = √(κ × H*)
#check L_canonical_pos          -- L* > 0

-- GIFT spectral prediction
#check lambda1_gift             -- λ₁ = dim(G₂)/H* = 14/99
#check spectral_holonomy_principle   -- λ₁ × H* = dim(G₂)
#check spectral_geometric_identity   -- λ₁ × L² = π²

-- Refined spectral bounds (H7 cross-section gap)
#check CrossSectionGap          -- γ > 0 hypothesis
#check TCSHypothesesExt         -- Extended hypotheses with H7
#check refined_spectral_bounds  -- π²/L² - Ce^{-δL} ≤ λ₁ ≤ π²/L² + C/L³
#check spectral_gap_vanishes_at_rate  -- λ₁ = O(1/L²)
#check coefficient_is_pi_squared      -- Coefficient is exactly π²
```

**Key Formulas:**

| Formula | Meaning |
|---------|---------|
| κ = π²/14 | Selection constant |
| L*² = κ × H* = 99π²/14 | Canonical neck length squared |
| λ₁ = 14/99 | GIFT spectral prediction |
| λ₁ × H* = dim(G₂) | Spectral-Holonomy Principle |

## New in v3.3.13

### Literature Axioms for TCS Spectral Theory

New module `LiteratureAxioms.lean` integrating published results:

```lean
import GIFT.Spectral.LiteratureAxioms

-- Cross-section topology
#check CrossSection               -- Structure for TCS cross-sections
#check K3_S1                       -- K3 × S¹ cross-section (dim = 5)
#check K3_betti                    -- K3 surface Betti numbers

-- Langlais 2024 (Comm. Math. Phys.) - Spectral Density
#check langlais_spectral_density
-- Λ_q(s) = 2(b_{q-1}(X) + b_q(X))√s + O(1)

-- Density coefficients for K3 × S¹
#check density_coefficient_K3S1   -- Direct computation
#check K3_S1_density_coeff_2      -- 2-forms: 46
#check K3_S1_density_coeff_3      -- 3-forms: 88

-- CGN 2024 (Inventiones) - No Small Eigenvalues
#check cgn_no_small_eigenvalues   -- ∃ c > 0: no ev in (0, c/L)
#check cgn_cheeger_lower_bound    -- C'/L² ≤ λ₁ (Cheeger-based)

-- Torsion-free correction
#check torsion_free_correction    -- ‖φ̃_T - φ_T‖ ≤ Ce^{-δT}

-- GIFT prediction structure
#check gift_prediction_structure  -- 14/99 = dim(G₂)/H*
#check gift_prediction_in_range   -- 1/100 < 14/99 < 1/4

-- Complete certificate
#check literature_axioms_certificate
```

**Literature References:**

| Axiom | Source | Statement |
|-------|--------|-----------|
| `langlais_spectral_density` | Langlais 2024, Comm. Math. Phys. | Spectral density formula |
| `cgn_no_small_eigenvalues` | CGN 2024, Inventiones | No eigenvalues in (0, c/L) |
| `cgn_cheeger_lower_bound` | CGN 2024, line 3598 | Lower bound from Cheeger |
| `torsion_free_correction` | CGN 2024, Joyce 2000 | Exponential closeness |

**Physical Significance:**

The Model Theorem λ₁ ~ 1/L² combined with:
- Canonical neck length L² ~ H* = 99 (conjectured)
- Holonomy coefficient dim(G₂) = 14 (conjectured)

Yields the GIFT prediction: **λ₁ = 14/99**

---

## New in v3.3.12

### TCS Spectral Bounds (Model Theorem)

New modules for Twisted Connected Sum spectral bounds:

```lean
import GIFT.Spectral.NeckGeometry
import GIFT.Spectral.TCSBounds

-- TCS Manifold Structure
#check TCSManifold                  -- K = M₁ ∪_N M₂ with neck
#check TCSManifold.neckLength       -- L > 0
#check TCSManifold.volume_eq_one    -- (H1) Normalized volume

-- Hypotheses (H2)-(H6)
#check BoundedNeckVolume            -- (H2) Vol(N) ∈ [v₀, v₁]
#check BlockCheegerBound            -- (H4) h(Mᵢ \ N) ≥ h₀
#check BalancedBlocks               -- (H5) Vol(Mᵢ) ∈ [1/4, 3/4]
#check ProductNeckMetric            -- (H3) axiom
#check NeckMinimality               -- (H6) axiom

-- Complete hypothesis bundle
#check TCSHypotheses                -- All (H1)-(H6) combined

-- Threshold neck length
#check L₀                           -- 2v₀/h₀
#check L₀_pos                       -- L₀ > 0 (proven)
```

### Model Theorem: λ₁ ~ 1/L²

```lean
import GIFT.Spectral.TCSBounds

-- Bound constants
#check c₁                           -- v₀² (lower bound coefficient)
#check c₂_robust                    -- 16v₁/(1-v₁) (upper bound)

-- THE MODEL THEOREM
#check tcs_spectral_bounds
-- For L > L₀:  c₁/L² ≤ λ₁(K) ≤ c₂/L²

-- Individual bounds
#check spectral_upper_bound         -- Rayleigh quotient (axiom)
#check spectral_lower_bound         -- Cheeger inequality (axiom)

-- Scaling theorem
#check spectral_gap_scales_as_inverse_L_squared
-- λ₁ = Θ(1/L²)

-- Algebraic verification (proven!)
#check typical_tcs_bounds_algebraic
-- v₀ = v₁ = 1/2, h₀ = 1 gives c₁ = 1/4, c₂ = 16, L₀ = 1

#check tcs_bounds_certificate       -- Complete certificate
```

**Physical Significance:**

For K7 (compact G₂-holonomy manifold from TCS construction):
- Neck length L scales as √H* where H* = b₂ + b₃ + 1 = 99
- Model theorem gives λ₁ ~ 1/L² ~ 1/H*
- Universal law: λ₁ × H* = dim(G₂) → λ₁ = 14/99

---

## New in v3.3.11

### Monster Dimension via Coxeter Numbers

The Monster group's smallest faithful representation dimension (196883) is now expressed
purely in terms of Coxeter numbers and the third Betti number:

```lean
import GIFT.Moonshine.MonsterCoxeter

-- THE MAIN THEOREM: Monster dimension from Coxeter numbers
#check monster_dim_coxeter_formula
-- (b3 - h_G2) * (b3 - h_E7) * (b3 - h_E8) = 196883
-- (77 - 6) * (77 - 18) * (77 - 30) = 71 × 59 × 47 = 196883

-- Coxeter numbers in Core.lean
#check GIFT.Core.h_G2   -- 6  (Coxeter number of G₂)
#check GIFT.Core.h_E6   -- 12 (Coxeter number of E₆)
#check GIFT.Core.h_E7   -- 18 (Coxeter number of E₇)
#check GIFT.Core.h_E8   -- 30 (Coxeter number of E₈)

-- Individual prime factors derived from b₃
#check factor_71_from_coxeter  -- 71 = b₃ - h(G₂) = 77 - 6
#check factor_59_from_coxeter  -- 59 = b₃ - h(E₇) = 77 - 18
#check factor_47_from_coxeter  -- 47 = b₃ - h(E₈) = 77 - 30

-- Structural relations between Coxeter numbers
#check coxeter_additivity      -- h(G₂) + h(E₆) = h(E₇) (6 + 12 = 18)
#check coxeter_ratio_E8_G2     -- h(E₈) / h(G₂) = Weyl_factor (30/6 = 5)
#check coxeter_sum_jordan      -- h(G₂) + h(E₇) + h(E₈) = 2 × dim(J₃(𝕆))

-- Root count formula: |roots| = h × rank
#check E8_roots_coxeter        -- 30 × 8 = 240
#check G2_roots_coxeter        -- 6 × 2 = 12
```

**Mathematical Significance:**

The Monster-Coxeter formula is:
- **Exact**: No remainder or adjustment
- **Intrinsic**: Only fundamental invariants (b₃, Coxeter numbers)
- **Predictive**: Monster dimension follows from Lie theory + G₂ topology

### j-Invariant Coefficient Observations

```lean
import GIFT.Moonshine.JInvariant

-- j(τ) = q⁻¹ + 744 + 196884q + 21493760q² + 864299970q³ + ...

-- Quotient c₂/c₁ ≈ 109 is GIFT-expressible!
#check gift_109              -- 109 = b₃ + dim(G₂) + h(E₇) = 77 + 14 + 18
#check j_coeff_2_quotient    -- floor(c₂/c₁) = 109

-- Quotient c₃/c₂ ≈ 40 is also GIFT-expressible
#check gift_40               -- 40 = b₂ + h(E₇) + b₀ = 21 + 18 + 1
#check j_coeff_3_quotient    -- floor(c₃/c₂) = 40
```

**Note:** These are OBSERVATIONS. The integer parts of c₂/c₁ and c₃/c₂ are GIFT-expressible,
but the remainders have no known interpretation.

---

## New in v3.3.9

### Complete Spectral Theory Formalization

The `GIFT.Spectral` module now provides a comprehensive 4-phase formalization connecting
topology to the Yang-Mills mass gap:

```lean
import GIFT.Spectral

-- Spectral Theory Foundations
#check GIFT.Spectral.SpectralTheory.CompactManifold    -- Abstract compact Riemannian manifold
#check GIFT.Spectral.SpectralTheory.LaplaceBeltrami    -- Laplacian operator structure
#check GIFT.Spectral.SpectralTheory.MassGap            -- First nonzero eigenvalue (axiom)
#check GIFT.Spectral.SpectralTheory.mass_gap_positive  -- MassGap M > 0 (theorem)

-- G₂ Holonomy Manifolds
#check GIFT.Spectral.G2Manifold.G2HolonomyManifold   -- 7D manifolds with G₂ holonomy
#check GIFT.Spectral.G2Manifold.K7                    -- Canonical K7 via TCS construction
#check GIFT.Spectral.G2Manifold.K7_is_7_dimensional   -- dim(K7) = 7 (theorem)

-- Universal Spectral Law
#check GIFT.Spectral.UniversalLaw.K7_spectral_law     -- MassGap(K7) × 99 = 14
#check GIFT.Spectral.UniversalLaw.K7_mass_gap_is_14_over_99  -- λ₁(K7) = 14/99
#check GIFT.Spectral.UniversalLaw.topological_origin  -- 14 from G₂, 99 from cohomology

-- Cheeger-Buser Inequalities
#check GIFT.Spectral.CheegerInequality.CheegerConstant   -- Isoperimetric constant
#check GIFT.Spectral.CheegerInequality.cheeger_inequality -- h²/4 ≤ λ₁ ≤ 2h + 10h²
#check GIFT.Spectral.CheegerInequality.K7_cheeger_bound   -- h(K7) = 7/99 (theorem)

-- Yang-Mills Connection
#check GIFT.Spectral.YangMills.YangMillsMassGap       -- E₁ - E₀ definition
#check GIFT.Spectral.YangMills.GIFT_prediction        -- Δ = (14/99) × 200 MeV
#check GIFT.Spectral.YangMills.mass_gap_in_MeV        -- 28 < Δ < 29 MeV (theorem)
#check GIFT.Spectral.YangMills.topological_origin     -- Mass gap from pure topology
```

**Module Structure:**

| Module | Content | Status |
|--------|---------|--------|
| `SpectralTheory.lean` | Laplacian, spectral theorem, mass gap definition | Axiom-based |
| `G2Manifold.lean` | G₂ holonomy, K7 via TCS construction | Axiom-based |
| `UniversalLaw.lean` | λ₁ × H* = dim(G₂), the key theorem | Axiom-based |
| `CheegerInequality.lean` | Cheeger-Buser bounds: h²/4 ≤ λ₁ | Axiom-based |
| `YangMills.lean` | Gauge theory connection, physical prediction | Axiom-based |
| `MassGapRatio.lean` | Algebraic 14/99 theorems | **Proven** |

**Key Results:**
- Universal spectral law: λ₁(K7) × H* = dim(G2) → λ₁ = 14/99
- Topological origin: numerator from holonomy (14), denominator from cohomology (99)
- Cheeger bound: h(K7) = 7/99, giving h²/4 = 49/39204 as lower bound
- Physical prediction: Δ_YM ≈ 28.28 MeV (within lattice QCD range 20-40 MeV)
- New proven relations: 215+ certified mathematical relationships

---

## New in v3.3.8

### Yang-Mills Mass Gap Module

The key GIFT prediction for Yang-Mills: λ₁(K₇) = dim(G₂)/H* = 14/99

```lean
import GIFT.Spectral

-- Mass gap ratio = 14/99 (proven, no axioms!)
#check GIFT.Spectral.MassGapRatio.mass_gap_ratio_value
-- mass_gap_ratio = 14 / 99

-- Irreducible fraction
#check GIFT.Spectral.MassGapRatio.mass_gap_ratio_irreducible
-- Nat.gcd 14 99 = 1

-- Topological derivation: holonomy / cohomology
#check GIFT.Spectral.MassGapRatio.mass_gap_from_holonomy_cohomology
-- 14/99 = 14/(21 + 77 + 1) = dim(G₂)/(b₂ + b₃ + 1)

-- Cheeger inequality bound
#check GIFT.Spectral.MassGapRatio.cheeger_bound_value
-- (14/99)²/4 = 49/9801

-- Physical prediction: mass gap ≈ 28.28 MeV
#check GIFT.Spectral.MassGapRatio.mass_gap_prediction
-- 28 < (14/99) × 200 < 29 MeV

-- PINN numerical verification: 0.57% deviation
#check GIFT.Spectral.MassGapRatio.deviation_percentage
-- 0.005 < 8/1414 < 0.006
```

**Key Results:**
- Mass gap ratio: 14/99 ≈ 0.1414
- Cheeger lower bound: 49/9801 ≈ 0.005
- PINN measurement: λ₁ = 0.1406 (satisfies Cheeger bound)
- Deviation: < 1% agreement with theory
- Physical prediction: Δ ≈ 28.28 MeV (with Λ_QCD = 200 MeV)

---

## New in v3.3.7

### 🎉 TIER 1 COMPLETE - All Numerical Axioms Proven!

The last two numerical axioms have been converted to theorems:

```lean
import GIFT.Foundations.NumericalBounds
import GIFT.Foundations.GoldenRatioPowers

-- FINAL rpow bounds - NOW PROVEN!
#check rpow_27_1618_gt_206_proven   -- 27^1.618 > 206 PROVEN
#check rpow_27_16185_lt_209_proven  -- 27^1.6185 < 209 PROVEN

-- Muon-electron mass ratio prediction
#check jordan_power_phi_bounds  -- 206 < 27^φ < 209 PROVEN (m_μ/m_e ≈ 206.77)

-- Supporting bounds
#check log_three_bounds_tight   -- 1.098 < log(3) < 1.1 PROVEN
#check log_27_bounds            -- 3.294 < log(27) < 3.3 PROVEN
#check exp_5329_gt_206          -- exp(5.329) > 206 PROVEN
#check exp_5342_lt_209          -- exp(5.342) < 209 PROVEN
```

**Axiom Status:**
- ✅ **Numerical bounds: COMPLETE!** 0 remaining
- ⏳ Algebraic (GL₇ action, G₂ Lie algebra): 2 remaining
- ⏳ Geometric (K7 Hodge theory): 13 remaining

---

## v3.3.6

### Numerical Bounds Axioms - Major Reduction!

Four more axioms converted to theorems:

```lean
import GIFT.Foundations.NumericalBounds
import GIFT.Foundations.GoldenRatioPowers
import GIFT.Hierarchy.DimensionalGap

-- log(5) and log(10) bounds
#check log_five_bounds_tight   -- 1.6 < log(5) < 1.7 PROVEN
#check log_ten_bounds_tight    -- 2.293 < log(10) < 2.394 PROVEN

-- Jordan suppression factor
#check phi_inv_54_very_small   -- φ⁻⁵⁴ < 10⁻¹⁰ PROVEN

-- Cohomological suppression magnitude
#check cohom_suppression_magnitude  -- 10⁻⁶ < exp(-99/8) < 10⁻⁵ PROVEN
```

**Axiom Reduction:** Numerical bounds axioms: 4 → 2

---

## v3.3.5

### Numerical Bounds via Taylor Series (Lean 4)

The `NumericalBounds.lean` module provides axiom-free proofs of transcendental bounds:

```lean
import GIFT.Foundations.NumericalBounds

-- Proven bounds on e (from Mathlib's 9-decimal precision)
#check exp_one_gt      -- 2.7 < e
#check exp_one_lt      -- e < 2.72

-- Proven bounds on φ (golden ratio)
#check phi_bounds      -- 1.618 < φ < 1.6185
#check phi_inv_sq_eq   -- φ⁻² = 2 - φ (algebraic identity)

-- Proven bounds on log(2) (from Mathlib)
#check log_two_bounds  -- 0.693 < log(2) < 0.694

-- KEY RESULT: log(φ) bounds via Taylor series
#check log_phi_bounds  -- 0.48 < log(φ) < 0.49 PROVEN!
#check exp_048_lt      -- exp(0.48) < 1.617 (Taylor upper bound)
#check exp_049_gt      -- 1.631 < exp(0.49) (Taylor lower bound)
```

**Axiom Reduction:** Numerical bounds axioms: 7 → 4 (3 proven)

---

## In v3.3.4

### G₂ Differential Geometry Complete - AXIOM-FREE Hodge Star (Lean 4)

The Geometry module now has **zero axioms**! The key theorem `psi_eq_star_phi` (ψ = ⋆φ) is now PROVEN via explicit Hodge star computation.

```lean
import GIFT.Geometry

-- ψ = ⋆φ is now a THEOREM, not an axiom!
#check HodgeStarR7.psi_eq_star_phi
-- standardG2.psi = star3 standardG2.phi

-- Explicit Hodge star computation
#check HodgeStarCompute.hodgeStar3to4    -- Coefficient-level ⋆ : Ω³ → Ω⁴
#check HodgeStarCompute.hodgeStar4to3    -- Coefficient-level ⋆ : Ω⁴ → Ω³
#check HodgeStarCompute.hodgeStar_invol_3  -- ⋆⋆ = +1 PROVEN

-- Levi-Civita signs for complement bijection
#check HodgeStarCompute.sign3            -- 35 signs for 3→4
#check HodgeStarCompute.complement3to4   -- Index bijection

-- Complete G₂ structure (axiom-free)
#check HodgeStarR7.standardG2Geom        -- (d, ⋆, φ, ψ)
#check HodgeStarR7.standardG2Geom_torsionFree  -- dφ=0 ∧ dψ=0
```

**G₂ Differential Geometry Checklist (all achieved):**
- ✓ φ : Ω³(ℝ⁷) as `DiffForm 3`
- ✓ ψ := ⋆φ **PROVEN** (not axiomatized)
- ✓ TorsionFree := (dφ=0) ∧ (dψ=0)
- ✓ Zero axioms in Geometry module
- ✓ CI green

---

## New in v3.3.3

### DG-Ready Geometry Module (Lean 4)

New `GIFT/Geometry/` module with proper Mathlib-based differential forms infrastructure:

```lean
import GIFT.Geometry

-- Exterior algebra on ℝ⁷
#check Ext                    -- ExteriorAlgebra ℝ V7
#check wedge                  -- ω ∧' η (wedge product)

-- Differential k-forms
#check DiffForm               -- DiffForm k (position-dependent coefficients)
#check ExteriorDerivative     -- d with d²=0
#check trivialExteriorDeriv   -- d=0 for constant forms

-- Hodge star
#check HodgeStar              -- ⋆ : Ωᵏ → Ω⁷⁻ᵏ
#check starStar_sign_positive -- ⋆⋆ = +1 in 7 dimensions

-- Complete G₂ geometric structure
#check G2GeomData             -- (d, ⋆, φ, ψ)
#check standardG2Geom         -- Standard flat ℝ⁷ structure
#check standardG2Geom_torsionFree  -- Proven torsion-free!
```

Key features:
- `DiffForm k` structure with position-dependent coefficients
- `@[ext]` lemma for structure extensionality
- `@[simp]` lemmas for coefficient access (`smul_coeffs`, `add_coeffs`)
- `TorsionFree` condition: dφ = 0 ∧ d(⋆φ) = 0

---

## New in v3.3.2

### G2 Forms Bridge + Analytical Foundations (Lean 4)

Connects abstract G2 differential forms to concrete cross product, plus axiom-free analytical infrastructure:

```lean
import GIFT.Foundations.Analysis.G2Forms.All

-- G2 structure from Fano plane cross product
#check CrossProductG2           -- G2Structure
#check crossProductG2_torsionFree  -- Proof it's torsion-free!

-- phi0 coefficients from epsilon structure constants
#check phi0_coefficients        -- 35 coefficients of canonical 3-form

-- Bridge theorem: unifies abstract forms with concrete cross product
#check g2_forms_bridge_complete
```

**Analytical Foundations (axiom-free):**
```lean
import GIFT.Foundations.Analysis.Sobolev.Basic
import GIFT.Foundations.Analysis.Elliptic.Basic
import GIFT.Foundations.Analysis.IFT.Basic

-- Sobolev embedding: H^4 embeds in C^0 for dim 7
#check K7_embedding_condition   -- 2 * 4 > 7 (native_decide)

-- Elliptic bootstrap: H^0 -> H^2 -> H^4
#check bootstrap_H0_H4          -- 2 iterations

-- Joyce PINN verification
#check K7_pinn_verified         -- 0.00141 < 0.0288
#check K7_safety_margin         -- >20x margin
```

**Also in v3.3.2:**
- Directory rename: `Tier1/` → `G2Forms/` (standard terminology)
- Terminology cleanup across 12 files (B1-B5, A1-A12 → descriptive names)
- CLAUDE.md priority section for academic terminology

---

## New in v3.3.1

### G2 Forms Infrastructure (Lean 4)

Axiom-free formalization of torsion-free G2 structures:

```lean
import GIFT.Foundations.Analysis.G2Forms.All

-- Create a G2 structure
def myG2 : G2Structure := ConstantG2 (fun _ => 0) (fun _ => 0)

-- The torsion-free predicate is now well-typed!
#check myG2.TorsionFree  -- Prop

-- TorsionFree = closed ∧ coclosed
-- where closed = (dφ = 0) and coclosed = (d⋆φ = 0)
```

**Checklist:**
- ✓ Canonical Ωᵏ(M) via `GradedDiffForms`
- ✓ Exterior derivative d with d∘d=0 proven
- ✓ Hodge star ⋆ : Ωᵏ → Ωⁿ⁻ᵏ structure
- ✓ `TorsionFree φ := (dφ = 0) ∧ (d⋆φ = 0)`
- ✓ Zero axioms, build green

---

## New in v3.3.0

### chi(K7) Terminology Fix

**Important correction**: The true Euler characteristic χ(K7) = 0, not 42!

For compact oriented odd-dimensional manifolds, Poincaré duality implies χ = 0.
The value 42 = 2×b₂ is a **structural invariant**, now properly named `two_b2`.

```python
from gift_core.topology import K7

K7.euler_characteristic  # 0 (correct!)
K7.two_b2                # 42 (structural invariant)
```

```lean
import GIFT.Core

#check Core.two_b2                      -- abbrev for 2 * b2 = 42
#check Core.chi_K7_eq_two_b2            -- chi_K7 = two_b2 (same value)
#check Core.euler_char_K7_alternating_sum  -- proves χ = 0
```

## New in v3.2.14

### Fano Selection Principle (Lean 4)

Formalized the mathematical structure explaining WHY certain GIFT formulas work:

```lean
import GIFT.Relations.FanoSelectionPrinciple
import GIFT.Relations.OverDetermination
import GIFT.Relations.SectorClassification

-- Fano basis: constants divisible by 7
#check FanoSelectionPrinciple.fano_basis_complete
-- dim_K7 = 1×7, dim_G2 = 2×7, b2 = 3×7, chi_K7 = 6×7, fund_E7 = 8×7, b3 = 11×7, PSL27 = 24×7

-- N_gen derivation from Fano symmetry
#check FanoSelectionPrinciple.N_gen_from_PSL27_fund_E7  -- N_gen = |PSL(2,7)|/fund(E7) = 168/56 = 3

-- Over-determination: 28 proven expressions for 6 key fractions
#check OverDetermination.over_determination_certificate

-- Sector classification: Gauge / Matter / Holonomy
#check SectorClassification.sector_classification_certified
```

### New Observable: m_W/m_Z = 37/42

```lean
import GIFT.Observables.BosonMasses

#check BosonMasses.m_W_over_m_Z          -- 37/42
#check BosonMasses.m_W_over_m_Z_primary  -- (2b₂ - Weyl)/(2b₂) = 37/42
-- Experimental: 0.8815, GIFT: 0.8810, Deviation: 0.06% (was 8.7%!)
```

## New in v3.2.13

### GitHub Pages Blueprint Update

The blueprint visualization has been streamlined:
- **50+ observables** with **0.24% mean deviation** (updated from 0.087%)
- Dependency graph reduced by 14 nodes (cleaner visualization)
- Orphan nodes connected, redundant clusters merged

## New in v3.2.12

### Extended Observables (Lean 4)

Complete formalization of 22+ physical observables in `GIFT.Observables`:

```lean
import GIFT.Observables

-- Electroweak
#check Observables.sin2_theta_W           -- 3/13
#check Observables.sin2_theta_W_primary   -- b₂/(b₃+dim_G₂) = 3/13

-- PMNS Neutrino Mixing
#check Observables.sin2_theta12           -- 4/13
#check Observables.sin2_theta23           -- 6/11
#check Observables.sin2_theta13           -- 11/496

-- Quark Masses
#check Observables.m_s_over_m_d           -- 20
#check Observables.m_b_over_m_t           -- 1/42 (THE 42!)

-- Boson Masses
#check Observables.m_H_over_m_W           -- 81/52
#check Observables.m_Z_over_m_W           -- 11/10

-- CKM Matrix
#check Observables.sin2_theta12_CKM       -- 56/248 = 7/31
#check Observables.A_Wolf                 -- 83/99

-- Cosmology
#check Observables.Omega_DM_over_Omega_b  -- 43/8 (contains the 42!)
#check Observables.reduced_hubble         -- 167/248
#check Observables.sigma_8                -- 17/21
```

### The 42 Universality

The Euler characteristic χ(K₇) = 42 appears in two independent domains:

```lean
-- In particle physics: m_b/m_t = 1/42
theorem m_b_over_m_t_primary :
    (Core.b0 : ℚ) / Core.chi_K7 = 1 / 42 := ...

-- In cosmology: Ω_DM/Ω_b = (1 + 42)/8 = 43/8
theorem Omega_DM_primary :
    (Core.b0 + Core.chi_K7 : ℚ) / Core.rank_E8 = 43 / 8 := ...
```

---

## New in v3.2.10

### Tau Structural Derivation

The hierarchy parameter τ is now **derived** from framework invariants:

```python
from gift_core import TAU, DIM_E8xE8, B2, DIM_J3O, H_STAR

# τ = dim(E₈×E₈) × b₂ / (dim(J₃(𝕆)) × H*)
#   = 496 × 21 / (27 × 99) = 3472/891
tau_num = DIM_E8xE8 * B2      # 496 × 21 = 10416
tau_den = DIM_J3O * H_STAR    # 27 × 99 = 2673
# Reduced: 10416/2673 = 3472/891

print(float(TAU))  # 3.8967...
```

### E-Series Jordan Algebra

The Jordan algebra dimension **emerges** from the E-series:

```python
from gift_core import (
    DIM_E8, DIM_E6, DIM_SU3, DIM_J3O,
    E_SERIES_DIFF, J3O_FROM_E_SERIES
)

# dim(J₃(𝕆)) = (dim(E₈) - dim(E₆) - dim(SU₃)) / 6
#            = (248 - 78 - 8) / 6 = 162 / 6 = 27
print(E_SERIES_DIFF)       # 162
print(J3O_FROM_E_SERIES)   # 27
assert J3O_FROM_E_SERIES == DIM_J3O
```

### Numerical Observations

Approximate relations with computed deviations:

```python
from gift_core import verify_numerical_observations, get_numerical_summary

# Get all observations
obs = verify_numerical_observations()
print(obs['tau_powers'])  # τ², τ³, τ⁴, τ⁵ bounds

# Summary with deviations
summary = get_numerical_summary()
print(summary['tau^5'])
# {'computed': 898.48, 'target': 900, 'deviation_percent': 0.17, ...}

# Key observations:
# - τ⁴ ≈ 231 = N_gen × b₃ (0.19% deviation)
# - τ⁵ ≈ 900 = h(E₈)² (0.17% deviation)
# - τ ≈ 8γ^(5π/12) (0.0045% deviation)
```

### Exceptional Ranks Sum

```python
from gift_core import (
    RANK_E8, RANK_E7, RANK_E6, RANK_F4, RANK_G2,
    EXCEPTIONAL_RANKS_SUM, DIM_J3O
)

# Sum of exceptional Lie algebra ranks = 27 = dim(J₃(𝕆))
print(RANK_E8 + RANK_E7 + RANK_E6 + RANK_F4 + RANK_G2)  # 8+7+6+4+2 = 27
assert EXCEPTIONAL_RANKS_SUM == DIM_J3O
```

---

## New in v3.2

### E8 Root System

The 240 roots of E8 as actual vectors in ℝ⁸:

```python
from gift_core.roots import (
    E8_ROOTS,           # All 240 roots
    D8_ROOTS,           # 112 integer roots (±eᵢ ± eⱼ)
    HALF_INTEGER_ROOTS, # 128 half-integer roots
    E8_SIMPLE_ROOTS,    # 8 simple roots (Bourbaki)
    E8_CARTAN_MATRIX,   # 8×8 Cartan matrix
)

# Root operations
from gift_core.roots import (
    inner_product,      # ⟨u, v⟩
    norm, norm_sq,      # ‖v‖, ‖v‖²
    weyl_reflection,    # Weyl reflection s_α(v)
    is_root,            # Check if vector is a root
    is_in_E8_lattice,   # Check lattice membership
    positive_roots,     # 120 positive roots
    highest_root,       # θ = 2α₁ + 3α₂ + ...
)

# Example: Simple roots (Bourbaki convention)
print(E8_SIMPLE_ROOTS[0])  # (1, -1, 0, 0, 0, 0, 0, 0) = α₁
print(E8_SIMPLE_ROOTS[7])  # (-0.5, -0.5, ...) = α₈

# Statistics
from gift_core.roots import root_statistics
stats = root_statistics()
print(stats)
# {'total_roots': 240, 'd8_roots': 112, 'half_integer_roots': 128,
#  'coxeter_number': 30, 'weyl_group_order': 696729600, ...}
```

### Fano Plane & G2 Cross Product

The Fano plane encodes octonion multiplication and G₂ structure:

```python
from gift_core.fano import (
    FANO_LINES,         # 7 lines, each with 3 points
    epsilon,            # Structure constants ε(i,j,k)
    cross_product,      # G2-invariant cross product in R^7
    phi0,               # Associative 3-form
)

# The 7 lines of the Fano plane
print(FANO_LINES)
# [(0,1,3), (1,2,4), (2,3,5), (3,4,6), (4,5,0), (5,6,1), (6,0,2)]

# Epsilon tensor: ε(i,j,k) = ±1 or 0
print(epsilon(0, 1, 3))  # +1 (cyclic order on line)
print(epsilon(1, 0, 3))  # -1 (antisymmetric)

# G2 cross product in R^7
u = (1, 0, 0, 0, 0, 0, 0)
v = (0, 1, 0, 0, 0, 0, 0)
w = cross_product(u, v)
print(w)  # Result in R^7

# Verify Lagrange identity: ‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩²
from gift_core.fano import verify_lagrange_identity
print(verify_lagrange_identity(u, v))  # True

# Octonion multiplication (imaginary units)
from gift_core.fano import octonion_multiply_imaginaries
sign, result = octonion_multiply_imaginaries(0, 1)  # e₁ * e₂
print(f"e₁ × e₂ = {'+' if sign > 0 else '-'}e{result+1}")  # +e₄
```

### Verification Module

Check all GIFT relations programmatically:

```python
from gift_core import verify, verify_all, verify_summary

# Quick check
assert verify()  # True if all pass

# Detailed results
results = verify_all()
for r in results:
    print(f"{r.name}: {'✓' if r.passed else '✗'}")

# Summary
summary = verify_summary()
print(f"Passed: {summary['passed']}/{summary['total']}")
print(f"By category: {summary['by_category']}")

# Pretty report
from gift_core import print_verification_report
print_verification_report()
```

### Visualization (requires matplotlib)

```python
from gift_core.visualize import (
    plot_fano,          # Fano plane diagram
    plot_e8_projection, # E8 roots 2D projection
    plot_dynkin_e8,     # E8 Dynkin diagram
    plot_gift_constants,# Bar chart of constants
)

# Fano plane
plot_fano(save_path='fano.png')

# E8 roots (requires numpy)
plot_e8_projection(projection='random', save_path='e8.png')

# Dynkin diagram
plot_dynkin_e8(save_path='dynkin.png')

# All visualizations
from gift_core.visualize import plot_all
plot_all(save_dir='./figures/')
```

## Basic Usage

```python
from gift_core import *

# Access any certified constant
print(SIN2_THETA_W)      # Fraction(3, 13)
print(TAU)               # Fraction(3472, 891)
print(KAPPA_T)           # Fraction(1, 61)
print(GAMMA_GIFT)        # Fraction(511, 884)
print(ALPHA_INV_BASE)    # 137
```

## Certified Constants

### Original Relations

| Constant | Value | Description |
|----------|-------|-------------|
| `SIN2_THETA_W` | 3/13 | Weinberg angle |
| `TAU` | 3472/891 | Hierarchy parameter |
| `KAPPA_T` | 1/61 | Torsion parameter |
| `DET_G` | 65/32 | Metric determinant |
| `Q_KOIDE` | 2/3 | Koide formula |
| `M_TAU_M_E` | 3477 | Tau/electron mass ratio |
| `M_S_M_D` | 20 | Strange/down mass ratio |
| `DELTA_CP` | 197 | CP violation phase (degrees) |
| `H_STAR` | 99 | Topological invariant |
| `P2` | 2 | Pontryagin class |
| `N_GEN` | 3 | Number of generations |

### Topological Extension

| Constant | Value | Description |
|----------|-------|-------------|
| `GAMMA_GIFT` | 511/884 | GIFT parameter |
| `THETA_23` | 85/99 | Neutrino mixing angle |
| `ALPHA_INV_BASE` | 137 | Fine structure constant inverse (base) |
| `OMEGA_DE_FRAC` | 98/99 | Dark energy fraction |

### Yukawa Duality

| Constant | Value | Description |
|----------|-------|-------------|
| `ALPHA_SUM_A` | 12 | Structure A sum (2+3+7) |
| `ALPHA_SUM_B` | 13 | Structure B sum (2+5+6) |
| `ALPHA_PROD_A` | 42 | Structure A product |
| `ALPHA_PROD_B` | 60 | Structure B product |
| `DUALITY_GAP` | 18 | Gap between structures |
| `VISIBLE_DIM` | 43 | Visible sector dimension |
| `HIDDEN_DIM` | 34 | Hidden sector dimension |

### Irrational Sector

| Constant | Value | Description |
|----------|-------|-------------|
| `ALPHA_INV_COMPLETE` | 267489/1952 | Complete alpha inverse (~137.033) |
| `THETA_13_DEGREES_SIMPLIFIED` | 60/7 | Theta_13 in degrees (~8.57) |
| `PHI_LOWER_BOUND` | 1618/1000 | Golden ratio lower bound |
| `M_MU_M_E_LOWER` | 206 | Muon/electron mass ratio bound |

### Exceptional Groups

| Constant | Value | Description |
|----------|-------|-------------|
| `DIM_F4` | 52 | Dimension of F4 |
| `DELTA_PENTA` | 25 | Pentagonal structure (Weyl^2) |
| `WEYL_E8_ORDER` | 696729600 | Order of Weyl(E8) |

### Mass Factorization

| Constant | Value | Description |
|----------|-------|-------------|
| `MASS_FACTORIZATION` | 3477 | 3 x 19 x 61 (tau/electron mass ratio) |
| `PRIME_8` | 19 | 8th prime (Von Staudt-Clausen) |
| `T61_DIM` | 61 | Torsion configuration space |
| `W_SUM` | 49 | G2 torsion classes (1+7+14+27) |
| `T61_RESIDUE` | 12 | Gauge residue (dim(G2) - p2) |
| `IMPEDANCE` | 9 | H*/D_bulk |

### Sequence Embeddings

```python
from gift_core.sequences import fib, lucas, FIBONACCI_GIFT, LUCAS_GIFT

# Fibonacci embedding: F_3...F_12 are GIFT constants
print(fib(8))   # 21 = b2
print(fib(9))   # 34 = hidden_dim
print(fib(12))  # 144 = (dim_G2 - p2)^2

# Lucas embedding
print(lucas(6))  # 18 = duality_gap
print(lucas(8))  # 47 = Monster factor

# View all embeddings
for n, (val, name) in FIBONACCI_GIFT.items():
    print(f"F_{n} = {val} = {name}")
```

### Joyce Existence Theorem

```python
from gift_core.analysis import JoyceCertificate, verify_pinn_bounds

# Quick verification
assert verify_pinn_bounds()  # K7 admits torsion-free G2!

# Detailed certificate
cert = JoyceCertificate.verify()
print(cert)
# JoyceCertificate:
#   Torsion < threshold: True
#   Safety margin: 20.4x
#   Contraction K < 1: True
#   det(g) = 65/32: True
#   Status: VALID

# Check individual conditions
print(cert.torsion_below_threshold)  # True
print(float(cert.safety_margin))     # ~20.4
```

### Interval Arithmetic

```python
from gift_core.analysis import (
    Interval, TORSION_BOUND, JOYCE_THRESHOLD,
    DET_G_BOUND, DET_G_TARGET
)

# PINN torsion bound: [0.00139, 0.00141]
print(TORSION_BOUND)  # [0.001390, 0.001410]

# Joyce threshold: 0.0288
print(JOYCE_THRESHOLD.lo)  # 0.0288

# Verify bound is below threshold
print(TORSION_BOUND.hi < JOYCE_THRESHOLD.lo)  # True

# det(g) verification
print(DET_G_BOUND.contains(DET_G_TARGET))  # True
```

## TCS Construction (v3.2+)

K₇ Betti numbers are now **derived** from Twisted Connected Sum building blocks:

```python
from gift_core import *

# TCS Building Blocks (v3.2)
# M₁ = Quintic hypersurface in CP⁴
M1_B2 = 11  # b₂(M₁)
M1_B3 = 40  # b₃(M₁)

# M₂ = Complete Intersection (2,2,2) in CP⁶
M2_B2 = 10  # b₂(M₂)
M2_B3 = 37  # b₃(M₂)

# K₇ = M₁ #_TCS M₂ (Twisted Connected Sum)
B2 = M1_B2 + M2_B2  # 11 + 10 = 21 ✓
B3 = M1_B3 + M2_B3  # 40 + 37 = 77 ✓

# Both Betti numbers DERIVED from building blocks!
H_STAR = B2 + B3 + 1  # 99
```

### Structural Identities (v3.2)

```python
# Weyl Triple Identity: 3 independent paths to Weyl = 5
assert (DIM_G2 + 1) // N_GEN == WEYL_FACTOR      # 15 / 3 = 5
assert B2 // N_GEN - P2 == WEYL_FACTOR           # 21 / 3 - 2 = 5
assert DIM_G2 - RANK_E8 - 1 == WEYL_FACTOR       # 14 - 8 - 1 = 5

# PSL(2,7) = 168: Fano plane symmetry group
PSL27_ORDER = 168
assert (B3 + DIM_G2) + B3 == PSL27_ORDER         # 91 + 77 = 168
assert RANK_E8 * B2 == PSL27_ORDER               # 8 × 21 = 168
assert N_GEN * (B3 - B2) == PSL27_ORDER          # 3 × 56 = 168
```

## Algebraic Foundations (v3.1+)

GIFT constants are now **derived** from octonion algebraic structure:

```python
from gift_core import *

# The derivation chain: ℍ → 𝕆 → G₂ → GIFT

# Octonions have 7 imaginary units
IMAGINARY_COUNT = 7

# G₂ = Aut(𝕆) has dimension 2 × 7 = 14
DIM_G2 = 14  # = 2 * IMAGINARY_COUNT

# b₂ = C(7,2) = 21 (pairs of imaginary units)
B2 = 21  # = choose(7, 2)

# fund(E₇) = 2 × b₂ + dim(G₂) = 56
FUND_E7 = 56

# b₃ = b₂ + fund(E₇) = 77
B3 = 77  # = 21 + 56

# H* = b₂ + b₃ + 1 = 99
H_STAR = 99

# Physical predictions from the algebraic chain:
# sin²θ_W = 21/91 = 3/13  (b₂ / (b₃ + dim_G2))
# Q_Koide = 14/21 = 2/3   (dim_G2 / b₂)
# N_gen = 3               (from K₄ matchings, E₇ structure)
```

### Key Insight

Previous versions defined constants arbitrarily:
```python
DIM_E8 = 248  # Just a number
```

v3.1+ **derives** them from octonion structure:
```
𝕆 has 7 imaginary units
  → G₂ = Aut(𝕆) has dim = 2×7 = 14
  → b₂ = C(7,2) = 21
  → fund(E₇) = 56
  → b₃ = 77
  → Physical predictions follow
```

## Topological Constants

These are the fundamental constants from which relations are derived:

```python
from gift_core import *

print(DIM_E8)      # 248 - Dimension of E8
print(RANK_E8)     # 8   - Rank of E8
print(DIM_G2)      # 14  - Dimension of G2
print(DIM_K7)      # 7   - Dimension of K7 manifold
print(B2)          # 21  - Second Betti number
print(B3)          # 77  - Third Betti number
print(DIM_J3O)     # 27  - Jordan algebra dimension
print(WEYL_FACTOR) # 5   - Weyl factor
print(D_BULK)      # 11  - M-theory dimension
```

## K7 Metric Pipeline

Build G2 holonomy metrics on K7 manifolds (requires numpy):

```python
import gift_core as gc

if gc.NUMPY_AVAILABLE:
    # Configure pipeline
    config = gc.PipelineConfig(
        neck_length=15.0,      # TCS gluing parameter
        resolution=32,         # Grid resolution
        pinn_epochs=1000,      # Neural network training
        use_pinn=True          # Enable physics-informed learning
    )

    # Run computation
    result = gc.run_pipeline(config)

    # Access results
    print(f"det(g) = {result.det_g}")
    print(f"kappa_T = {result.kappa_T}")
    print(f"b2 = {result.betti[2]}")
    print(f"b3 = {result.betti[3]}")

    # Export to proof assistant
    lean_proof = result.certificate.to_lean()

    # Physics extraction
    yukawa = gc.YukawaTensor(result.harmonic_forms)
    masses = yukawa.fermion_masses()
```

### Pipeline Modules

| Module | Purpose |
|--------|---------|
| `geometry/` | K3, CY3, TCS manifold construction |
| `g2/` | G2 3-form, holonomy, torsion constraints |
| `harmonic/` | Hodge Laplacian, harmonic forms, Betti validation |
| `nn/` | Physics-informed neural networks |
| `physics/` | Yukawa tensors, mass spectrum, gauge couplings |
| `verification/` | Interval arithmetic, certificate generation |

## Relation Object

Each relation is a `CertifiedRelation` object:

```python
from gift_core import PROVEN_RELATIONS

r = PROVEN_RELATIONS[0]
print(r.symbol)      # Human-readable symbol
print(r.value)       # Exact value (Fraction or int)
print(r.derivation)  # How it's derived
print(r.lean_theorem)  # Lean 4 theorem name
```

## Lean 4 Usage (v3.1+)

### GIFT.Core - Single Source of Truth

As of v3.1, use `GIFT.Core` for all GIFT constants:

```lean
import GIFT.Core
open GIFT.Core

-- All constants are available
#check b2        -- 21
#check b3        -- 77
#check H_star    -- 99
#check dim_E8    -- 248
#check dim_G2    -- 14
```

### Migration from Legacy Modules

If you have code using `GIFT.Algebra`, `GIFT.Topology`, or `GIFT.Geometry`:

**Before:**
```lean
import GIFT.Algebra
import GIFT.Topology
import GIFT.Geometry
open GIFT.Algebra GIFT.Topology GIFT.Geometry
```

**After:**
```lean
import GIFT.Core
open GIFT.Core
```

The legacy modules still work (they re-export from Core), but new code should use Core directly.

### Constant Derivation Hierarchy

Constants are derived from octonion structure:

```
GIFT.Algebraic.Octonions
  └─ imaginary_count = 7

GIFT.Algebraic.G2
  └─ dim_G2 = 2 × imaginary_count = 14

GIFT.Algebraic.BettiNumbers
  ├─ b2 = C(7,2) = 21
  ├─ fund_E7 = 2 × b2 + dim_G2 = 56
  ├─ b3 = b2 + fund_E7 = 77
  └─ H_star = b2 + b3 + 1 = 99

GIFT.Core
  ├─ Re-exports from Algebraic modules
  └─ Defines remaining constants (dim_E8, dim_K7, etc.)
```

### Available Constants in GIFT.Core

| Category | Constants |
|----------|-----------|
| **Octonion-derived** | `imaginary_count`, `dim_G2`, `rank_G2`, `b2`, `b3`, `H_star`, `fund_E7` |
| **Exceptional Lie** | `dim_E8`, `rank_E8`, `dim_E8xE8`, `dim_E7`, `dim_E6`, `dim_F4` |
| **Geometry** | `dim_K7`, `dim_J3O`, `D_bulk` |
| **Topology** | `p2`, `det_g_num`, `det_g_den`, `kappa_T_den` |
| **Weyl Group** | `Weyl_factor`, `Weyl_sq`, `weyl_E8_order` |
| **Standard Model** | `dim_SU3`, `dim_SU2`, `dim_U1`, `dim_SM_gauge` |
| **Primes** | `prime_6`, `prime_8`, `prime_11` |

## Blueprint Documentation

GIFT includes a LaTeX blueprint that generates an interactive dependency graph showing proof structure.

### Viewing the Blueprint

The blueprint is hosted at the project's GitHub Pages (if enabled), or can be built locally:

```bash
cd blueprint
pip install leanblueprint
leanblueprint build
# Open _build/html/index.html
```

### Blueprint Structure

The dependency graph shows how theorems and definitions connect:

| Chapter | Contents |
|---------|----------|
| **E8 Lattice** | AllInteger, SumEven, E8_lattice, reflect_preserves_lattice |
| **G2 Cross Product** | Fano plane, epsilon tensor, Lagrange identity |
| **Algebraic Foundations** | Octonions, G2, Betti numbers, H* |
| **SO(16) Decomposition** | dim_SO, spinor, geometric/spinorial parts |
| **Physical Relations** | Weinberg angle, Koide, fine structure, lepton masses |
| **Sequences** | Fibonacci F₃-F₁₂, Lucas L₀-L₉ embeddings |
| **Prime Atlas** | Direct prime expressions, Heegner numbers |
| **Moonshine** | Monster dimension, j-invariant |
| **McKay** | Coxeter number, binary icosahedral, E8 kissing |
| **Joyce Theorem** | PINN verification, torsion bounds, existence |
| **Explicit G2 Metric** | phi0, scale factor, torsion-free proof |

### Key Dependencies

The central hub is `def:H_star` (H* = b₂ + b₃ + 1 = 99), which connects to:
- Physical relations (mass ratios, coupling constants)
- Topological invariants (Betti numbers)
- Cosmological parameters (Ω_DE)

Other important hubs:
- `def:b2`, `def:b3` → Algebraic chain from octonions
- `def:fib`, `def:lucas` → Sequence embeddings
- `def:coxeter` → McKay correspondence
- `def:monster_dim` → Moonshine connections

## Version History

See [CHANGELOG.md](../CHANGELOG.md) for detailed version history.
