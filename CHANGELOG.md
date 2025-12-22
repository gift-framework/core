# Changelog

All notable changes to GIFT Core will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [3.1.8] - 2025-12-22

### Summary

**Axiom Reduction!** Eliminated 8 axioms by connecting to already-proven theorems in RootSystems.lean and G2CrossProduct.lean. Total axioms reduced from 52 to 44 (15% reduction).

### Changed

- **E8Lattice.lean**: Replaced 4 root counting axioms with proven theorems from RootSystems.lean
  - `D8_roots_card_enum` → `RootSystems.D8_card` (112 roots)
  - `HalfInt_roots_card_enum` → `RootSystems.HalfInt_card` (128 roots)
  - `E8_roots_decomposition_enum` → `RootSystems.E8_roots_decomposition`
  - `E8_roots_card_240` → `RootSystems.E8_enumeration_card` (240 total)

- **G2TensorForm.lean**: Replaced 4 cross product axioms with proven theorems from G2CrossProduct.lean
  - `G2_cross_bilinear_left` → `G2CrossProduct.cross_left_linear`
  - `G2_cross_antisymm'` → `G2CrossProduct.G2_cross_antisymm`
  - `G2_cross_lagrange` → `G2CrossProduct.G2_cross_norm`
  - `cross_matches_octonion_structure` → `G2CrossProduct.cross_is_octonion_structure`

### Fixed

- **Namespace conflicts**: Use qualified names to avoid ambiguous term errors
  - `RootSystems.AllInteger` vs `InnerProductSpace.AllInteger`
  - `G2CrossProduct.R7` vs `InnerProductSpace.R7`

### Documentation

- Updated `docs/AXIOM_AUDIT.md` with progress tracking (v3.1.8)
- Added namespace conflict guidelines to `CLAUDE.md`

---

## [3.1.7] - 2025-12-22

### Summary

**Blueprint Dependency Graph Consolidation!** Added ~40 `\uses{}` connections to eliminate isolated nodes, then cleaned up ~30 noisy connections for a high signal-to-noise dependency graph.

### Added

- **Missing `\uses{}` connections** to isolated blueprint nodes:
  - E8 Lattice: `AllInteger`, `SumEven`, `AllHalfInteger` → `R8`
  - Fibonacci: `fib_3_p2`, `fib_6_rank`, `fib_8_b2`, `fib_12_alpha` → `fib` + core defs
  - Lucas: `lucas_4_K7`, `lucas_5_bulk`, `b3_lucas` → `lucas`
  - j-Invariant: `j_E8`, `j_triality` → `j_constant`
  - McKay: `coxeter_gift`, `euler_p2`, `binary_icosahedral` → `coxeter`
  - Monster: `monster_ap`, `monster_factor`, `monster_gift` → `monster_dim` + core
  - Heegner: `heegner_163`, `heegner_all` → `heegner` + `b3`
  - Analytical Metric: `torsion_bound`, `margin_20x`, `target_interval` → interconnected

### Changed

- **Fixed duplicate label**: `\label{chap:analytical}` → renamed second to `\label{chap:explicit_metric}`

### Removed

- **~30 noisy `\uses{def:H_star}` connections** that didn't represent meaningful dependencies:
  - `def:dim_SO` (generic formula, doesn't use H*)
  - `def:spinor_SO16` (derives from imaginary_count, not H*)
  - Fibonacci/Lucas theorems (use `def:fib`/`def:lucas`, not H*)
  - Heegner, Monster, j-Invariant (use their own definitions)
  - McKay correspondence (uses coxeter, not H*)

### Technical Notes

**H* connections kept** (legitimate dependencies):
- `thm:m_tau_m_e`: Uses `10 × H*` in the mass ratio formula
- `thm:Omega_DE_fraction`: Uses `(H*-1)/H* = 98/99`
- `def:alpha_inv_bulk`: Uses `H*/D_bulk = 99/11 = 9`

**Dependency graph metrics:**
- Before consolidation: ~60 `\uses{}` tags, many isolated nodes
- After consolidation: 107 `\uses{}` tags
- After cleanup: 100 `\uses{}` tags (higher signal-to-noise)

---

## [3.1.6] - 2025-12-21

### Summary

**Dependency Graph Simplification!** Deduplicated constant definitions across the codebase and connected the Hierarchy module to Certificate.lean, significantly improving the blueprint dependency graph.

### Changed

- **Constant Deduplication**: Replaced independent `def` declarations with `abbrev` pointing to canonical sources:
  - `b2`, `b3`, `H_star` → `Algebraic.BettiNumbers` (canonical)
  - `dim_G2` → `Algebraic.G2` (canonical)
  - `dim_E8` → `Algebraic.G2` or `Core` (layer-appropriate)

- **Files Updated**:
  - `AnalyticalMetric.lean`: Uses BettiNumbers/G2 abbrevs
  - `G2Holonomy.lean`: Uses BettiNumbers/G2 abbrevs
  - `CayleyDickson.lean`: Uses G2.dim_G2
  - `GIFTConstants.lean`: Uses G2.dim_E8

### Added

- **Hierarchy → Certificate Connection**:
  - Import `GIFT.Hierarchy` in `Certificate.lean`
  - New theorem `gift_v33_hierarchy_certificate` with 7 relations
  - Abbrevs linking key hierarchy theorems to Certificate

### Technical Notes

**Pattern: `def` vs `abbrev` vs `theorem`**
- `def foo : ℕ := 27` → Value, can compare: `foo = 27`
- `abbrev foo : ℕ := Bar.foo` → Alias to canonical source
- `theorem foo : x = y := ...` → Prop, use equation directly (NOT `foo = 27`)

**Pattern: ℚ constants and `norm_num`**
- `norm_num` cannot simplify through coercions from ℕ to ℚ
- For ℚ proofs, use literal definitions with comments noting canonical source

**Dependency Graph Impact**:
- Before: ~15 isolated nodes defining same values independently
- After: Explicit import chains to canonical sources
- Hierarchy module (~20 nodes) now connected to main certification chain

---

## [3.1.5] - 2025-12-21

### Summary

**Dimensional Hierarchy Module!** Complete formalization of the electroweak hierarchy problem via GIFT constants. The master formula M_EW/M_Pl = exp(-H*/rank(E8)) × φ⁻⁵⁴ ≈ 10⁻¹⁷ emerges from topology.

### Added

- **GoldenRatioPowers.lean**: Golden ratio power formalization
  - `phi_inv_sq`: φ⁻² = 3 - φ (VEV scaling factor)
  - `phi_inv_54`: φ⁻⁵⁴ ~ 10⁻¹¹ (Jordan suppression exponent)
  - `jordan_power_phi`: 27^φ ≈ 206.77 (Jordan algebra-golden ratio connection)
  - Bounds: 206 < 27^φ < 208

- **Hierarchy Module** (`GIFT.Hierarchy`):
  - **DimensionalGap.lean**: Master hierarchy formula
    - `cohom_suppression`: exp(-H*/rank(E8)) = exp(-99/8) ~ 4.2 × 10⁻⁶
    - `jordan_suppression`: φ⁻⁵⁴ = (φ⁻²)^27 ~ 10⁻¹¹
    - `hierarchy_ratio`: Combined ~ 10⁻¹⁷ (electroweak scale!)
    - `ln_hierarchy`: -H*/8 - 54 ln(φ) ≈ -38.4
  - **VacuumStructure.lean**: 21 vacuum structure
    - `n_vacua = b2 = 21` (second Betti number)
    - `vev_scaling = phi_inv_sq` (VEV at each vacuum)
    - `chi_K7 = 0` (K7 Euler characteristic)
  - **E6Cascade.lean**: E8 → E6 → SM symmetry breaking
    - `dim_E6 = 78`, `rank_E6 = 6`
    - Cascade dimensions: (248, 78, 45, 24, 12)
    - Difference sequence: (170, 33, 21, 12)
  - **AbsoluteMasses.lean**: Mass ratio formulas
    - `tau_electron_ratio = 3477` (m_τ/m_e)
    - Numerology: 3477 = 3 × 19 × 61

### Technical Notes

**Why φ⁻⁵⁴?**
- Jordan algebra: dim(J₃(𝕆)) = 27
- VEV scaling: φ⁻² per vacuum level
- Total: (φ⁻²)^27 = φ⁻⁵⁴

**Why H*/8?**
- H* = b₂ + b₃ + 1 = 99 (cohomological dimension)
- rank(E8) = 8
- Ratio appears in exponential suppression

**Hierarchy decomposition:**
```
ln(M_EW/M_Pl) = -H*/rank - 54 ln(φ)
              = -99/8 - 54 × 0.481
              = -12.375 - 26.0
              ≈ -38.4
```
This gives M_EW/M_Pl ≈ exp(-38.4) ≈ 2 × 10⁻¹⁷ ✓

---

## [3.1.4] - 2025-12-17

### Summary

**Analytical G₂ Metric Discovery!** The standard G₂ form φ₀ scaled by c = (65/32)^{1/14} is the EXACT closed-form solution. No PINN training needed!

### Added

- **AnalyticalMetric.lean**: Complete closed-form G₂ metric formalization
  - `phi0_indices`: Standard associative 3-form indices [(0,1,2), (0,3,4), ...]
  - `phi0_signs`: Sign pattern [+1, +1, +1, +1, -1, -1, -1]
  - `scale_factor_power_14`: c¹⁴ = 65/32 scaling derivation
  - `det_g_target`: det(g) = 65/32 exactly
  - `torsion_norm_constant_form`: ||T|| = 0 (constant form has zero torsion)
  - `canonical_metric`: Complete AnalyticalG2Metric structure

### Key Discovery

The metric is simply: **g = (65/32)^{1/7} × I₇**

```
φ(x) = c × φ₀  where c = (65/32)^{1/14} ≈ 1.0543

g_ij = { (65/32)^{1/7} ≈ 1.1115  if i = j
       { 0                       if i ≠ j
```

**Properties:**
- det(g) = 65/32 = 2.03125 EXACTLY
- ||T|| = 0 < 0.0288 (Joyce threshold) with INFINITE margin
- Hol(g) = G₂ by construction
- Only 7/35 = 20% of φ components non-zero

### Technical Notes

**Why zero torsion?** For a CONSTANT 3-form φ(x) = φ₀:
- d(φ) = 0 (exterior derivative of constant)
- d(*φ) = 0 (same reasoning)
- T is determined by d(φ) and d(*φ), so T = 0

This is the SIMPLEST non-trivial G₂ structure on ℝ⁷ satisfying GIFT constraints!

---

## [3.1.3] - 2025-12-16

### Summary

**Lagrange Identity for 7D Cross Product PROVEN!** The identity `‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩²` is now a theorem, not an axiom.

### Added

- **G2CrossProduct.lean**: Complete Lagrange identity proof
  - `R7_norm_sq_eq_sum`: ‖v‖² = ∑ᵢ vᵢ² - THEOREM (via Mathlib PiLp)
  - `R7_inner_eq_sum`: ⟨u,v⟩ = ∑ᵢ uᵢvᵢ - THEOREM (via Mathlib PiLp)
  - `G2_cross_norm`: **THEOREM** (was axiom) - Full Lagrange identity proof

### Changed

- **Lagrange Identity Status**: AXIOM → THEOREM
  - 130+ lines of sum manipulation proof
  - Uses `Finset.sum_eq_single` for Kronecker delta evaluation
  - Uses `psi_contract_vanishes` for coassociative 4-form cancellation

### Technical Notes

**Lagrange Identity Proof Structure:**

```
‖u × v‖² = ∑ₖ (∑ᵢⱼ εᵢⱼₖ uᵢ vⱼ)²
         = ∑ᵢⱼₗₘ (∑ₖ εᵢⱼₖ εₗₘₖ) uᵢ vⱼ uₗ vₘ
         = ∑ᵢⱼₗₘ (δᵢₗδⱼₘ - δᵢₘδⱼₗ + ψᵢⱼₗₘ) uᵢ vⱼ uₗ vₘ
         = ‖u‖²‖v‖² - ⟨u,v⟩² + 0   (ψ vanishes by antisymmetry)
```

**Key Lemmas Used:**
- `psi_antisym_il`: ψ(i,j,l,m) = -ψ(l,j,i,m) for all 2401 cases
- `psi_contract_vanishes`: Antisymmetric ψ × symmetric uᵢuₗ = 0
- `epsilon_contraction_decomp`: ∑ₖ εᵢⱼₖεₗₘₖ = Kronecker + ψ

### Verification Status

**G₂ Cross Product Properties: 9/10**
- `G2_cross_norm` (Lagrange identity) - **THEOREM** (was axiom)
- `cross_is_octonion_structure` - Exhaustive check times out (343 cases)

---

## [3.1.2] - 2025-12-16

### Summary

Lagrange identity infrastructure: **All key algebraic lemmas proven** for the 7D cross product norm identity. The coassociative 4-form approach provides a rigorous mathematical foundation.

### Added

- **G2CrossProduct.lean**: Lagrange identity proof infrastructure
  - `psi`: Coassociative 4-form ψ (deviation from 3D Kronecker formula)
  - `psi_antisym_il`: ψ(i,j,l,m) = -ψ(l,j,i,m) - THEOREM (7⁴ = 2401 cases via native_decide)
  - `epsilon_contraction_decomp`: ∑ₖ ε(i,j,k)ε(l,m,k) = Kronecker + ψ - THEOREM
  - `kronecker_part`: Definition of δᵢₗδⱼₘ - δᵢₘδⱼₗ
  - `antisym_sym_contract_vanishes`: Generic lemma for antisymmetric × symmetric = 0 - THEOREM
  - `psi_contract_vanishes`: ψ terms vanish under symmetric uᵢuₗvⱼvₘ contraction - THEOREM

### Changed

- **E8Lattice.lean**: Removed no-op `push_cast` linter warnings (lines 501, 534, 564)

### Technical Notes

**Lagrange Identity Proof Strategy (Harvey & Lawson, "Calibrated Geometries"):**

The 7D epsilon contraction differs from 3D:
```
∑ₖ ε(i,j,k)ε(l,m,k) = δᵢₗδⱼₘ - δᵢₘδⱼₗ + ψᵢⱼₗₘ
```

Key insight: ψ is antisymmetric under i↔l, but uᵢuₗ is symmetric. Therefore:
```
∑ᵢₗ ψᵢⱼₗₘ · uᵢuₗ = 0  (antisym × sym vanishes)
```

The Kronecker terms give exactly ‖u‖²‖v‖² - ⟨u,v⟩², proving the Lagrange identity.

**Status:** All algebraic lemmas proven. Final theorem kept as axiom pending EuclideanSpace norm expansion (Mathlib plumbing).

### Verification Status

**G₂ Cross Product Properties: 8/10 + infrastructure**
- Lagrange identity: Key lemmas PROVEN (5 theorems), final assembly pending Mathlib integration
- `cross_is_octonion_structure`: Exhaustive check times out

---

## [3.1.1] - 2025-12-16

### Summary

Axiom resolution patch: **All 9 helper axioms converted to theorems**, plus Weyl reflection and lattice closure properties proven.

### Changed

- **E8Lattice.lean**: Complete axiom elimination
  - `sq_mod_two_eq_self_mod_two`: n² = n (mod 2) - THEOREM via case analysis
  - `sum_sq_mod_two`: ∑(nᵢ²) = ∑(nᵢ) (mod 2) - THEOREM via divisibility
  - `inner_int_of_both_int`: inner product of integer vectors - THEOREM
  - `inner_int_of_both_half_int`: inner product of half-integer vectors - THEOREM
  - `inner_int_of_int_half`: mixed inner product - THEOREM
  - `norm_sq_even_of_int_even_sum`: norm squared of integer vectors - THEOREM
  - `norm_sq_even_of_half_int_even_sum`: norm squared of half-integer vectors - THEOREM
  - `E8_smul_int_closed`: E₈ lattice closed under ℤ-scaling - THEOREM
  - `E8_sub_closed`: E₈ lattice closed under subtraction - THEOREM

- **`reflect_preserves_lattice`**: Now a THEOREM (Weyl reflection preserves E₈ lattice)

### Verification Status

**E₈ Root System: 12/12 COMPLETE** - No changes

**G₂ Cross Product Properties: 8/10** (was 6/10)
- Proven: `epsilon_antisymm`, `epsilon_diag`, `reflect_preserves_lattice`, `G2_cross_bilinear`, `G2_cross_antisymm`, `cross_self`, epsilon_contraction lemmas
- Axioms: Lagrange 7D identity, octonion structure (timeout)

**Helper Lemmas: 9/9 COMPLETE** (was 7 axioms)
- All number theory and lattice closure facts now proven

### Technical Notes

Key proof techniques for cast handling:
- `push_cast; ring` for coordinate calculations with ℤ to ℝ casts
- `linarith` for linear arithmetic avoiding pattern matching issues
- `convert hgoal using 1; push_cast; ring` for cast difference resolution

---

## [3.1.0] - 2025-12-15

### Summary

Consolidation release focusing on mathematical foundations and formal verification.

### Added

- **Mathematical Foundations** (`GIFT.Foundations`):
  - `RootSystems.lean`: Rigorous E₈ root enumeration (240 = 112 + 128)
  - `E8Lattice.lean`: EuclideanSpace formalization with Mathlib
  - `E8Mathlib.lean`: Connection to Mathlib's CoxeterMatrix.E8
  - `G2CrossProduct.lean`: 7D cross product from Fano plane
  - `RationalConstants.lean`: GIFT ratios as proper ℚ arithmetic
  - `GraphTheory.lean`: K₄, K₇ via Mathlib SimpleGraph
  - `GoldenRatio.lean`: φ from Fibonacci, Binet formula

- **Algebraic Derivation Chain** (`GIFT.Algebraic`):
  - `Octonions.lean`: 7 imaginary units, Fano plane
  - `G2.lean`: G₂ = Aut(𝕆), dim = 14
  - `BettiNumbers.lean`: b₂ = C(7,2) = 21, b₃ = 77, H* = 99
  - `GIFTConstants.lean`: Physical predictions from algebra

- **Core Module** (`GIFT.Core`): Single source of truth for all constants

### Verification Status

**E₈ Root System: 12/12 COMPLETE**
- Root enumeration (RootSystems.lean)
- Lattice properties via case analysis + helper lemmas
- Basis and inner product (Mathlib API)

**G₂ Cross Product Properties: 6/10**
- Proven: `epsilon_antisymm`, `epsilon_diag`, `G2_cross_bilinear`, `G2_cross_antisymm`, `cross_self`
- Axioms: `reflect_preserves_lattice`, Lagrange 7D, octonion structure, `E8_smul_int_closed`

**Helper Lemmas**: 7 standard number theory facts

### Changed

- Version consolidated from iterative development to 3.1.0
- 175+ certified relations maintained

---

## [3.0.0] - 2025-12-09

### Added

- **Joyce Existence Theorem**: K7 admits torsion-free G2 structure
- **Sobolev Spaces**: H^k formalization with embeddings
- **Differential Forms**: Exterior calculus with Hodge star
- **Interval Arithmetic**: PINN certificate bounds
- **Python Analysis**: `gift_core.analysis` module

---

## [2.0.0] - 2025-12-09

### Added

- **Sequence Embeddings**: Fibonacci F₃-F₁₂, Lucas L₀-L₉
- **Prime Atlas**: 100% coverage of primes < 200
- **Monster Group**: 196883 = 47 × 59 × 71
- **McKay Correspondence**: E8 ↔ Binary Icosahedral

### Changed

- Total relations: 75 → 165+

---

## [1.0.0] - 2025-12-01

### Added

- Initial release with 13 original certified relations
- Lean 4 and Coq formal proofs
- Python package `giftpy`
