# Changelog

All notable changes to GIFT Core will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
