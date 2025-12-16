# Changelog

All notable changes to GIFT Core will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [3.1.1] - 2025-12-16

### Summary

Axiom resolution patch: **All 9 helper axioms converted to theorems**, plus B1 and lattice closure properties proven.

### Changed

- **E8Lattice.lean**: Complete axiom elimination
  - `sq_mod_two_eq_self_mod_two`: n^2 = n (mod 2) - THEOREM via case analysis
  - `sum_sq_mod_two`: sum(n_i^2) = sum(n_i) (mod 2) - THEOREM via divisibility
  - `inner_int_of_both_int`: inner product of integer vectors - THEOREM
  - `inner_int_of_both_half_int`: inner product of half-integer vectors - THEOREM
  - `inner_int_of_int_half`: mixed inner product - THEOREM
  - `norm_sq_even_of_int_even_sum`: norm squared of integer vectors - THEOREM
  - `norm_sq_even_of_half_int_even_sum`: norm squared of half-integer vectors - THEOREM
  - `E8_smul_int_closed`: E8 lattice closed under Z-scaling - THEOREM
  - `E8_sub_closed`: E8 lattice closed under subtraction - THEOREM

- **B1 (reflect_preserves_lattice)**: Now a THEOREM via A6 + lattice closure

### Axiom Resolution Status

**Tier 1 (E8 Root System): 12/12 COMPLETE** - No changes

**Tier 2 (G2 Cross Product): 8/10** (was 6/10)
- Proven: epsilon_antisymm, epsilon_diag, B1, B2, B3, B3', epsilon_contraction lemmas
- Axioms: B4 (Lagrange 7D identity), B5 (Fano structure - timeout)

**Helper Lemmas: 9/9 COMPLETE** (was 7 axioms)
- All number theory and lattice closure facts now proven

### Technical Notes

Key proof techniques for cast handling:
- `push_cast; ring` for coordinate calculations with Z to R casts
- `linarith` for linear arithmetic avoiding pattern matching issues
- `convert hgoal using 1; push_cast; ring` for cast difference resolution

---

## [3.1.0] - 2025-12-15

### Summary

Consolidation release focusing on mathematical foundations and axiom resolution.

### Added

- **Mathematical Foundations** (`GIFT.Foundations`):
  - `RootSystems.lean`: Rigorous E8 root enumeration (240 = 112 + 128)
  - `E8Lattice.lean`: EuclideanSpace formalization with Mathlib
  - `E8Mathlib.lean`: Connection to Mathlib's CoxeterMatrix.E8
  - `G2CrossProduct.lean`: 7D cross product from Fano plane
  - `RationalConstants.lean`: GIFT ratios as proper ℚ arithmetic
  - `GraphTheory.lean`: K4, K7 via Mathlib SimpleGraph
  - `GoldenRatio.lean`: phi from Fibonacci, Binet formula

- **Algebraic Derivation Chain** (`GIFT.Algebraic`):
  - `Octonions.lean`: 7 imaginary units, Fano plane
  - `G2.lean`: G2 = Aut(O), dim = 14
  - `BettiNumbers.lean`: b2 = C(7,2) = 21, b3 = 77, H* = 99
  - `GIFTConstants.lean`: Physical predictions from algebra

- **Core Module** (`GIFT.Core`): Single source of truth for all constants

### Axiom Resolution Status

**Tier 1 (E8 Root System): 12/12 COMPLETE**
- A1-A5: Root enumeration (RootSystems.lean)
- A6-A7: Lattice properties via case analysis + helper axioms
- A9-A12: Basis and inner product (Mathlib API)

**Tier 2 (G2 Cross Product): 6/10**
- Proven: epsilon_antisymm, epsilon_diag, B2 (bilinear), B3 (antisymm), B3' (self)
- Axioms: B1, B4 (Lagrange 7D), B5 (Fano structure), E8_smul_int_closed

**Helper Axioms**: 7 standard number theory facts

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
