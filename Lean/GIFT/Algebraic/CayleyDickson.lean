/-
  GIFT Algebraic Foundations: Cayley-Dickson Construction
  =======================================================

  Phase 2b of the Octonion Formalization Plan.

  The Cayley-Dickson construction doubles algebras:
  ℝ (1) → ℂ (2) → ℍ (4) → 𝕆 (8) → 𝕊 (16) → ...

  Each doubling introduces:
  - Loss of a property (commutativity, associativity, etc.)
  - New imaginary units

  Key dimension sequence: 1, 2, 4, 8, 16, ...
  Key imaginary sequence: 0, 1, 3, 7, 15, ... = 2ⁿ - 1
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Ring.Nat
import GIFT.Algebraic.Quaternions
import GIFT.Algebraic.Octonions
import GIFT.Algebraic.G2

namespace GIFT.Algebraic.CayleyDickson

/-!
## Dimension Doubling

The Cayley-Dickson construction doubles dimension at each step.
-/

/-- Dimension of ℝ -/
def dim_R : ℕ := 1

/-- Dimension of ℂ -/
def dim_C : ℕ := 2

/-- Dimension of ℍ -/
def dim_H : ℕ := 4

/-- Dimension of 𝕆 -/
def dim_O : ℕ := 8

/-- Dimension sequence: 2ⁿ -/
def dim_seq (n : ℕ) : ℕ := 2^n

theorem dim_R_eq : dim_R = dim_seq 0 := rfl
theorem dim_C_eq : dim_C = dim_seq 1 := rfl
theorem dim_H_eq : dim_H = dim_seq 2 := rfl
theorem dim_O_eq : dim_O = dim_seq 3 := rfl

/-- Each step doubles dimension -/
theorem doubling (n : ℕ) : dim_seq (n + 1) = 2 * dim_seq n := by
  simp only [dim_seq, pow_succ, mul_comm]

/-!
## Imaginary Unit Counts

At each level n, there are 2ⁿ - 1 imaginary units.
-/

/-- Imaginary units at level n: 2ⁿ - 1 -/
def imaginary_seq (n : ℕ) : ℕ := 2^n - 1

/-- ℝ has 0 imaginary units -/
theorem imaginary_R : imaginary_seq 0 = 0 := rfl

/-- ℂ has 1 imaginary unit (i) -/
theorem imaginary_C : imaginary_seq 1 = 1 := rfl

/-- ℍ has 3 imaginary units (i, j, k) -/
theorem imaginary_H : imaginary_seq 2 = 3 := rfl

/-- 𝕆 has 7 imaginary units (e₁, ..., e₇) -/
theorem imaginary_O : imaginary_seq 3 = 7 := rfl

/-- Octonion imaginary count matches -/
theorem imaginary_O_eq : Octonions.imaginary_count = imaginary_seq 3 := rfl

/-!
## Properties Lost at Each Doubling

ℝ: ordered, commutative, associative, division algebra
ℂ: loses ordering
ℍ: loses commutativity
𝕆: loses associativity (but keeps alternativity)
𝕊: loses alternativity (sedenions have zero divisors!)
-/

/-- Level at which commutativity is lost -/
def lose_commutativity : ℕ := 2  -- ℍ

/-- Level at which associativity is lost -/
def lose_associativity : ℕ := 3  -- 𝕆

/-- Level at which division is lost -/
def lose_division : ℕ := 4  -- 𝕊 (sedenions)

/-!
## Embedding Structure

The Cayley-Dickson construction gives natural embeddings:
ℝ ↪ ℂ ↪ ℍ ↪ 𝕆
-/

/-- The 3 imaginary units of ℍ embed into the 7 of 𝕆 -/
theorem quaternion_imaginary_embed :
    Quaternions.imaginary_count ≤ Octonions.imaginary_count := by decide

/-- Specifically: 3 ≤ 7 with 4 new imaginary units added -/
theorem new_imaginary_in_octonions :
    Octonions.imaginary_count - Quaternions.imaginary_count = 4 := rfl

/-- The 4 new imaginary units equal dim(ℍ) -/
theorem doubling_adds_four :
    dim_H = Octonions.imaginary_count - Quaternions.imaginary_count := rfl

/-!
## Pairs Decomposition

A key formula relating quaternion and octonion pairs:
C(3,2) + C(4,2) + 3×4 = 21

This decomposes the 21 = C(7,2) pairs of octonion imaginaries.
-/

/-- C(3,2) = 3 : pairs within ℍ imaginaries -/
theorem pairs_in_H : Nat.choose 3 2 = 3 := by native_decide

/-- C(4,2) = 6 : pairs within new imaginaries -/
theorem pairs_in_new : Nat.choose 4 2 = 6 := by native_decide

/-- 3 × 4 = 12 : mixed pairs (one from ℍ, one new) -/
theorem mixed_pairs : 3 * 4 = 12 := rfl

/-- Total: 3 + 6 + 12 = 21 = b₂ -/
theorem pairs_decomposition :
    Nat.choose 3 2 + Nat.choose 4 2 + 3 * 4 = 21 := by native_decide

/-- This equals C(7,2) -/
theorem pairs_total :
    Nat.choose 3 2 + Nat.choose 4 2 + 3 * 4 = Nat.choose 7 2 := by native_decide

/-!
## Quaternion Subalgebras in 𝕆

Each pair (eᵢ, eⱼ) on a Fano line generates a copy of ℍ.
There are 7 such quaternionic subalgebras.
-/

/-- Number of quaternionic subalgebras in 𝕆 -/
def quaternion_subalgebras : ℕ := 7

theorem quaternion_subalgebras_eq : quaternion_subalgebras = Octonions.fano_lines := rfl

/-- Each subalgebra has 3 imaginaries -/
theorem subalgebra_imaginary_count : 3 = Quaternions.imaginary_count := rfl

/-!
## The Chain ℍ → 𝕆 → G₂

The automorphism groups shrink at each doubling:
- Aut(ℂ) = ℤ/2 (complex conjugation)
- Aut(ℍ) = SO(3) (rotations of imaginary part)
- Aut(𝕆) = G₂ (exceptional!)

Dimension of Aut:
- dim(Aut(ℂ)) = 0 (discrete)
- dim(Aut(ℍ)) = 3 = dim(SO(3))
- dim(Aut(𝕆)) = 14 = dim(G₂)
-/

/-- Dimension of SO(3) = Aut(ℍ) -/
def dim_SO3 : ℕ := 3

/-- Dimension of G₂ = Aut(𝕆) (from canonical source: Algebraic.G2) -/
abbrev dim_G2 : ℕ := G2.dim_G2

/-- Key relation: dim(G₂) = 2 × |Im(𝕆)| -/
theorem G2_from_imaginary : dim_G2 = 2 * Octonions.imaginary_count := rfl

/-!
## Summary

The Cayley-Dickson construction establishes:
1. 𝕆 = ℍ ⊕ ℍ·ℓ has dimension 8 = 2×4
2. 7 imaginary units = 3 + 4 (from ℍ plus new)
3. C(7,2) = 21 decomposes as 3 + 6 + 12
4. Aut(𝕆) = G₂ with dim = 14 = 2×7

This provides the algebraic foundation for deriving GIFT constants.
-/

end GIFT.Algebraic.CayleyDickson
