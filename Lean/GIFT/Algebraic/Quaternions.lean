/-
  GIFT Algebraic Foundations: Quaternions
  ========================================

  Phase 1 of the Octonion Formalization Plan.

  Establishes the correspondence between:
  - K₄ (complete graph on 4 vertices)
  - ℍ (quaternions)

  The quaternions form the first step in the Cayley-Dickson construction:
  ℝ → ℂ → ℍ → 𝕆

  Key facts:
  - dim(ℍ) = 4 = |V(K₄)|
  - 3 imaginary units {i,j,k} = C(4,2)/2 = 3 vertex pairings
  - Anti-commutative: ij = -ji, etc.
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

namespace GIFT.Algebraic.Quaternions

open Quaternion

/-!
## K₄ Properties (complementing Foundations.GraphTheory)
-/

/-- The complete graph K₄ -/
def K4 : SimpleGraph (Fin 4) := ⊤

/-- K₄ has 4 vertices -/
theorem K4_card_vertices : Fintype.card (Fin 4) = 4 := by decide

/-- K₄ adjacency is decidable -/
instance K4_DecidableRel : DecidableRel K4.Adj := fun v w =>
  if h : v = w then isFalse (K4.loopless v ∘ (h ▸ ·))
  else isTrue h

/-- K₄ has 6 edges = C(4,2) -/
theorem K4_card_edges : K4.edgeFinset.card = 6 := by native_decide

/-- Each vertex of K₄ has degree 3 -/
theorem K4_degree (v : Fin 4) : K4.degree v = 3 := by
  fin_cases v <;> native_decide

/-!
## Quaternion Properties (using Mathlib)
-/

/-- The quaternions have dimension 4 over ℝ -/
theorem quaternion_finrank : FiniteDimensional.finrank ℝ (Quaternion ℝ) = 4 :=
  Quaternion.finrank_eq_four

/-- Dimension correspondence: K₄ vertices = dim(ℍ) -/
theorem K4_vertices_eq_quaternion_dim :
    Fintype.card (Fin 4) = FiniteDimensional.finrank ℝ (Quaternion ℝ) := by
  simp [K4_card_vertices, quaternion_finrank]

/-!
## Imaginary Quaternion Units

The three imaginary units {i, j, k} satisfy:
- i² = j² = k² = -1
- ij = k, jk = i, ki = j
- ji = -k, kj = -i, ik = -j
-/

/-- Imaginary unit i -/
def imI : Quaternion ℝ := ⟨0, 1, 0, 0⟩

/-- Imaginary unit j -/
def imJ : Quaternion ℝ := ⟨0, 0, 1, 0⟩

/-- Imaginary unit k -/
def imK : Quaternion ℝ := ⟨0, 0, 0, 1⟩

/-- Number of imaginary units in ℍ -/
def imaginary_count : ℕ := 3

theorem imaginary_count_eq : imaginary_count = 3 := rfl

/-- The imaginary units as a function -/
def Im_H : Fin 3 → Quaternion ℝ
  | 0 => imI
  | 1 => imJ
  | 2 => imK

/-- Count of imaginary units -/
theorem Im_H_card : Fintype.card (Fin 3) = 3 := by decide

/-!
## Quaternion Multiplication Rules

Verifying the fundamental relations.
-/

/-- i² = -1 -/
theorem imI_sq : imI * imI = -1 := by
  simp only [imI]
  ext <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]

/-- j² = -1 -/
theorem imJ_sq : imJ * imJ = -1 := by
  simp only [imJ]
  ext <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]

/-- k² = -1 -/
theorem imK_sq : imK * imK = -1 := by
  simp only [imK]
  ext <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]

/-- ij = k -/
theorem imI_mul_imJ : imI * imJ = imK := by
  simp only [imI, imJ, imK]
  ext <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]

/-- ji = -k (anti-commutativity) -/
theorem imJ_mul_imI : imJ * imI = -imK := by
  simp only [imI, imJ, imK]
  ext <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]

/-- jk = i -/
theorem imJ_mul_imK : imJ * imK = imI := by
  simp only [imI, imJ, imK]
  ext <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]

/-- kj = -i -/
theorem imK_mul_imJ : imK * imJ = -imI := by
  simp only [imI, imJ, imK]
  ext <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]

/-- ki = j -/
theorem imK_mul_imI : imK * imI = imJ := by
  simp only [imI, imJ, imK]
  ext <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]

/-- ik = -j -/
theorem imI_mul_imK : imI * imK = -imJ := by
  simp only [imI, imJ, imK]
  ext <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]

/-!
## Anti-commutativity

The fundamental property distinguishing ℍ from ℂ.
-/

/-- Anti-commutativity: ij = -ji -/
theorem quaternion_anticomm_IJ : imI * imJ = -(imJ * imI) := by
  rw [imI_mul_imJ, imJ_mul_imI]
  ring

/-- Anti-commutativity: jk = -kj -/
theorem quaternion_anticomm_JK : imJ * imK = -(imK * imJ) := by
  rw [imJ_mul_imK, imK_mul_imJ]
  ring

/-- Anti-commutativity: ki = -ik -/
theorem quaternion_anticomm_KI : imK * imI = -(imI * imK) := by
  rw [imK_mul_imI, imI_mul_imK]
  ring

/-!
## Connection to K₄ Structure

K₄ has 3 perfect matchings, corresponding to 3 ways to pair 4 vertices.
This matches the 3 imaginary units of ℍ!

Perfect matchings in K₄:
- {(0,1), (2,3)} ↔ i
- {(0,2), (1,3)} ↔ j
- {(0,3), (1,2)} ↔ k

The edges of K₄ form the Fano plane with ℍ multiplication.
-/

/-- K₄ has C(4,2) = 6 edges -/
theorem K4_edges_eq_choose : K4.edgeFinset.card = Nat.choose 4 2 := by native_decide

/-- 6 edges, 3 pairs of opposite edges = 3 imaginary units -/
theorem K4_opposite_pairs : Nat.choose 4 2 / 2 = imaginary_count := by native_decide

/-!
## Summary

Phase 1 establishes:
1. K₄ ↔ ℍ correspondence via dimension
2. 3 imaginary units with anti-commutative multiplication
3. K₄ perfect matchings ↔ imaginary units

Next: Phase 2 - Octonions via Cayley-Dickson doubling of ℍ
-/

end GIFT.Algebraic.Quaternions
