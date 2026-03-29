/-
G₂ Seven-Form: Proving g2_subset_SO7 and g2_det_one
=====================================================

The seven-form contraction B(i,j) = ∑ε·φ₀·φ₀·φ₀ = 144·δᵢⱼ (native_decide) gives,
via the transformation law det(A)·(AᵀA) = I, both:
  - g2_subset_SO7: AᵀA = I (G₂ ⊆ SO(7))
  - g2_det_one: det(A) = 1

One axiom remains: g2_det_mul_gram (the 7-form transformation law).
This replaces the previous 2 axioms (g2_subset_SO7 + g2_det_one) with 1.

Mathematical proof of g2_det_mul_gram (not yet formalized):
  The 7-form B(i,j) is alternating multilinear in 7 basis vectors.
  By uniqueness of ∧⁷(ℝ⁷): B(v₀,...,v₆) = B(e₀,...,e₆)·det(M_v).
  Evaluating at v_k = Ae_k with isG2Matrix: det(A)·144·δ = 144·(AᵀA).
  Mathlib path: AlternatingMap.eq_smul_basis_det

References:
- Bryant, R.L. (1987). Metrics with exceptional holonomy. Ann. Math. 126:525-576.
- Harvey, R. & Lawson, H.B. (1982). Calibrated geometries. Acta Math.

Version: 1.0.0 (2026-03-29)
-/

import Mathlib
import GIFT.Algebraic.G2ThreeForm

namespace GIFT.Algebraic.G2Bform

open Finset BigOperators GIFT.Algebraic.G2ThreeForm Matrix

/-!
## The Seven-Form Contraction B(i,j)

B(i,j) = ∑_{a₀,a₁,a₂,a₃} φ₀(i,a₀,a₁)·φ₀(j,a₂,a₃)·pvZT(a₀,a₁,a₂,a₃)

where pvZT computes the "partial volume term": for 4 distinct indices, find the
remaining 3, evaluate φ₀ on them, and multiply by 6·sgn.
-/

/-- Sign of a 7-tuple. Returns 0 for non-permutations (repeated indices). -/
private def signOf7 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : Fin 7) : ℤ :=
  let v : Fin 7 → Fin 7 := ![a₀, a₁, a₂, a₃, a₄, a₅, a₆]
  ∏ p ∈ (univ.filter (fun p : Fin 7 × Fin 7 => p.1 < p.2)),
    if v p.2 > v p.1 then 1
    else if v p.1 > v p.2 then -1
    else 0

/-- Partial volume term: for 4 indices (a₀,a₁,a₂,a₃), find the complement
    {e,f,g} = {0,...,6}\{a₀,...,a₃}, compute 6·sgn(a₀,...,a₃,e,f,g)·φ₀(e,f,g). -/
private def pvZT (a₀ a₁ a₂ a₃ : Fin 7) : ℤ :=
  if a₀ = a₁ ∨ a₀ = a₂ ∨ a₀ = a₃ ∨ a₁ = a₂ ∨ a₁ = a₃ ∨ a₂ = a₃ then 0
  else
    let rem := ([0, 1, 2, 3, 4, 5, 6] : List (Fin 7)).filter
      (fun x => x ≠ a₀ ∧ x ≠ a₁ ∧ x ≠ a₂ ∧ x ≠ a₃)
    match rem with
    | [e, f, g] =>
      let phiVal := phi0_ordered e f g
      if phiVal = 0 then 0
      else 6 * signOf7 a₀ a₁ a₂ a₃ e f g * phiVal
    | _ => 0

/-- The seven-form contraction B(i,j) over ℤ.
    B(i,j) = ∑_{a₀,a₁,a₂,a₃} φ₀(i,a₀,a₁)·φ₀(j,a₂,a₃)·pvZT(a₀,a₁,a₂,a₃) -/
def BformZ (i j : Fin 7) : ℤ :=
  ∑ a₀ : Fin 7, ∑ a₁ : Fin 7, ∑ a₂ : Fin 7, ∑ a₃ : Fin 7,
    phi0Z i a₀ a₁ * phi0Z j a₂ a₃ * pvZT a₀ a₁ a₂ a₃

/-- **B = 144·δ**: The seven-form contraction equals 144 times the Kronecker delta.

Verified by `native_decide` (7⁶ = 117,649 ℤ products). -/
theorem BformZ_eq : ∀ i j : Fin 7,
    BformZ i j = 144 * if i = j then 1 else 0 := by native_decide

/-!
## The Key Axiom: Seven-Form Transformation Law

This is the ONLY axiom in this file. It states that the seven-form contraction,
when evaluated on A-transformed basis vectors, picks up a factor of det(A).
Equivalently: det(A)·(AᵀA) = I for G₂ matrices.

**Axiom Category: B (Standard result)** — follows from the uniqueness of
alternating n-forms in n dimensions (Mathlib: `AlternatingMap.eq_smul_basis_det`).

**Elimination path**: Construct BformZ as a Mathlib `AlternatingMap`, then apply
`AlternatingMap.eq_smul_basis_det` to equate B on A-columns with det(A)·B on e-columns.
-/

/-- **The seven-form transformation law**: det(A)·(AᵀA)ᵢⱼ = δᵢⱼ for G₂ matrices.

Mathematical proof:
1. B(i,j) = 144·δ_{ij} (BformZ_eq above)
2. The 7-form B is alternating multilinear in the basis vectors
3. By uniqueness (∧⁷ℝ⁷ is 1-dim): B(Ae₀,...,Ae₆) = det(A)·B(e₀,...,e₆)
4. Using isG2Matrix on each φ₀ factor: B(Ae₀,...,Ae₆) = B(e₀,...,e₆)·(AᵀA correction)
5. Equating: det(A)·(AᵀA)ᵢⱼ = δᵢⱼ -/
axiom g2_det_mul_gram {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : isG2Matrix A) :
    ∀ i j : Fin 7, A.det * (A.transpose * A) i j = if i = j then 1 else 0

/-- det(A) ≠ 0 for G₂ matrices. -/
theorem g2_det_ne_zero {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : isG2Matrix A) :
    A.det ≠ 0 := by
  intro h; have := g2_det_mul_gram hA 0 0; simp [h] at this

/-- det(A)⁹ = 1 for G₂ matrices. -/
theorem g2_det_pow9 {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : isG2Matrix A) :
    A.det ^ 9 = 1 := by
  have h : A.det • (A.transpose * A) = 1 := by
    ext i j; simp [Matrix.smul_apply, smul_eq_mul]; exact g2_det_mul_gram hA i j
  have h2 := congr_arg Matrix.det h
  simp [Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
        Fintype.card_fin] at h2
  nlinarith [h2]

/-- det(A) = 1 for G₂ matrices.

From det(A)⁹ = 1: since 9 is odd and det(A)⁹ > 0, we have det(A) > 0.
Then det(A) = 1 is the only positive real 9th root of unity. -/
theorem g2_det_eq_one {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : isG2Matrix A) :
    A.det = 1 := by
  have h9 := g2_det_pow9 hA
  have hne := g2_det_ne_zero hA
  -- det(A)^9 = 1 and det(A) ≠ 0
  -- det(A)^8 = (det(A)^4)^2 ≥ 0, so det(A)^9 = det(A) * det(A)^8 has same sign as det(A)
  -- Since det(A)^9 = 1 > 0, det(A) > 0
  have hpos : A.det > 0 := by nlinarith [sq_nonneg (A.det ^ 4)]
  -- Now: x > 0 and x^9 = 1 implies x = 1
  -- Proof: if x > 1 then x^9 > 1; if 0 < x < 1 then x^9 < 1
  nlinarith [sq_nonneg (A.det - 1), sq_nonneg (A.det ^ 2 - 1),
             sq_nonneg (A.det ^ 4 - 1), sq_nonneg (A.det * (A.det - 1)),
             sq_nonneg (A.det ^ 2 * (A.det - 1)),
             mul_pos hpos hpos]

/-- **G₂ ⊆ SO(7)**: AᵀA = I for G₂ matrices.

Proved from g2_det_mul_gram + g2_det_eq_one. -/
theorem g2_subset_SO7 {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : isG2Matrix A) :
    A.transpose * A = 1 := by
  ext i j
  have h := g2_det_mul_gram hA i j
  rw [g2_det_eq_one hA, one_mul] at h
  rw [h]; simp [Matrix.one_apply]

/-- **G₂ elements have determinant 1**. -/
theorem g2_det_one {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : isG2Matrix A) :
    A.det = 1 := g2_det_eq_one hA

end GIFT.Algebraic.G2Bform
