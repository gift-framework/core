/-
GIFT Geometry: Concrete Hodge Star Computation
===============================================

Explicit computation of the Hodge star operator ⋆ : Ω³ ↔ Ω⁴ on ℝ⁷
using complement indices and Levi-Civita signs.

## Key Results

1. `complement3to4`/`complement4to3`: Bijection between 3-tuple and 4-tuple indices
2. `sign3`/`sign4`: Levi-Civita signs for the Hodge star
3. `hodgeStar3to4`/`hodgeStar4to3`: Concrete coefficient transformations
4. `hodgeStar_involutive`: Proof that ⋆⋆ = +1 (in dimension 7)
5. `phi0_coeffs`/`psi0_coeffs`: Canonical G₂ forms with correct Hodge duality

Version: 3.3.4
-/

import GIFT.Geometry.DifferentialFormsR7
import Mathlib.Data.Finset.Basic

namespace GIFT.Geometry.HodgeStarCompute

open GIFT.Geometry.Exterior
open GIFT.Geometry.DifferentialFormsR7

/-!
## Part 1: Index Tables for 3-tuples and 4-tuples

The ordered k-tuples in {0,...,6} are indexed by Fin C(7,k).
For k=3 and k=4, this is Fin 35.
-/

/-- All ordered 3-tuples (i<j<k) in Fin 7, indexed 0-34 -/
def triples : Fin 35 → (Fin 7 × Fin 7 × Fin 7) := fun n =>
  match n.val with
  | 0 => (0, 1, 2) | 1 => (0, 1, 3) | 2 => (0, 1, 4) | 3 => (0, 1, 5) | 4 => (0, 1, 6)
  | 5 => (0, 2, 3) | 6 => (0, 2, 4) | 7 => (0, 2, 5) | 8 => (0, 2, 6) | 9 => (0, 3, 4)
  | 10 => (0, 3, 5) | 11 => (0, 3, 6) | 12 => (0, 4, 5) | 13 => (0, 4, 6) | 14 => (0, 5, 6)
  | 15 => (1, 2, 3) | 16 => (1, 2, 4) | 17 => (1, 2, 5) | 18 => (1, 2, 6) | 19 => (1, 3, 4)
  | 20 => (1, 3, 5) | 21 => (1, 3, 6) | 22 => (1, 4, 5) | 23 => (1, 4, 6) | 24 => (1, 5, 6)
  | 25 => (2, 3, 4) | 26 => (2, 3, 5) | 27 => (2, 3, 6) | 28 => (2, 4, 5) | 29 => (2, 4, 6)
  | 30 => (2, 5, 6) | 31 => (3, 4, 5) | 32 => (3, 4, 6) | 33 => (3, 5, 6) | 34 => (4, 5, 6)
  | _ => (0, 1, 2)

/-- All ordered 4-tuples (a<b<c<d) in Fin 7, indexed 0-34 -/
def quads : Fin 35 → (Fin 7 × Fin 7 × Fin 7 × Fin 7) := fun n =>
  match n.val with
  | 0 => (0, 1, 2, 3) | 1 => (0, 1, 2, 4) | 2 => (0, 1, 2, 5) | 3 => (0, 1, 2, 6)
  | 4 => (0, 1, 3, 4) | 5 => (0, 1, 3, 5) | 6 => (0, 1, 3, 6) | 7 => (0, 1, 4, 5)
  | 8 => (0, 1, 4, 6) | 9 => (0, 1, 5, 6) | 10 => (0, 2, 3, 4) | 11 => (0, 2, 3, 5)
  | 12 => (0, 2, 3, 6) | 13 => (0, 2, 4, 5) | 14 => (0, 2, 4, 6) | 15 => (0, 2, 5, 6)
  | 16 => (0, 3, 4, 5) | 17 => (0, 3, 4, 6) | 18 => (0, 3, 5, 6) | 19 => (0, 4, 5, 6)
  | 20 => (1, 2, 3, 4) | 21 => (1, 2, 3, 5) | 22 => (1, 2, 3, 6) | 23 => (1, 2, 4, 5)
  | 24 => (1, 2, 4, 6) | 25 => (1, 2, 5, 6) | 26 => (1, 3, 4, 5) | 27 => (1, 3, 4, 6)
  | 28 => (1, 3, 5, 6) | 29 => (1, 4, 5, 6) | 30 => (2, 3, 4, 5) | 31 => (2, 3, 4, 6)
  | 32 => (2, 3, 5, 6) | 33 => (2, 4, 5, 6) | 34 => (3, 4, 5, 6)
  | _ => (0, 1, 2, 3)

/-!
## Part 2: Complement Bijection

The complement of a 3-tuple is the unique 4-tuple consisting of the
remaining elements of {0,...,6}. This defines a bijection Fin 35 ↔ Fin 35.
-/

/-- Complement: 3-tuple index → 4-tuple index of complement set -/
def complement3to4 : Fin 35 → Fin 35 := fun n =>
  -- (i,j,k) ↦ {0,...,6} \ {i,j,k}
  ⟨match n.val with
  | 0 => 34 | 1 => 33 | 2 => 32 | 3 => 31 | 4 => 30
  | 5 => 29 | 6 => 28 | 7 => 27 | 8 => 26 | 9 => 25
  | 10 => 24 | 11 => 23 | 12 => 22 | 13 => 21 | 14 => 20
  | 15 => 19 | 16 => 18 | 17 => 17 | 18 => 16 | 19 => 15
  | 20 => 14 | 21 => 13 | 22 => 12 | 23 => 11 | 24 => 10
  | 25 => 9 | 26 => 8 | 27 => 7 | 28 => 6 | 29 => 5
  | 30 => 4 | 31 => 3 | 32 => 2 | 33 => 1 | 34 => 0
  | _ => 0, by fin_cases n <;> simp⟩

/-- Complement: 4-tuple index → 3-tuple index (inverse of above) -/
def complement4to3 : Fin 35 → Fin 35 := fun n =>
  ⟨match n.val with
  | 0 => 34 | 1 => 33 | 2 => 32 | 3 => 31 | 4 => 30
  | 5 => 29 | 6 => 28 | 7 => 27 | 8 => 26 | 9 => 25
  | 10 => 24 | 11 => 23 | 12 => 22 | 13 => 21 | 14 => 20
  | 15 => 19 | 16 => 18 | 17 => 17 | 18 => 16 | 19 => 15
  | 20 => 14 | 21 => 13 | 22 => 12 | 23 => 11 | 24 => 10
  | 25 => 9 | 26 => 8 | 27 => 7 | 28 => 6 | 29 => 5
  | 30 => 4 | 31 => 3 | 32 => 2 | 33 => 1 | 34 => 0
  | _ => 0, by fin_cases n <;> simp⟩

/-- complement3to4 and complement4to3 are inverses -/
theorem complement_invol_34 : ∀ n : Fin 35, complement4to3 (complement3to4 n) = n := by
  intro n; fin_cases n <;> rfl

theorem complement_invol_43 : ∀ n : Fin 35, complement3to4 (complement4to3 n) = n := by
  intro n; fin_cases n <;> rfl

/-!
## Part 3: Levi-Civita Signs

For a 3-tuple I = (i,j,k), the Hodge star sign is:
  σ(I) = sgn(i,j,k,a,b,c,d)
where (a,b,c,d) is the sorted complement.

This sign is computed by counting inversions.
-/

/-- Levi-Civita sign for 3→4 Hodge star -/
def sign3 : Fin 35 → ℝ := fun n =>
  match n.val with
  -- Signs computed by counting inversions in (i,j,k,a,b,c,d) → (0,1,2,3,4,5,6)
  | 0 => 1    -- (0,1,2,3,4,5,6): 0 inversions
  | 1 => -1   -- (0,1,3,2,4,5,6): 1 inversion
  | 2 => 1    -- (0,1,4,2,3,5,6): 2 inversions
  | 3 => -1   -- (0,1,5,2,3,4,6): 3 inversions
  | 4 => 1    -- (0,1,6,2,3,4,5): 4 inversions
  | 5 => 1    -- (0,2,3,1,4,5,6): 2 inversions
  | 6 => -1   -- (0,2,4,1,3,5,6): 3 inversions
  | 7 => 1    -- (0,2,5,1,3,4,6): 4 inversions
  | 8 => -1   -- (0,2,6,1,3,4,5): 5 inversions
  | 9 => 1    -- (0,3,4,1,2,5,6): 4 inversions
  | 10 => -1  -- (0,3,5,1,2,4,6): 5 inversions
  | 11 => 1   -- (0,3,6,1,2,4,5): 6 inversions
  | 12 => 1   -- (0,4,5,1,2,3,6): 6 inversions
  | 13 => -1  -- (0,4,6,1,2,3,5): 7 inversions
  | 14 => 1   -- (0,5,6,1,2,3,4): 8 inversions
  | 15 => -1  -- (1,2,3,0,4,5,6): 3 inversions
  | 16 => 1   -- (1,2,4,0,3,5,6): 4 inversions
  | 17 => -1  -- (1,2,5,0,3,4,6): 5 inversions
  | 18 => 1   -- (1,2,6,0,3,4,5): 6 inversions
  | 19 => -1  -- (1,3,4,0,2,5,6): 5 inversions
  | 20 => 1   -- (1,3,5,0,2,4,6): 6 inversions
  | 21 => -1  -- (1,3,6,0,2,4,5): 7 inversions
  | 22 => -1  -- (1,4,5,0,2,3,6): 7 inversions
  | 23 => 1   -- (1,4,6,0,2,3,5): 8 inversions
  | 24 => -1  -- (1,5,6,0,2,3,4): 9 inversions
  | 25 => 1   -- (2,3,4,0,1,5,6): 6 inversions
  | 26 => -1  -- (2,3,5,0,1,4,6): 7 inversions
  | 27 => 1   -- (2,3,6,0,1,4,5): 8 inversions
  | 28 => 1   -- (2,4,5,0,1,3,6): 8 inversions
  | 29 => -1  -- (2,4,6,0,1,3,5): 9 inversions
  | 30 => 1   -- (2,5,6,0,1,3,4): 10 inversions
  | 31 => -1  -- (3,4,5,0,1,2,6): 9 inversions
  | 32 => 1   -- (3,4,6,0,1,2,5): 10 inversions
  | 33 => -1  -- (3,5,6,0,1,2,4): 11 inversions
  | 34 => 1   -- (4,5,6,0,1,2,3): 12 inversions
  | _ => 1

/-- Sign for 4→3 Hodge star (uses complement's sign) -/
def sign4 : Fin 35 → ℝ := fun n => sign3 (complement4to3 n)

/-- All signs are ±1 -/
theorem sign3_squared (n : Fin 35) : sign3 n * sign3 n = 1 := by
  fin_cases n <;> simp [sign3]

theorem sign4_squared (n : Fin 35) : sign4 n * sign4 n = 1 := by
  unfold sign4; exact sign3_squared _

/-!
## Part 4: Hodge Star on Coefficients

The Hodge star ⋆ : Ω³ → Ω⁴ acts on coefficients by:
  (⋆ω)_J = sign(I) · ω_I
where J is the complement of I.
-/

/-- Hodge star on 3-form coefficients -/
def hodgeStar3to4 (ω : Fin 35 → ℝ) : Fin 35 → ℝ := fun j =>
  sign3 (complement4to3 j) * ω (complement4to3 j)

/-- Hodge star on 4-form coefficients -/
def hodgeStar4to3 (η : Fin 35 → ℝ) : Fin 35 → ℝ := fun i =>
  sign4 (complement3to4 i) * η (complement3to4 i)

/-- ⋆⋆ = +1 on 3-forms (key property in dimension 7) -/
theorem hodgeStar_invol_3 (ω : Fin 35 → ℝ) : hodgeStar4to3 (hodgeStar3to4 ω) = ω := by
  funext i
  unfold hodgeStar4to3 hodgeStar3to4 sign4
  -- Goal: sign3 (complement4to3 (complement3to4 i)) *
  --       (sign3 (complement4to3 (complement3to4 i)) * ω (complement4to3 (complement3to4 i))) = ω i
  -- Use complement_invol_34 : complement4to3 (complement3to4 n) = n
  simp only [complement_invol_34]
  -- Goal: sign3 i * (sign3 i * ω i) = ω i
  rw [← mul_assoc, sign3_squared, one_mul]

/-- ⋆⋆ = +1 on 4-forms -/
theorem hodgeStar_invol_4 (η : Fin 35 → ℝ) : hodgeStar3to4 (hodgeStar4to3 η) = η := by
  funext j
  unfold hodgeStar3to4 hodgeStar4to3 sign4
  -- Goal: sign3 (complement4to3 (complement3to4 (complement4to3 j))) *
  --       (sign3 (complement4to3 j) * η (complement3to4 (complement4to3 j))) = η j
  -- Use complement_invol_43 : complement3to4 (complement4to3 n) = n
  simp only [complement_invol_43]
  -- Goal: sign3 (complement4to3 j) * (sign3 (complement4to3 j) * η j) = η j
  rw [← mul_assoc, sign3_squared, one_mul]

/-- Hodge star is linear -/
theorem hodgeStar3to4_linear (a : ℝ) (ω η : Fin 35 → ℝ) :
    hodgeStar3to4 (fun i => a * ω i + η i) = fun j => a * hodgeStar3to4 ω j + hodgeStar3to4 η j := by
  funext j
  unfold hodgeStar3to4
  ring

/-!
## Part 5: Canonical G₂ Forms

The G₂ 3-form φ₀ has 7 nonzero coefficients at Fano line indices.
The coassociative 4-form ψ₀ = ⋆φ₀ is computed via the Hodge star.
-/

/-- G₂ 3-form φ₀: coefficients are 1 at Fano line indices, 0 elsewhere -/
def phi0_coeffs : Fin 35 → ℝ := fun n =>
  match n.val with
  | 1 => 1   -- (0,1,3): Fano line
  | 8 => 1   -- (0,2,6): Fano line
  | 12 => 1  -- (0,4,5): Fano line
  | 16 => 1  -- (1,2,4): Fano line
  | 24 => 1  -- (1,5,6): Fano line
  | 26 => 1  -- (2,3,5): Fano line
  | 32 => 1  -- (3,4,6): Fano line
  | _ => 0

/-- Coassociative 4-form ψ₀ = ⋆φ₀ (computed, not hardcoded) -/
def psi0_coeffs : Fin 35 → ℝ := hodgeStar3to4 phi0_coeffs

/-- ψ₀ = ⋆φ₀ by definition -/
theorem psi0_eq_star_phi0 : psi0_coeffs = hodgeStar3to4 phi0_coeffs := rfl

/-- ⋆ψ₀ = φ₀ (inverse Hodge) -/
theorem star_psi0_eq_phi0 : hodgeStar4to3 psi0_coeffs = phi0_coeffs := by
  unfold psi0_coeffs
  exact hodgeStar_invol_3 phi0_coeffs

/-- Verify specific values of ψ₀ -/
-- Fano indices in 3-form: 1, 8, 12, 16, 24, 26, 32
-- Their complements: 33, 26, 22, 18, 10, 8, 2
-- Note: We prove these by explicit unfolding since Real.decidableEq is noncomputable

theorem psi0_at_2 : psi0_coeffs ⟨2, by omega⟩ = 1 := by
  unfold psi0_coeffs hodgeStar3to4 complement4to3 sign3 phi0_coeffs
  norm_num

theorem psi0_at_8 : psi0_coeffs ⟨8, by omega⟩ = -1 := by
  unfold psi0_coeffs hodgeStar3to4 complement4to3 sign3 phi0_coeffs
  norm_num

theorem psi0_at_10 : psi0_coeffs ⟨10, by omega⟩ = -1 := by
  unfold psi0_coeffs hodgeStar3to4 complement4to3 sign3 phi0_coeffs
  norm_num

theorem psi0_at_18 : psi0_coeffs ⟨18, by omega⟩ = 1 := by
  unfold psi0_coeffs hodgeStar3to4 complement4to3 sign3 phi0_coeffs
  norm_num

theorem psi0_at_22 : psi0_coeffs ⟨22, by omega⟩ = 1 := by
  unfold psi0_coeffs hodgeStar3to4 complement4to3 sign3 phi0_coeffs
  norm_num

theorem psi0_at_26 : psi0_coeffs ⟨26, by omega⟩ = -1 := by
  unfold psi0_coeffs hodgeStar3to4 complement4to3 sign3 phi0_coeffs
  norm_num

theorem psi0_at_33 : psi0_coeffs ⟨33, by omega⟩ = -1 := by
  unfold psi0_coeffs hodgeStar3to4 complement4to3 sign3 phi0_coeffs
  norm_num

/-!
## Part 6: G₂ DiffForm Structures

Lift the coefficient-level operations to DiffForm structures.
-/

/-- Canonical G₂ 3-form as constant DiffForm -/
def phi0_form : DiffForm 3 := constDiffForm 3 phi0_coeffs

/-- Canonical G₂ 4-form (Hodge dual of φ₀) as constant DiffForm -/
def psi0_form : DiffForm 4 := constDiffForm 4 psi0_coeffs

/-- Hodge star on constant 3-forms -/
def hodgeStar3 (ω : DiffForm 3) : DiffForm 4 :=
  constDiffForm 4 (hodgeStar3to4 (ω.coeffs 0))

/-- Hodge star on constant 4-forms -/
def hodgeStar4 (η : DiffForm 4) : DiffForm 3 :=
  constDiffForm 3 (hodgeStar4to3 (η.coeffs 0))

/-- ψ₀ = ⋆φ₀ as DiffForms -/
theorem psi0_form_eq_star_phi0_form : psi0_form = hodgeStar3 phi0_form := by
  unfold psi0_form hodgeStar3 phi0_form constDiffForm psi0_coeffs
  rfl

/-- ⋆(⋆φ₀) = φ₀ as DiffForms -/
theorem hodgeStar_invol_phi0 : hodgeStar4 (hodgeStar3 phi0_form) = phi0_form := by
  unfold hodgeStar4 hodgeStar3 phi0_form constDiffForm
  congr 1
  funext _ i
  exact congrFun (hodgeStar_invol_3 phi0_coeffs) i

/-!
## Part 7: Corrected G₂ Form Data

The standardG2 in DifferentialFormsR7 should use these correct coefficients.
-/

/-- Corrected G₂ form data with proper Hodge duality -/
def correctedG2 : G2FormData where
  phi := phi0_form
  psi := psi0_form

/-- Corrected G₂ is torsion-free on flat ℝ⁷ -/
theorem correctedG2_torsionFree :
    G2FormData.TorsionFree trivialExteriorDeriv correctedG2 := by
  unfold G2FormData.TorsionFree correctedG2
  constructor
  · exact constant_forms_closed 3 phi0_form
  · exact constant_forms_closed 4 psi0_form

/-!
## Part 8: Module Certificate
-/

/-- Hodge star computation certificate -/
theorem hodge_compute_certificate :
    -- Complement bijection
    (∀ n, complement4to3 (complement3to4 n) = n) ∧
    (∀ n, complement3to4 (complement4to3 n) = n) ∧
    -- Involutivity
    (∀ ω, hodgeStar4to3 (hodgeStar3to4 ω) = ω) ∧
    (∀ η, hodgeStar3to4 (hodgeStar4to3 η) = η) ∧
    -- G₂ torsion-free
    G2FormData.TorsionFree trivialExteriorDeriv correctedG2 := by
  exact ⟨complement_invol_34, complement_invol_43,
         hodgeStar_invol_3, hodgeStar_invol_4,
         correctedG2_torsionFree⟩

end GIFT.Geometry.HodgeStarCompute
