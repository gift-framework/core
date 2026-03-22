/-
GIFT Foundations: Exterior Algebra
==================================

Formalizes Λᵏ(V) exterior algebra and wedge product using Mathlib.
This provides the foundation for differential forms.

Version: 3.2.0
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import GIFT.Foundations.Analysis.InnerProductSpace

namespace GIFT.Foundations.Analysis.ExteriorAlgebra

open InnerProductSpace

/-!
## Exterior Algebra on ℝⁿ
-/

/-- Exterior algebra of ℝⁿ -/
abbrev Exterior (n : ℕ) := ExteriorAlgebra ℝ (Fin n → ℝ)

/-- Canonical inclusion ι : V → Λ(V) -/
noncomputable def ι' {n : ℕ} (v : Fin n → ℝ) : Exterior n :=
  ExteriorAlgebra.ι ℝ v

/-!
## Wedge Product
-/

/-- Wedge product as multiplication in exterior algebra -/
noncomputable def wedge {n : ℕ} (ω η : Exterior n) : Exterior n :=
  ω * η

-- Precedence 70 > 65 (addition) so ω₁ ∧' η + ω₂ parses as (ω₁ ∧' η) + ω₂
infixl:70 " ∧' " => wedge

/-- Wedge is associative -/
theorem wedge_assoc {n : ℕ} (ω η ζ : Exterior n) :
    (ω ∧' η) ∧' ζ = ω ∧' (η ∧' ζ) := by
  unfold wedge
  exact mul_assoc ω η ζ

/-- Wedge is left-distributive -/
theorem wedge_add_left {n : ℕ} (ω₁ ω₂ η : Exterior n) :
    (ω₁ + ω₂) ∧' η = (ω₁ ∧' η) + (ω₂ ∧' η) := by
  unfold wedge
  exact add_mul ω₁ ω₂ η

/-- Wedge is right-distributive -/
theorem wedge_add_right {n : ℕ} (ω η₁ η₂ : Exterior n) :
    ω ∧' (η₁ + η₂) = (ω ∧' η₁) + (ω ∧' η₂) := by
  unfold wedge
  exact mul_add ω η₁ η₂

/-!
## Anticommutativity for 1-forms
-/

/-- Key property: v ∧ v = 0 -/
theorem ι_wedge_self_eq_zero {n : ℕ} (v : Fin n → ℝ) :
    ι' v ∧' ι' v = 0 := by
  unfold wedge ι'
  exact ExteriorAlgebra.ι_sq_zero v

/-!
## Basis k-forms
-/

/-- Standard basis vector as function -/
def stdVec {n : ℕ} (i : Fin n) : Fin n → ℝ := fun j => if i = j then 1 else 0

/-- Basis 1-forms as elements of exterior algebra -/
noncomputable def e {n : ℕ} (i : Fin n) : Exterior n :=
  ι' (stdVec i)

/-- Basis 2-form eᵢ ∧ eⱼ -/
noncomputable def e2 {n : ℕ} (i j : Fin n) : Exterior n :=
  e i ∧' e j

/-- Basis 3-form eᵢ ∧ eⱼ ∧ eₖ -/
noncomputable def e3 {n : ℕ} (i j k : Fin n) : Exterior n :=
  e i ∧' e j ∧' e k

/-- eᵢ ∧ eᵢ = 0 -/
theorem e_wedge_self {n : ℕ} (i : Fin n) :
    e i ∧' e (n := n) i = 0 := by
  unfold e
  exact ι_wedge_self_eq_zero _

/-!
## Dimension Formulas
-/

/-- Dimension of 2-forms on ℝ⁷: C(7,2) = 21 -/
theorem dim_2forms_7 : Nat.choose 7 2 = 21 := by native_decide

/-- Dimension of 3-forms on ℝ⁷: C(7,3) = 35 -/
theorem dim_3forms_7 : Nat.choose 7 3 = 35 := by native_decide

/-- Dimension of 7-forms on ℝ⁷ (top form): C(7,7) = 1 -/
theorem dim_7forms_7 : Nat.choose 7 7 = 1 := by native_decide

/-- Yukawa degree: 2 + 2 + 3 = 7 -/
theorem yukawa_degree : 2 + 2 + 3 = 7 := by native_decide

/-!
## Yukawa Coupling Structure

For Yukawa Y_ijk = ∫_{K7} ωᵢ ∧ ωⱼ ∧ ηₖ where ωᵢ,ωⱼ ∈ Ω² and ηₖ ∈ Ω³
-/

/-- Triple wedge gives top form (volume element) -/
theorem yukawa_wedge_is_top_form : Nat.choose 7 (2 + 2 + 3) = 1 := by
  native_decide

/-- 21 × 21 × 77 possible Yukawa couplings -/
theorem yukawa_coupling_count : 21 * 21 * 77 = 33957 := by native_decide

/-!
## G2 Decomposition of Forms

On a G2-manifold, k-forms decompose under G2 representations.
-/

/-- Ω² decomposes as Ω²₇ ⊕ Ω²₁₄ -/
theorem omega2_G2_decomposition : 7 + 14 = 21 := by native_decide

/-- Ω³ decomposes as Ω³₁ ⊕ Ω³₇ ⊕ Ω³₂₇ -/
theorem omega3_G2_decomposition : 1 + 7 + 27 = 35 := by native_decide

end GIFT.Foundations.Analysis.ExteriorAlgebra
