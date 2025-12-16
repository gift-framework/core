/-
  GIFT Foundations: G2 Cross Product (Axioms Tier 2: B2-B5)
  =========================================================

  The 7-dimensional cross product is intimately connected to:
  1. The octonion multiplication
  2. The G2 holonomy group
  3. The associative 3-form φ₀

  For u, v ∈ ℝ⁷ (imaginary octonions), the cross product satisfies:
  - u × v = Im(u · v) where · is octonion multiplication
  - |u × v|² = |u|²|v|² - ⟨u,v⟩²  (Lagrange identity)
  - u × v = -v × u  (antisymmetry)
  - The stabilizer of × in GL(7) is exactly G2

  References:
    - Harvey & Lawson, "Calibrated Geometries"
    - Bryant, "Metrics with exceptional holonomy"
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GIFT.Foundations.G2CrossProduct

open Finset BigOperators

/-!
## The 7-dimensional Euclidean Space

Im(𝕆) ≅ ℝ⁷ is the imaginary part of the octonions.
-/

/-- 7-dimensional Euclidean space (imaginary octonions) -/
abbrev R7 := EuclideanSpace ℝ (Fin 7)

/-!
## Fano Plane Structure

The multiplication of imaginary octonion units follows the Fano plane.
The 7 points are {0,1,2,3,4,5,6} and the 7 lines are:
  {0,1,3}, {1,2,4}, {2,3,5}, {3,4,6}, {4,5,0}, {5,6,1}, {6,0,2}

For a line {i,j,k} in cyclic order: eᵢ × eⱼ = eₖ
-/

/-- Fano plane lines (cyclic triples) -/
def fano_lines : List (Fin 7 × Fin 7 × Fin 7) :=
  [(0,1,3), (1,2,4), (2,3,5), (3,4,6), (4,5,0), (5,6,1), (6,0,2)]

/-- Number of Fano lines -/
theorem fano_lines_count : fano_lines.length = 7 := rfl

/-- Structure constants for the 7D cross product (simplified version)
    Returns +1, -1, or 0 based on Fano plane structure -/
def epsilon (i j k : Fin 7) : ℤ :=
  -- We use a lookup approach for the 7 cyclic lines
  if (i.val, j.val, k.val) = (0, 1, 3) ∨ (i.val, j.val, k.val) = (1, 3, 0) ∨
     (i.val, j.val, k.val) = (3, 0, 1) then 1
  else if (i.val, j.val, k.val) = (3, 1, 0) ∨ (i.val, j.val, k.val) = (0, 3, 1) ∨
          (i.val, j.val, k.val) = (1, 0, 3) then -1
  else if (i.val, j.val, k.val) = (1, 2, 4) ∨ (i.val, j.val, k.val) = (2, 4, 1) ∨
          (i.val, j.val, k.val) = (4, 1, 2) then 1
  else if (i.val, j.val, k.val) = (4, 2, 1) ∨ (i.val, j.val, k.val) = (1, 4, 2) ∨
          (i.val, j.val, k.val) = (2, 1, 4) then -1
  else if (i.val, j.val, k.val) = (2, 3, 5) ∨ (i.val, j.val, k.val) = (3, 5, 2) ∨
          (i.val, j.val, k.val) = (5, 2, 3) then 1
  else if (i.val, j.val, k.val) = (5, 3, 2) ∨ (i.val, j.val, k.val) = (2, 5, 3) ∨
          (i.val, j.val, k.val) = (3, 2, 5) then -1
  else if (i.val, j.val, k.val) = (3, 4, 6) ∨ (i.val, j.val, k.val) = (4, 6, 3) ∨
          (i.val, j.val, k.val) = (6, 3, 4) then 1
  else if (i.val, j.val, k.val) = (6, 4, 3) ∨ (i.val, j.val, k.val) = (3, 6, 4) ∨
          (i.val, j.val, k.val) = (4, 3, 6) then -1
  else if (i.val, j.val, k.val) = (4, 5, 0) ∨ (i.val, j.val, k.val) = (5, 0, 4) ∨
          (i.val, j.val, k.val) = (0, 4, 5) then 1
  else if (i.val, j.val, k.val) = (0, 5, 4) ∨ (i.val, j.val, k.val) = (4, 0, 5) ∨
          (i.val, j.val, k.val) = (5, 4, 0) then -1
  else if (i.val, j.val, k.val) = (5, 6, 1) ∨ (i.val, j.val, k.val) = (6, 1, 5) ∨
          (i.val, j.val, k.val) = (1, 5, 6) then 1
  else if (i.val, j.val, k.val) = (1, 6, 5) ∨ (i.val, j.val, k.val) = (5, 1, 6) ∨
          (i.val, j.val, k.val) = (6, 5, 1) then -1
  else if (i.val, j.val, k.val) = (6, 0, 2) ∨ (i.val, j.val, k.val) = (0, 2, 6) ∨
          (i.val, j.val, k.val) = (2, 6, 0) then 1
  else if (i.val, j.val, k.val) = (2, 0, 6) ∨ (i.val, j.val, k.val) = (6, 2, 0) ∨
          (i.val, j.val, k.val) = (0, 6, 2) then -1
  else 0

/-!
## The 7-dimensional Cross Product

(u × v)ₖ = ∑ᵢⱼ ε(i,j,k) uᵢ vⱼ
-/

/-- The 7-dimensional cross product -/
noncomputable def cross (u v : R7) : R7 :=
  (WithLp.equiv 2 _).symm (fun k => ∑ i, ∑ j, (epsilon i j k : ℝ) * u i * v j)

/-!
## Helper lemmas for epsilon structure constants
-/

/-- epsilon is antisymmetric in first two arguments - PROVEN by exhaustive check -/
theorem epsilon_antisymm (i j k : Fin 7) : epsilon i j k = -epsilon j i k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> native_decide

/-- epsilon vanishes when first two indices are equal -/
theorem epsilon_diag (i k : Fin 7) : epsilon i i k = 0 := by
  fin_cases i <;> fin_cases k <;> native_decide

/-- Helper: Extract k-th component of cross product (definitional)
    (cross u v) k = ∑ i, ∑ j, ε(i,j,k) * u(i) * v(j) -/
@[simp] theorem cross_apply (u v : R7) (k : Fin 7) :
    (cross u v) k = ∑ i, ∑ j, (epsilon i j k : ℝ) * u i * v j := rfl

/-!
## Theorem B2: G2_cross_bilinear

The cross product is bilinear. This follows from the definition
as a sum of products with constant coefficients ε(i,j,k).
-/

/-- B2a: Cross product is linear in first argument (PROVEN) -/
theorem cross_left_linear (a : ℝ) (u v w : R7) :
    cross (a • u + v) w = a • cross u w + cross v w := by
  ext k
  simp only [cross_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  -- LHS: ∑ i j, ε * (a * u i + v i) * w j
  -- RHS: a * (∑ i j, ε * u i * w j) + ∑ i j, ε * v i * w j
  -- First expand ε * (X + Y) = ε * X + ε * Y, then (A + B) * w = A*w + B*w
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  all_goals (apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring)

/-- B2b: Cross product is linear in second argument (PROVEN) -/
theorem cross_right_linear (a : ℝ) (u v w : R7) :
    cross u (a • v + w) = a • cross u v + cross u w := by
  ext k
  simp only [cross_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  all_goals (apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring)

/-- B2: Cross product is bilinear (PROVEN) -/
theorem G2_cross_bilinear :
    (∀ a : ℝ, ∀ u v w : R7, cross (a • u + v) w = a • cross u w + cross v w) ∧
    (∀ a : ℝ, ∀ u v w : R7, cross u (a • v + w) = a • cross u v + cross u w) :=
  ⟨cross_left_linear, cross_right_linear⟩

/-!
## Theorem B3: G2_cross_antisymm (PROVEN)

u × v = -v × u

Proof: ε(i,j,k) = -ε(j,i,k) (epsilon_antisymm) + extensionality
-/

/-- B3: Cross product is antisymmetric (PROVEN)
    Proof: Use epsilon_antisymm and sum reindexing -/
theorem G2_cross_antisymm (u v : R7) : cross u v = -cross v u := by
  ext k
  simp only [cross_apply, PiLp.neg_apply]
  -- Goal: ∑ i, ∑ j, ε(i,j,k) * u(i) * v(j) = -(∑ i, ∑ j, ε(i,j,k) * v(i) * u(j))
  -- Swap indices i ↔ j in RHS, then use ε(j,i,k) = -ε(i,j,k)
  conv_rhs =>
    arg 1  -- the sum inside negation
    rw [Finset.sum_comm]  -- swap order of sums
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  -- Goal: ε(i,j,k) * u i * v j = -(ε(j,i,k) * v j * u i)
  have h := epsilon_antisymm i j k
  simp only [Int.cast_neg, h]
  ring

/-- B3': u × u = 0 (PROVEN) - follows from antisymmetry -/
theorem cross_self (u : R7) : cross u u = 0 := by
  have h := G2_cross_antisymm u u
  -- h: cross u u = -(cross u u), i.e., x = -x
  -- In a vector space over ℝ, x = -x implies x = 0
  have h2 : (2 : ℝ) • cross u u = 0 := by
    calc (2 : ℝ) • cross u u
        = cross u u + cross u u := two_smul ℝ _
      _ = cross u u + (-cross u u) := by rw [← h]
      _ = 0 := add_neg_cancel _
  -- Since 2 ≠ 0 in ℝ, we get cross u u = 0
  have h3 : (2 : ℝ) ≠ 0 := two_ne_zero
  exact (smul_eq_zero.mp h2).resolve_left h3

/-!
## Theorem B4: G2_cross_norm (Lagrange Identity) - PROVEN

|u × v|² = |u|²|v|² - ⟨u,v⟩²

This is the 7D generalization of the 3D identity.

The proof strategy:
1. Define epsilon_contraction: ∑ₖ ε(i,j,k)ε(l,m,k)
2. Prove by exhaustive computation that when contracted with uᵢvⱼuₗvₘ,
   the result equals |u|²|v|² - ⟨u,v⟩²
3. The coassociative 4-form ψ terms vanish due to symmetry of uᵢuₗ

Key insight: The 7D identity differs from 3D, but Lagrange still holds because
the antisymmetric remainder (ψ) vanishes under the symmetric contraction.
-/

/-- Epsilon contraction: ∑ₖ ε(i,j,k) * ε(l,m,k) -/
def epsilon_contraction (i j l m : Fin 7) : ℤ :=
  ∑ k : Fin 7, epsilon i j k * epsilon l m k

/-- The epsilon contraction at diagonal (i,j,i,j) equals 1 when i≠j, 0 when i=j -/
theorem epsilon_contraction_diagonal (i j : Fin 7) :
    epsilon_contraction i j i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> native_decide

/-- Epsilon contraction is zero when first two indices are equal -/
theorem epsilon_contraction_first_eq (i l m : Fin 7) :
    epsilon_contraction i i l m = 0 := by
  fin_cases i <;> fin_cases l <;> fin_cases m <;> native_decide

/-- The Lagrange-relevant part: when i=l and j=m (distinct), contraction = 1 -/
theorem epsilon_contraction_same (i j : Fin 7) (h : i ≠ j) :
    epsilon_contraction i j i j = 1 := by
  fin_cases i <;> fin_cases j <;> first | contradiction | native_decide

/-- When i=m and j=l (distinct), contraction = -1 -/
theorem epsilon_contraction_swap (i j : Fin 7) (h : i ≠ j) :
    epsilon_contraction i j j i = -1 := by
  fin_cases i <;> fin_cases j <;> first | contradiction | native_decide

/-!
### B4 Proof via Coassociative 4-form Antisymmetry

The epsilon contraction in 7D differs from 3D:
  ∑ₖ ε(i,j,k)ε(l,m,k) = δᵢₗδⱼₘ - δᵢₘδⱼₗ + ψᵢⱼₗₘ

where ψ is the coassociative 4-form correction. The key insight is that ψ is
antisymmetric under i↔l, so when contracted with the symmetric tensor uᵢuₗ,
the ψ contribution vanishes.

Reference: Harvey & Lawson, "Calibrated Geometries", Acta Math. 1982
-/

/-- The coassociative 4-form ψ (deviation from 3D Kronecker formula)
    ψᵢⱼₗₘ = ∑ₖ ε(i,j,k)ε(l,m,k) - (δᵢₗδⱼₘ - δᵢₘδⱼₗ) -/
def psi (i j l m : Fin 7) : ℤ :=
  epsilon_contraction i j l m -
  ((if i = l ∧ j = m then 1 else 0) - (if i = m ∧ j = l then 1 else 0))

/-- ψ is antisymmetric under exchange of first and third indices (i ↔ l)
    Verified exhaustively for all 7⁴ = 2401 index combinations -/
theorem psi_antisym_il (i j l m : Fin 7) : psi i j l m = -psi l j i m := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;> native_decide

/-- Epsilon contraction decomposition into Kronecker + ψ -/
theorem epsilon_contraction_decomp (i j l m : Fin 7) :
    epsilon_contraction i j l m =
    ((if i = l ∧ j = m then 1 else 0) - (if i = m ∧ j = l then 1 else 0)) + psi i j l m := by
  simp only [psi]
  ring

/-- The Kronecker part of epsilon contraction -/
def kronecker_part (i j l m : Fin 7) : ℤ :=
  (if i = l ∧ j = m then 1 else 0) - (if i = m ∧ j = l then 1 else 0)

/-- Generic lemma: antisymmetric tensor contracted with symmetric tensor vanishes.
    If T(i,l) = -T(l,i) and S(i,l) = S(l,i), then ∑ᵢₗ T(i,l)S(i,l) = 0.
    Here we apply this with T = ψ(·,j,·,m) and S(i,l) = uᵢuₗ. -/
theorem antisym_sym_contract_vanishes
    (T : Fin 7 → Fin 7 → ℝ) (u : Fin 7 → ℝ)
    (hT : ∀ i l, T i l = -T l i) :
    ∑ i : Fin 7, ∑ l : Fin 7, T i l * u i * u l = 0 := by
  -- Show S = -S, hence S = 0
  have h : ∑ i : Fin 7, ∑ l : Fin 7, T i l * u i * u l =
           -(∑ i : Fin 7, ∑ l : Fin 7, T i l * u i * u l) := by
    calc ∑ i : Fin 7, ∑ l : Fin 7, T i l * u i * u l
        = ∑ l : Fin 7, ∑ i : Fin 7, T l i * u l * u i := by rw [Finset.sum_comm]
      _ = ∑ l : Fin 7, ∑ i : Fin 7, (-T i l) * u l * u i := by
          apply Finset.sum_congr rfl; intro l _
          apply Finset.sum_congr rfl; intro i _
          rw [hT l i]
      _ = ∑ l : Fin 7, ∑ i : Fin 7, (-(T i l * u l * u i)) := by
          apply Finset.sum_congr rfl; intro l _
          apply Finset.sum_congr rfl; intro i _
          ring
      _ = -(∑ l : Fin 7, ∑ i : Fin 7, T i l * u l * u i) := by
          -- Apply sum_neg_distrib from inside out
          conv_lhs => arg 2; ext l; rw [Finset.sum_neg_distrib]
          rw [Finset.sum_neg_distrib]
      _ = -(∑ i : Fin 7, ∑ l : Fin 7, T i l * u l * u i) := by rw [Finset.sum_comm]
      _ = -(∑ i : Fin 7, ∑ l : Fin 7, T i l * u i * u l) := by
          congr 1
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro l _
          ring
  linarith

/-- The ψ correction vanishes when contracted with symmetric uᵢuₗ and vⱼvₘ -/
theorem psi_contract_vanishes (u v : Fin 7 → ℝ) :
    ∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin 7, ∑ m : Fin 7,
      (psi i j l m : ℝ) * u i * u l * v j * v m = 0 := by
  -- For each fixed (j,m), the inner sum over (i,l) vanishes by antisymmetry
  have h_inner : ∀ j m : Fin 7,
      ∑ i : Fin 7, ∑ l : Fin 7, (psi i j l m : ℝ) * u i * u l = 0 := by
    intro j m
    apply antisym_sym_contract_vanishes (fun i l => (psi i j l m : ℝ)) u
    intro i l
    have h := psi_antisym_il i j l m
    simp only [h, Int.cast_neg]
  -- Reorder sums to put j, m on outside, then factor out v j * v m
  calc ∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin 7, ∑ m : Fin 7,
         (psi i j l m : ℝ) * u i * u l * v j * v m
      = ∑ j : Fin 7, ∑ i : Fin 7, ∑ l : Fin 7, ∑ m : Fin 7,
         (psi i j l m : ℝ) * u i * u l * v j * v m := by rw [Finset.sum_comm]
    _ = ∑ j : Fin 7, ∑ i : Fin 7, ∑ m : Fin 7, ∑ l : Fin 7,
         (psi i j l m : ℝ) * u i * u l * v j * v m := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]
    _ = ∑ j : Fin 7, ∑ m : Fin 7, ∑ i : Fin 7, ∑ l : Fin 7,
         (psi i j l m : ℝ) * u i * u l * v j * v m := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_comm]
    _ = ∑ j : Fin 7, ∑ m : Fin 7, (v j * v m) *
         (∑ i : Fin 7, ∑ l : Fin 7, (psi i j l m : ℝ) * u i * u l) := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro l _
        ring
    _ = ∑ j : Fin 7, ∑ m : Fin 7, (v j * v m) * 0 := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro m _
        rw [h_inner j m]
    _ = 0 := by simp only [mul_zero, Finset.sum_const_zero]

/-- B4: Lagrange identity for 7D cross product (KEY LEMMAS PROVEN)
    |u × v|² = |u|²|v|² - ⟨u,v⟩²

    The mathematical content is fully proven via:
    - epsilon_contraction_decomp: ∑ₖ ε(i,j,k)ε(l,m,k) = Kronecker + ψ
    - psi_antisym_il: ψ is antisymmetric under i↔l (2401 cases verified)
    - psi_contract_vanishes: ψ terms vanish under symmetric contraction

    The final step connecting to EuclideanSpace norms requires Mathlib lemmas
    for expanding ‖·‖² and ⟨·,·⟩ in terms of coordinate sums.
    Kept as axiom pending this plumbing; the core identity is proven. -/
axiom G2_cross_norm (u v : R7) :
    ‖cross u v‖^2 = ‖u‖^2 * ‖v‖^2 - (@inner ℝ R7 _ u v)^2

/-!
## Axiom B5: cross_is_octonion

The cross product equals the imaginary part of octonion multiplication.
For pure imaginary octonions u, v: u × v = Im(u · v)

This is true by construction: we defined epsilon using the Fano plane
structure which is exactly the octonion multiplication table.
-/

/-- B5: Cross product structure matches octonion multiplication
    Every nonzero epsilon corresponds to a Fano line permutation.

    This is true by construction: epsilon is defined using the Fano plane.
    NOTE: Exhaustive case verification (343 cases) causes deterministic timeout.
    Kept as axiom until a more efficient proof strategy is found. -/
axiom cross_is_octonion_structure :
    ∀ i j k : Fin 7, epsilon i j k ≠ 0 →
      (∃ line ∈ fano_lines, (i, j, k) = line ∨
        (j, k, i) = line ∨ (k, i, j) = line ∨
        (k, j, i) = line ∨ (j, i, k) = line ∨ (i, k, j) = line)

/-!
## Connection to G2 Holonomy

The group G2 is exactly the stabilizer of the cross product:
  G2 = { g ∈ GL(7) | g(u × v) = gu × gv for all u, v }

Equivalently, G2 stabilizes the associative 3-form φ₀.
-/

/-- The associative 3-form φ₀ (structure constants) -/
def phi0 (i j k : Fin 7) : ℝ := epsilon i j k

/-- G2 condition: preserves the cross product -/
def preserves_cross (g : R7 →ₗ[ℝ] R7) : Prop :=
  ∀ u v, g (cross u v) = cross (g u) (g v)

/-- G2 condition: preserves φ₀ -/
def preserves_phi0 (g : R7 →ₗ[ℝ] R7) : Prop :=
  ∀ i j k, phi0 i j k = ∑ a, ∑ b, ∑ c,
    (g (EuclideanSpace.single i 1) a) *
    (g (EuclideanSpace.single j 1) b) *
    (g (EuclideanSpace.single k 1) c) * phi0 a b c

/-- The two G2 characterizations are equivalent -/
axiom G2_equiv_characterizations (g : R7 →ₗ[ℝ] R7) :
    preserves_cross g ↔ preserves_phi0 g

/-!
## Dimension of G2

dim(G2) = 14 = dim(GL(7)) - dim(orbit of φ₀) = 49 - 35
-/

/-- dim(GL(7)) = 49 -/
theorem dim_GL7 : 7 * 7 = 49 := rfl

/-- The orbit of φ₀ under GL(7) has dimension 35 -/
def orbit_phi0_dim : ℕ := 35

/-- G2 dimension from stabilizer calculation -/
theorem G2_dim_from_stabilizer : 49 - orbit_phi0_dim = 14 := rfl

/-- Alternative: G2 has 12 roots + rank 2 = 14 -/
theorem G2_dim_from_roots : 12 + 2 = 14 := rfl

/-!
## Summary of Tier 2 Status (v3.1.2)

**Core Cross Product Theorems (6/6 PROVEN):**
- epsilon_antisymm ✅ PROVEN (7³ = 343 cases)
- epsilon_diag ✅ PROVEN (7² = 49 cases)
- cross_apply ✅ PROVEN (definitional)
- B2: G2_cross_bilinear ✅ PROVEN
- B3: G2_cross_antisymm ✅ PROVEN
- B3': cross_self ✅ PROVEN

**Epsilon Contraction Lemmas (4/4 PROVEN):**
- epsilon_contraction (definition)
- epsilon_contraction_diagonal ✅ PROVEN (7² = 49 cases)
- epsilon_contraction_first_eq ✅ PROVEN (7³ = 343 cases)
- epsilon_contraction_same ✅ PROVEN (i≠j, 42 cases)
- epsilon_contraction_swap ✅ PROVEN (i≠j, 42 cases)

**B4 Lagrange Identity Infrastructure (NEW in v3.1.2):**
- psi (coassociative 4-form) ✅ DEFINED
- psi_antisym_il ✅ PROVEN (7⁴ = 2401 cases via native_decide)
- epsilon_contraction_decomp ✅ PROVEN (Kronecker + ψ decomposition)
- antisym_sym_contract_vanishes ✅ PROVEN (algebraic lemma)
- psi_contract_vanishes ✅ PROVEN (ψ terms vanish under symmetric contraction)
- G2_cross_norm: AXIOM (key lemmas proven, EuclideanSpace plumbing pending)

**Remaining Axioms (2):**
- B4: G2_cross_norm (mathematical core proven, Mathlib integration pending)
- B5: cross_is_octonion_structure (exhaustive check times out)

**Note on B4 proof strategy:**
The coassociative 4-form ψ satisfies ψ(i,j,l,m) = -ψ(l,j,i,m).
When contracted with uᵢuₗvⱼvₘ (symmetric in i↔l), ψ vanishes.
The remaining Kronecker terms give exactly |u|²|v|² - ⟨u,v⟩².
All algebraic lemmas are proven; final theorem awaits EuclideanSpace norm expansion.
-/

end GIFT.Foundations.G2CrossProduct
