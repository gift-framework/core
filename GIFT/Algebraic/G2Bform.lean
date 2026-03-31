/-
G₂ Seven-Form: Proving g2_subset_SO7 and g2_det_one
=====================================================

The seven-form contraction Ω(i,j) = ∑_{σ∈S₇} sgn(σ)·φ(i,σ₀,σ₁)·φ(j,σ₂,σ₃)·φ(σ₄,σ₅,σ₆)
satisfies Ω = 144·δ (verified by native_decide). For a G₂ matrix A (preserving φ₀),
substituting A·φ = φ and expanding gives Ω = det(A)·144·(AᵀA), hence det(A)·(AᵀA) = I.
Then det(A)⁹ = 1, det(A) > 0, so det(A) = 1, and AᵀA = I.
-/
import Mathlib
import GIFT.Algebraic.G2ThreeForm

namespace GIFT.Algebraic.G2Bform

open Finset BigOperators GIFT.Algebraic.G2ThreeForm Matrix

/-!
## The Seven-Form Contraction Ω

Ω(i,j) = ∑_{σ ∈ S₇} sign(σ) · φ₀(i,σ(0),σ(1)) · φ₀(j,σ(2),σ(3)) · φ₀(σ(4),σ(5),σ(6))

This is a 7-form contraction: a degree-7 alternating polynomial identity in 7 basis vectors.
Evaluated on the standard basis, it equals 144·δ_{ij}.
-/

/-- Integer version of Ω for native_decide verification. -/
def OmegaZ (i j : Fin 7) : ℤ :=
  ∑ σ : Equiv.Perm (Fin 7),
    (↑(Equiv.Perm.sign σ) : ℤ) *
    phi0Z i (σ 0) (σ 1) * phi0Z j (σ 2) (σ 3) * phi0Z (σ 4) (σ 5) (σ 6)

/-- **Ω = 144·δ** over ℤ, verified by native_decide. -/
theorem OmegaZ_eq : ∀ i j : Fin 7,
    OmegaZ i j = 144 * if i = j then 1 else 0 := by native_decide

/-- Real-valued Ω. -/
noncomputable def Omega (i j : Fin 7) : ℝ :=
  ∑ σ : Equiv.Perm (Fin 7),
    (↑(Equiv.Perm.sign σ) : ℝ) *
    phi0 i (σ 0) (σ 1) * phi0 j (σ 2) (σ 3) * phi0 (σ 4) (σ 5) (σ 6)

/-- Casting lemma: OmegaZ casts to Omega. -/
theorem Omega_cast (i j : Fin 7) :
    (OmegaZ i j : ℝ) = Omega i j := by
  simp only [OmegaZ, Omega]
  push_cast
  congr 1; ext σ
  rw [← phi0Z_cast, ← phi0Z_cast, ← phi0Z_cast]

/-- **Ω = 144·δ** over ℝ. -/
theorem Omega_eq (i j : Fin 7) :
    Omega i j = 144 * if i = j then (1 : ℝ) else 0 := by
  rw [← Omega_cast]
  rw [OmegaZ_eq]
  push_cast
  split_ifs <;> ring

/-!
## Key Algebraic Identity: Sum over Functions Factors Through det
-/

/-- det of a matrix with repeated rows is zero. -/
theorem det_submatrix_non_injective {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R]
    (A : Matrix n n R) (f : n → n) (hf : ¬Function.Injective f) :
    (A.submatrix f id).det = 0 := by
  obtain ⟨i, j, hij_eq, hij_ne⟩ := Function.not_injective_iff.mp hf
  exact Matrix.det_zero_of_row_eq hij_ne (by ext k; simp [Matrix.submatrix, hij_eq])

/-
PROBLEM
Key factorization: sum over all functions = det(A) · sum over permutations.

PROVIDED SOLUTION
Split the sum over f : n → n into two parts: injective f and non-injective f.

For non-injective f: (A.submatrix f id).det = 0 by det_submatrix_non_injective, so those terms vanish.

For injective f on a finite type: injective implies bijective (Finite.injective_iff_bijective). Convert each injective f to an Equiv.Perm using Equiv.ofBijective. Then det(A.submatrix f id) = sign(f-as-perm) * det(A) by Matrix.det_permute (or det_submatrix_equiv_self combined with det_permute).

Factor out det(A) to get det(A) * ∑_{σ} sign(σ) * c(σ).

Key steps:
1. Use Finset.sum_filter_add_sum_filter_not (or similar) to split by injectivity
2. For non-injective: use det_submatrix_non_injective
3. For injective: use the equivalence between {injective f} and Perm n
4. Use Matrix.det_permute: (A.submatrix σ id).det = sign(σ) * A.det
-/
theorem sum_fun_det_eq_det_mul_sum_perm {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R]
    (A : Matrix n n R) (c : (n → n) → R) :
    ∑ f : n → n, c f * (A.submatrix f id).det =
    A.det * ∑ σ : Equiv.Perm n, (↑(Equiv.Perm.sign σ) : R) * c ↑σ := by
  rw [ Finset.mul_sum, ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun σ : Equiv.Perm n => σ : Equiv.Perm n → n → n ) Finset.univ ) ) ];
  · rw [ Finset.sum_image ];
    · refine' Finset.sum_congr rfl fun σ _ => _;
      simp +decide [ mul_comm, Matrix.det_permute ];
      ring;
    · exact fun σ _ τ _ h => Equiv.Perm.ext fun x => by simpa using congr_fun h x;
  · simp +zetaDelta at *;
    intro x hx
    have h_det_zero : Matrix.det (A.submatrix x id) = 0 := by
      apply det_submatrix_non_injective A x (by
      exact fun h => hx ( Equiv.ofBijective x ⟨ h, Finite.injective_iff_surjective.mp h ⟩ ) rfl)
    rw [h_det_zero]
    simp [hx]

/-!
## Expansion of the A-Transformed Omega
-/

/-- The A-transformed phi0 at (i,j,k). -/
noncomputable def Aphi0 (A : Matrix (Fin 7) (Fin 7) ℝ) (i j k : Fin 7) : ℝ :=
  ∑ a : Fin 7, ∑ b : Fin 7, ∑ c : Fin 7, A a i * A b j * A c k * phi0 a b c

/-- Omega with A-transformed phi0. -/
noncomputable def OmegaA (A : Matrix (Fin 7) (Fin 7) ℝ) (i j : Fin 7) : ℝ :=
  ∑ σ : Equiv.Perm (Fin 7),
    (↑(Equiv.Perm.sign σ) : ℝ) *
    Aphi0 A i (σ 0) (σ 1) * Aphi0 A j (σ 2) (σ 3) * Aphi0 A (σ 4) (σ 5) (σ 6)

/-- For G₂ matrices: OmegaA = Omega (since A preserves phi0). -/
theorem OmegaA_eq_Omega {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : isG2Matrix A)
    (i j : Fin 7) : OmegaA A i j = Omega i j := by
  unfold OmegaA Omega Aphi0
  congr 1; ext σ
  rw [hA i (σ 0) (σ 1), hA j (σ 2) (σ 3), hA (σ 4) (σ 5) (σ 6)]

/-
PROBLEM
The inner sum ∑_σ sign(σ) * ∏_k A(row(k), σ(k)) = det(A.submatrix row id).

PROVIDED SOLUTION
This is essentially the definition of Matrix.det. Matrix.det_apply says det(M) = ∑ σ, sign(σ) * ∏ i, M i (σ i). For M = A.submatrix row id, M i j = A (row i) (id j) = A (row i) j. So det(A.submatrix row id) = ∑ σ, sign(σ) * ∏ k, A (row k) (σ k). Use Matrix.det_apply and funext/congr.
-/
theorem perm_sum_eq_det (A : Matrix (Fin 7) (Fin 7) ℝ) (row : Fin 7 → Fin 7) :
    ∑ σ : Equiv.Perm (Fin 7), (↑(Equiv.Perm.sign σ) : ℝ) *
      ∏ k : Fin 7, A (row k) (σ k) = (A.submatrix row id).det := by
  rw [ ← Matrix.det_transpose, Matrix.det_apply' ];
  rfl

/-
PROBLEM
**Key expansion**: OmegaA factors through det(A) and AᵀA.

  OmegaA(A, i, j) = det(A) · ∑_{a,d} A(a,i) · A(d,j) · Omega(a,d)

PROVIDED SOLUTION
Expand OmegaA by unfolding OmegaA, Aphi0 and rearranging sums. The key steps:

1. Unfold OmegaA and Aphi0 to get:
   ∑_σ sign(σ) * (∑_{a,b,c} A(a,i)*A(b,σ0)*A(c,σ1)*phi0(a,b,c)) * (∑_{d,e,f} A(d,j)*A(e,σ2)*A(f,σ3)*phi0(d,e,f)) * (∑_{g,h,l} A(g,σ4)*A(h,σ5)*A(l,σ6)*phi0(g,h,l))

2. Pull A(a,i) out of the first sum: ∑_a A(a,i) * ∑_{b,c} ...
   Pull A(d,j) out of the second sum: ∑_d A(d,j) * ∑_{e,f} ...

3. Pull ∑_a A(a,i) * and ∑_d A(d,j) * outside the σ-sum.

4. Inside, expand the product of three sums over (b,c), (e,f), (g,h,l).

5. The 7 factors A(b,σ0)*A(c,σ1)*A(e,σ2)*A(f,σ3)*A(g,σ4)*A(h,σ5)*A(l,σ6) = ∏_k A(row(k), σ(k)) where row = ![b,c,e,f,g,h,l].

6. ∑_σ sign(σ) * ∏_k A(row(k), σ(k)) = det(A.submatrix row id) by perm_sum_eq_det.

7. The sum over (b,c,e,f,g,h,l) with det(A.submatrix row id) is ∑_{f : Fin 7 → Fin 7} c(f) * det(A.submatrix f id).

8. Apply sum_fun_det_eq_det_mul_sum_perm to factor out det(A).

9. The remaining sum over permutations gives Omega(a,d).

This is a long chain of sum rearrangements (Finset.sum_comm, Finset.mul_sum, Finset.sum_mul, etc.) and the key identity sum_fun_det_eq_det_mul_sum_perm. The proof should use simp/ring for the algebraic parts and congr/ext for structural parts.
-/
set_option maxHeartbeats 800000 in
theorem OmegaA_expansion (A : Matrix (Fin 7) (Fin 7) ℝ) (i j : Fin 7) :
    OmegaA A i j = A.det * ∑ a : Fin 7, ∑ d : Fin 7,
      A a i * A d j * Omega a d := by
  -- Expand the definition of OmegaA using the given formula.
  have h_expand : OmegaA A i j = ∑ a : Fin 7, ∑ d : Fin 7, A a i * A d j * ∑ σ : Equiv.Perm (Fin 7), (↑(Equiv.Perm.sign σ) : ℝ) * ∑ b : Fin 7, ∑ c : Fin 7, ∑ e : Fin 7, ∑ f : Fin 7, ∑ g : Fin 7, ∑ h : Fin 7, ∑ l : Fin 7, A b (σ 0) * A c (σ 1) * A e (σ 2) * A f (σ 3) * A g (σ 4) * A h (σ 5) * A l (σ 6) * phi0 a b c * phi0 d e f * phi0 g h l := by
    -- By definition of OmegaA, we can expand it using the given formula.
    have h_expand : OmegaA A i j = ∑ σ : Equiv.Perm (Fin 7), (↑(Equiv.Perm.sign σ) : ℝ) * (∑ a : Fin 7, ∑ b : Fin 7, ∑ c : Fin 7, A a i * A b (σ 0) * A c (σ 1) * phi0 a b c) * (∑ d : Fin 7, ∑ e : Fin 7, ∑ f : Fin 7, A d j * A e (σ 2) * A f (σ 3) * phi0 d e f) * (∑ g : Fin 7, ∑ h : Fin 7, ∑ l : Fin 7, A g (σ 4) * A h (σ 5) * A l (σ 6) * phi0 g h l) := by
      exact Finset.sum_congr rfl fun _ _ => by unfold Aphi0; ring;
    simp +decide only [h_expand, Finset.mul_sum _ _ _];
    simp +decide only [← sum_product'];
    simp +decide only [sum_mul];
    simp +decide only [← sum_product'];
    apply Finset.sum_bij (fun x _ => (x.2.2.1, x.2.1.1, x.1.1, x.2.2.2.1, x.2.2.2.2, x.2.1.2.1, x.2.1.2.2, x.1.2.1, x.1.2.2.1, x.1.2.2.2));
    · simp +decide [ Finset.mem_product ];
    · grind +ring;
    · simp +zetaDelta at *;
    · intros; ring!;
  -- Apply the sum_fun_det_eq_det_mul_sum_perm theorem to factor out the determinant of A.
  have h_factor : ∀ a d : Fin 7, ∑ σ : Equiv.Perm (Fin 7), (↑(Equiv.Perm.sign σ) : ℝ) * ∑ b : Fin 7, ∑ c : Fin 7, ∑ e : Fin 7, ∑ f : Fin 7, ∑ g : Fin 7, ∑ h : Fin 7, ∑ l : Fin 7, A b (σ 0) * A c (σ 1) * A e (σ 2) * A f (σ 3) * A g (σ 4) * A h (σ 5) * A l (σ 6) * phi0 a b c * phi0 d e f * phi0 g h l = A.det * ∑ σ : Equiv.Perm (Fin 7), (↑(Equiv.Perm.sign σ) : ℝ) * phi0 a (σ 0) (σ 1) * phi0 d (σ 2) (σ 3) * phi0 (σ 4) (σ 5) (σ 6) := by
    intro a d
    have h_factor : ∑ σ : Equiv.Perm (Fin 7), (↑(Equiv.Perm.sign σ) : ℝ) * ∑ b : Fin 7, ∑ c : Fin 7, ∑ e : Fin 7, ∑ f : Fin 7, ∑ g : Fin 7, ∑ h : Fin 7, ∑ l : Fin 7, A b (σ 0) * A c (σ 1) * A e (σ 2) * A f (σ 3) * A g (σ 4) * A h (σ 5) * A l (σ 6) * phi0 a b c * phi0 d e f * phi0 g h l = ∑ f : Fin 7 → Fin 7, (∑ σ : Equiv.Perm (Fin 7), (↑(Equiv.Perm.sign σ) : ℝ) * ∏ k : Fin 7, A (f k) (σ k)) * (phi0 a (f 0) (f 1)) * (phi0 d (f 2) (f 3)) * (phi0 (f 4) (f 5) (f 6)) := by
      simp +decide only [Fin.prod_univ_seven, sum_mul];
      simp +decide only [mul_assoc, sum_sigma', Finset.mul_sum _ _ _];
      apply Finset.sum_bij (fun x _ => ⟨![x.snd.fst, x.snd.snd.fst, x.snd.snd.snd.fst, x.snd.snd.snd.snd.fst, x.snd.snd.snd.snd.snd.fst, x.snd.snd.snd.snd.snd.snd.fst, x.snd.snd.snd.snd.snd.snd.snd], x.fst⟩);
      · grind +revert;
      · simp +contextual [ funext_iff, Fin.forall_fin_succ ];
        bound;
      · simp +zetaDelta at *;
        rintro ⟨ f, σ ⟩ ; use σ ; use f 0 ; use f 1 ; use f 2 ; use f 3 ; use f 4 ; use f 5 ; use f 6 ; simp +decide [ ← List.ofFn_inj ] ;
      · simp +decide [ Fin.forall_fin_succ ] at * <;> first | linarith | aesop | assumption;
    rw [ h_factor, Finset.mul_sum ];
    have h_factor : ∀ f : Fin 7 → Fin 7, (∑ σ : Equiv.Perm (Fin 7), (↑(Equiv.Perm.sign σ) : ℝ) * ∏ k : Fin 7, A (f k) (σ k)) = (A.submatrix f id).det := by
      intro f
      rw [Matrix.det_apply'];
      simp +decide [ Matrix.submatrix ];
      apply Finset.sum_bij (fun σ _ => σ⁻¹);
      · grind;
      · exact fun σ _ τ _ h => inv_injective h;
      · exact fun b _ => ⟨ b⁻¹, Finset.mem_univ _, inv_inv b ⟩;
      · intro σ _; rw [ ← Equiv.prod_comp σ⁻¹ ] ; simp +decide [ Equiv.Perm.sign_inv ] ;
    simp +decide only [h_factor, mul_assoc];
    convert sum_fun_det_eq_det_mul_sum_perm A ( fun f => phi0 a ( f 0 ) ( f 1 ) * ( phi0 d ( f 2 ) ( f 3 ) * phi0 ( f 4 ) ( f 5 ) ( f 6 ) ) ) using 1 ; ring!;
    · ac_rfl;
    · rw [ Finset.mul_sum _ _ _ ];
  simp +decide only [h_expand, Finset.mul_sum _ _ _];
  refine' Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => _;
  convert congr_arg ( fun x : ℝ => A a i * A b j * x ) ( h_factor a b ) using 1 <;> ring!;
  simp +decide only [mul_assoc, Finset.mul_sum _ _ _]

/-!
## Main Theorems
-/

/-
PROBLEM
Auxiliary: ∑_{a,d} A(a,i) · A(d,j) · Omega(a,d) = 144 · (AᵀA)_{ij}.

PROVIDED SOLUTION
Expand Omega using Omega_eq: Omega a d = 144 * (if a = d then 1 else 0). So the sum becomes ∑ a d, A a i * A d j * 144 * (if a = d then 1 else 0). The inner sum over d collapses to d = a, giving ∑ a, A a i * A a j * 144. Factor out 144 to get 144 * ∑ a, A a i * A a j = 144 * (Aᵀ * A) i j, since (Aᵀ * A) i j = ∑ a, A a i * A a j by definition of transpose and matrix multiplication.
-/
private theorem sum_Omega_eq_gram (A : Matrix (Fin 7) (Fin 7) ℝ) (i j : Fin 7) :
    ∑ a : Fin 7, ∑ d : Fin 7, A a i * A d j * Omega a d =
    144 * (A.transpose * A) i j := by
  -- Substitute the definition of `Omega` from `Omega_eq`.
  have h_subst : ∀ a d, Omega a d = 144 * if a = d then 1 else 0 := by
    exact fun a d => Omega_eq a d
  simp +decide [ h_subst, Matrix.mul_apply, Finset.mul_sum _ _ _ ] ; ring_nf

/-- **KEY LEMMA**: det(A)·(AᵀA)ᵢⱼ = δᵢⱼ for G₂ matrices. -/
theorem g2_det_mul_gram {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : isG2Matrix A) :
    ∀ i j : Fin 7, A.det * (A.transpose * A) i j = if i = j then 1 else 0 := by
  intro i j
  have hExpand : Omega i j = A.det * ∑ a : Fin 7, ∑ d : Fin 7,
      A a i * A d j * Omega a d := by
    rw [← OmegaA_eq_Omega hA]
    exact OmegaA_expansion A i j
  rw [Omega_eq, sum_Omega_eq_gram] at hExpand
  -- hExpand : 144 * (if i=j then 1 else 0) = A.det * (144 * (AᵀA)_{ij})
  have h144 : (144 : ℝ) ≠ 0 := by norm_num
  have := mul_right_cancel₀ h144 (by linarith : A.det * (A.transpose * A) i j * 144 =
    (if i = j then (1 : ℝ) else 0) * 144)
  linarith

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
  simp [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
        Fintype.card_fin] at h2
  nlinarith [h2]

/-
PROBLEM
det(A) = 1 for G₂ matrices.

PROVIDED SOLUTION
From g2_det_pow9: A.det ^ 9 = 1. From g2_det_ne_zero: A.det ≠ 0. Since A.det ^ 8 ≥ 0 (even power of a real number), and A.det ^ 9 = A.det ^ 8 * A.det = 1 > 0, we get A.det > 0. Now use the fact that x > 0 and x^9 = 1 implies x = 1: if x > 1 then x^9 > 1; if 0 < x < 1 then x^9 < 1. More precisely: x^9 = 1 and x > 0 means x = 1 (by strict monotonicity of x^9 on (0,∞)). Use nlinarith or pow_left_injective or similar.
-/
theorem g2_det_eq_one {A : Matrix (Fin 7) (Fin 7) ℝ} (hA : isG2Matrix A) :
    A.det = 1 := by
  have h_det_pos : 0 < A.det := by
    exact lt_of_le_of_ne ( by exact le_of_not_gt fun h => by have := g2_det_pow9 hA; nlinarith [ pow_pos ( neg_pos.mpr h ) 8 ] ) ( Ne.symm <| g2_det_ne_zero hA );
  exact ( by have := g2_det_pow9 hA; nlinarith [ pow_pos h_det_pos 2, pow_pos h_det_pos 3, pow_pos h_det_pos 4, pow_pos h_det_pos 5, pow_pos h_det_pos 6, pow_pos h_det_pos 7, pow_pos h_det_pos 8 ] )

/-- **G₂ ⊆ SO(7)**: AᵀA = I for G₂ matrices. -/
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