-- GIFT Foundations: Numerical Bounds
-- Axiom-free proofs of transcendental function bounds
--
-- This file provides proven bounds using Mathlib's certified decimal bounds.
-- It replaces/supplements axioms in DimensionalGap.lean and GoldenRatioPowers.lean.
--
-- INCREMENT 1: Basic exp(1) bounds from Mathlib.Analysis.Complex.ExponentialBounds

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import GIFT.Foundations.GoldenRatio

namespace GIFT.Foundations.NumericalBounds

open Real

/-!
## Section 1: Bounds on e = exp(1)

Using Mathlib's certified bounds:
- Real.exp_one_gt_d9 : 2.7182818283 < exp 1
- Real.exp_one_lt_d9 : exp 1 < 2.7182818286
-/

/-- e > 2.7. Proven from Mathlib's Real.exp_one_gt_d9. -/
theorem exp_one_gt : (27 : ℝ) / 10 < exp 1 := by
  have h := Real.exp_one_gt_d9  -- 2.7182818283 < exp 1
  linarith

/-- e < 2.72. Proven from Mathlib's Real.exp_one_lt_d9. -/
theorem exp_one_lt : exp 1 < (272 : ℝ) / 100 := by
  have h := Real.exp_one_lt_d9  -- exp 1 < 2.7182818286
  linarith

/-- Combined bounds: 2.7 < e < 2.72 -/
theorem exp_one_bounds : (27 : ℝ) / 10 < exp 1 ∧ exp 1 < (272 : ℝ) / 100 :=
  ⟨exp_one_gt, exp_one_lt⟩

/-!
## Section 2: sqrt(5) bounds (algebraic, no transcendentals)

These are proven purely via squaring inequalities.
-/

/-- sqrt(5) > 2 -/
theorem sqrt5_gt_two : 2 < sqrt 5 := by
  have h : (2 : ℝ)^2 < 5 := by norm_num
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [← sqrt_sq h2]
  exact sqrt_lt_sqrt (by norm_num) h

/-- sqrt(5) < 3 -/
theorem sqrt5_lt_three : sqrt 5 < 3 := by
  have h : (5 : ℝ) < 3^2 := by norm_num
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  rw [← sqrt_sq h3]
  exact sqrt_lt_sqrt (by norm_num) h

/-- sqrt(5) bounds: 2.236 < sqrt(5) < 2.237 -/
theorem sqrt5_bounds_tight : (2236 : ℝ) / 1000 < sqrt 5 ∧ sqrt 5 < (2237 : ℝ) / 1000 := by
  constructor
  · -- 2.236 < sqrt(5) because 2.236^2 = 4.999696 < 5
    have h : ((2236 : ℝ) / 1000)^2 < 5 := by norm_num
    have hpos : (0 : ℝ) ≤ 2236 / 1000 := by norm_num
    rw [← sqrt_sq hpos]
    exact sqrt_lt_sqrt (by norm_num) h
  · -- sqrt(5) < 2.237 because 5 < 2.237^2 = 5.004169
    have h : (5 : ℝ) < ((2237 : ℝ) / 1000)^2 := by norm_num
    have hpos : (0 : ℝ) ≤ 2237 / 1000 := by norm_num
    rw [← sqrt_sq hpos]
    exact sqrt_lt_sqrt (by norm_num) h

/-- Even tighter: 2.2360 < sqrt(5) < 2.2361 -/
theorem sqrt5_bounds_4dec : (22360 : ℝ) / 10000 < sqrt 5 ∧ sqrt 5 < (22361 : ℝ) / 10000 := by
  constructor
  · -- 2.2360^2 = 4.99969600 < 5
    have h : ((22360 : ℝ) / 10000)^2 < 5 := by norm_num
    have hpos : (0 : ℝ) ≤ 22360 / 10000 := by norm_num
    rw [← sqrt_sq hpos]
    exact sqrt_lt_sqrt (by norm_num) h
  · -- 5 < 2.2361^2 = 5.00014321
    have h : (5 : ℝ) < ((22361 : ℝ) / 10000)^2 := by norm_num
    have hpos : (0 : ℝ) ≤ 22361 / 10000 := by norm_num
    rw [← sqrt_sq hpos]
    exact sqrt_lt_sqrt (by norm_num) h

/-!
## Section 3: Golden ratio phi bounds

phi = (1 + sqrt(5))/2
Using sqrt5_bounds, we can derive phi bounds.
-/

-- Import phi definition
open GIFT.Foundations.GoldenRatio in
/-- phi > 1.618 -/
theorem phi_gt_1618 : (1618 : ℝ) / 1000 < GIFT.Foundations.GoldenRatio.phi := by
  unfold GIFT.Foundations.GoldenRatio.phi
  have h := sqrt5_bounds_tight.1  -- 2.236 < sqrt(5)
  linarith

open GIFT.Foundations.GoldenRatio in
/-- phi < 1.6185 -/
theorem phi_lt_16185 : GIFT.Foundations.GoldenRatio.phi < (16185 : ℝ) / 10000 := by
  unfold GIFT.Foundations.GoldenRatio.phi
  have h := sqrt5_bounds_tight.2  -- sqrt(5) < 2.237
  linarith

open GIFT.Foundations.GoldenRatio in
/-- phi bounds: 1.618 < phi < 1.6185 -/
theorem phi_bounds : (1618 : ℝ) / 1000 < GIFT.Foundations.GoldenRatio.phi ∧
    GIFT.Foundations.GoldenRatio.phi < (16185 : ℝ) / 10000 :=
  ⟨phi_gt_1618, phi_lt_16185⟩

open GIFT.Foundations.GoldenRatio in
/-- phi is positive -/
theorem phi_pos : 0 < GIFT.Foundations.GoldenRatio.phi := by
  unfold GIFT.Foundations.GoldenRatio.phi
  have h := sqrt5_gt_two
  linarith

open GIFT.Foundations.GoldenRatio in
/-- phi > 1 -/
theorem phi_gt_one : 1 < GIFT.Foundations.GoldenRatio.phi := by
  have h := phi_gt_1618
  linarith

open GIFT.Foundations.GoldenRatio in
/-- phi < 2 -/
theorem phi_lt_two : GIFT.Foundations.GoldenRatio.phi < 2 := by
  have h := phi_lt_16185
  linarith

open GIFT.Foundations.GoldenRatio in
/-- phi is nonzero -/
theorem phi_ne_zero : GIFT.Foundations.GoldenRatio.phi ≠ 0 :=
  ne_of_gt phi_pos

/-!
## Section 4: phi^(-2) bounds

phi^(-2) = 2 - phi (algebraic identity)
Using phi bounds, we get phi^(-2) bounds.
-/

/-- phi^(-2) = 2 - phi. Algebraic identity from phi^2 = phi + 1. -/
theorem phi_inv_sq_eq : GIFT.Foundations.GoldenRatio.phi⁻¹ ^ 2 = 2 - GIFT.Foundations.GoldenRatio.phi := by
  have hne : GIFT.Foundations.GoldenRatio.phi ≠ 0 := phi_ne_zero
  have hsq : GIFT.Foundations.GoldenRatio.phi ^ 2 = GIFT.Foundations.GoldenRatio.phi + 1 :=
    GIFT.Foundations.GoldenRatio.phi_squared
  -- phi^(-1) = phi - 1 (from phi^2 = phi + 1, multiply both sides by phi^(-1))
  have hinv : GIFT.Foundations.GoldenRatio.phi⁻¹ = GIFT.Foundations.GoldenRatio.phi - 1 := by
    have hmul : GIFT.Foundations.GoldenRatio.phi * (GIFT.Foundations.GoldenRatio.phi - 1) = 1 := by
      calc GIFT.Foundations.GoldenRatio.phi * (GIFT.Foundations.GoldenRatio.phi - 1)
          = GIFT.Foundations.GoldenRatio.phi^2 - GIFT.Foundations.GoldenRatio.phi := by ring
        _ = (GIFT.Foundations.GoldenRatio.phi + 1) - GIFT.Foundations.GoldenRatio.phi := by rw [hsq]
        _ = 1 := by ring
    field_simp
    linarith
  rw [hinv]
  calc (GIFT.Foundations.GoldenRatio.phi - 1) ^ 2
      = GIFT.Foundations.GoldenRatio.phi^2 - 2*GIFT.Foundations.GoldenRatio.phi + 1 := by ring
    _ = (GIFT.Foundations.GoldenRatio.phi + 1) - 2*GIFT.Foundations.GoldenRatio.phi + 1 := by rw [hsq]
    _ = 2 - GIFT.Foundations.GoldenRatio.phi := by ring

/-- phi^(-2) > 0 -/
theorem phi_inv_sq_pos : 0 < GIFT.Foundations.GoldenRatio.phi⁻¹ ^ 2 := by
  apply pow_pos
  rw [inv_pos]
  exact phi_pos

/-- phi^(-2) < 0.383 -/
theorem phi_inv_sq_lt_0383 : GIFT.Foundations.GoldenRatio.phi⁻¹ ^ 2 < (383 : ℝ) / 1000 := by
  rw [phi_inv_sq_eq]
  have h := phi_gt_1618
  linarith

/-- phi^(-2) > 0.381 -/
theorem phi_inv_sq_gt_0381 : (381 : ℝ) / 1000 < GIFT.Foundations.GoldenRatio.phi⁻¹ ^ 2 := by
  rw [phi_inv_sq_eq]
  have h := phi_lt_16185
  linarith

/-- phi^(-2) bounds: 0.381 < phi^(-2) < 0.383 -/
theorem phi_inv_sq_bounds : (381 : ℝ) / 1000 < GIFT.Foundations.GoldenRatio.phi⁻¹ ^ 2 ∧
    GIFT.Foundations.GoldenRatio.phi⁻¹ ^ 2 < (383 : ℝ) / 1000 :=
  ⟨phi_inv_sq_gt_0381, phi_inv_sq_lt_0383⟩

/-- phi^(-2) < 1 (it's a contraction) -/
theorem phi_inv_sq_lt_one : GIFT.Foundations.GoldenRatio.phi⁻¹ ^ 2 < 1 := by
  have h := phi_inv_sq_lt_0383
  linarith

/-!
## Section 5: Logarithm bounds from Mathlib

Mathlib provides:
- Real.log_two_gt_d9 : 0.6931471803 < log 2
- Real.log_two_lt_d9 : log 2 < 0.6931471807

We can derive bounds on log(10) = log(2) + log(5) if we have log(5) bounds.
-/

/-- log(2) > 0.693 (from Mathlib's 9-decimal precision) -/
theorem log_two_gt : (693 : ℝ) / 1000 < log 2 := by
  have h := Real.log_two_gt_d9  -- 0.6931471803 < log 2
  linarith

/-- log(2) < 0.694 -/
theorem log_two_lt : log 2 < (694 : ℝ) / 1000 := by
  have h := Real.log_two_lt_d9  -- log 2 < 0.6931471807
  linarith

/-- log(2) bounds: 0.693 < log(2) < 0.694 -/
theorem log_two_bounds : (693 : ℝ) / 1000 < log 2 ∧ log 2 < (694 : ℝ) / 1000 :=
  ⟨log_two_gt, log_two_lt⟩

/-- log(4) = 2 * log(2) -/
theorem log_four_eq : log 4 = 2 * log 2 := by
  have h : (4 : ℝ) = 2^2 := by norm_num
  rw [h, log_pow]
  norm_cast

/-- log(4) bounds: 1.386 < log(4) < 1.388 -/
theorem log_four_bounds : (1386 : ℝ) / 1000 < log 4 ∧ log 4 < (1388 : ℝ) / 1000 := by
  rw [log_four_eq]
  have ⟨hlo, hhi⟩ := log_two_bounds
  constructor <;> linarith

/-- log(8) = 3 * log(2) -/
theorem log_eight_eq : log 8 = 3 * log 2 := by
  have h : (8 : ℝ) = 2^3 := by norm_num
  rw [h, log_pow]
  norm_cast

/-- log(5) lower bound: log(5) > log(4) = 2*log(2) > 1.386 -/
theorem log_five_gt : (1386 : ℝ) / 1000 < log 5 := by
  have h4 : log 4 < log 5 := log_lt_log (by norm_num) (by norm_num : (4 : ℝ) < 5)
  have h := log_four_bounds.1
  linarith

/-- log(5) upper bound: log(5) < log(8) = 3*log(2) < 2.082 -/
theorem log_five_lt : log 5 < (2082 : ℝ) / 1000 := by
  have h8 : log 5 < log 8 := log_lt_log (by norm_num) (by norm_num : (5 : ℝ) < 8)
  rw [log_eight_eq] at h8
  have h := log_two_lt
  linarith

/-- log(10) = log(2) + log(5) -/
theorem log_ten_eq : log 10 = log 2 + log 5 := by
  have h : (10 : ℝ) = 2 * 5 := by norm_num
  rw [h, log_mul (by norm_num) (by norm_num)]

/-- log(10) lower bound (loose): log(10) > 2.079 -/
theorem log_ten_gt_loose : (2079 : ℝ) / 1000 < log 10 := by
  rw [log_ten_eq]
  have h2 := log_two_gt
  have h5 := log_five_gt
  linarith

/-- log(10) upper bound (loose): log(10) < 2.776 -/
theorem log_ten_lt_loose : log 10 < (2776 : ℝ) / 1000 := by
  rw [log_ten_eq]
  have h2 := log_two_lt
  have h5 := log_five_lt
  linarith

/-!
## Section 6: log(3) bounds via monotonicity

We have: 2 < 3 < 4
So: log(2) < log(3) < log(4) = 2*log(2)
-/

/-- log(3) > log(2) > 0.693 -/
theorem log_three_gt : (693 : ℝ) / 1000 < log 3 := by
  have h23 : log 2 < log 3 := log_lt_log (by norm_num) (by norm_num : (2 : ℝ) < 3)
  have h2 := log_two_gt
  linarith

/-- log(3) < log(4) = 2*log(2) < 1.388 -/
theorem log_three_lt : log 3 < (1388 : ℝ) / 1000 := by
  have h34 : log 3 < log 4 := log_lt_log (by norm_num) (by norm_num : (3 : ℝ) < 4)
  have h4 := log_four_bounds.2
  linarith

/-- log(3) bounds: 0.693 < log(3) < 1.388.
    Note: The actual value is log(3) ≈ 1.0986, so these are loose bounds.
    We'll tighten them using intermediate values. -/
theorem log_three_bounds_loose : (693 : ℝ) / 1000 < log 3 ∧ log 3 < (1388 : ℝ) / 1000 :=
  ⟨log_three_gt, log_three_lt⟩

/-!
## Section 7: Tighter log(3) bounds via exp monotonicity

To get tighter bounds on log(3), we use:
- If exp(a) < 3, then a < log(3)
- If 3 < exp(b), then log(3) < b

From Mathlib's exp bounds:
- exp(1) ≈ 2.718 < 3, so 1 < log(3)
- We need exp(1.1) > 3 or similar for upper bound
-/

/-- log(3) > 1 since exp(1) < 3 -/
theorem log_three_gt_one : 1 < log 3 := by
  rw [← exp_lt_exp, exp_log (by norm_num : (0 : ℝ) < 3)]
  -- Need: exp(1) < 3
  have he := exp_one_lt  -- exp(1) < 2.72
  linarith

/-!
## Section 8: log(1+√5) bounds

√5 ∈ (2.236, 2.237) implies 1+√5 ∈ (3.236, 3.237)
Since 3 < 3.236 and 3.237 < 4:
  log(3) < log(3.236) < log(1+√5) < log(3.237) < log(4)
-/

/-- 1 + √5 > 3.236 -/
theorem one_plus_sqrt5_gt : (3236 : ℝ) / 1000 < 1 + sqrt 5 := by
  have h := sqrt5_bounds_tight.1  -- 2.236 < √5
  linarith

/-- 1 + √5 < 3.237 -/
theorem one_plus_sqrt5_lt : 1 + sqrt 5 < (3237 : ℝ) / 1000 := by
  have h := sqrt5_bounds_tight.2  -- √5 < 2.237
  linarith

/-- log(1+√5) > log(3) > 1 -/
theorem log_one_plus_sqrt5_gt : 1 < log (1 + sqrt 5) := by
  have h1 : log 3 < log (1 + sqrt 5) := by
    apply log_lt_log (by norm_num)
    have hsqrt := sqrt5_bounds_tight.1
    linarith
  have h2 := log_three_gt_one
  linarith

/-- log(1+√5) < log(4) < 1.388 -/
theorem log_one_plus_sqrt5_lt : log (1 + sqrt 5) < (1388 : ℝ) / 1000 := by
  have h1 : log (1 + sqrt 5) < log 4 := by
    apply log_lt_log
    · have hsqrt := sqrt5_gt_two; linarith
    · have hsqrt := sqrt5_bounds_tight.2; linarith
  have h2 := log_four_bounds.2
  linarith

/-!
## Section 9: log(φ) bounds - THE KEY RESULT

φ = (1 + √5)/2
log(φ) = log((1+√5)/2) = log(1+√5) - log(2)

With:
- 1 < log(1+√5) < 1.388
- 0.693 < log(2) < 0.694

We get:
- log(φ) > 1 - 0.694 = 0.306 (too loose!)
- log(φ) < 1.388 - 0.693 = 0.695 (too loose!)

Need tighter bounds. Use:
- log(1+√5) > log(3.236) and we need log(3.236) > 1.17...
- This requires tighter log(3) or direct computation

Alternative approach: Use exp bounds on φ directly.
φ ∈ (1.618, 1.6185), so we need:
- exp(0.48) < 1.618 to prove log(φ) > 0.48
- exp(0.49) > 1.6185 to prove log(φ) < 0.49
-/

/-- log(φ) = log(1+√5) - log(2) -/
theorem log_phi_eq : log GIFT.Foundations.GoldenRatio.phi = log (1 + sqrt 5) - log 2 := by
  unfold GIFT.Foundations.GoldenRatio.phi
  rw [log_div (by have h := sqrt5_gt_two; linarith) (by norm_num)]

/-- log(φ) > 0 since φ > 1 -/
theorem log_phi_pos : 0 < log GIFT.Foundations.GoldenRatio.phi :=
  Real.log_pos phi_gt_one

/-- log(φ) < 1 since φ < e -/
theorem log_phi_lt_one : log GIFT.Foundations.GoldenRatio.phi < 1 := by
  rw [← exp_lt_exp, exp_log phi_pos]
  have hphi := phi_lt_16185
  have he := exp_one_gt  -- 2.7 < e
  linarith

/-!
## Section 10: Tight log(φ) bounds via Taylor series

Using Real.sum_le_exp_of_nonneg from Mathlib:
For x ≥ 0: Σₖ₌₀ⁿ⁻¹ xᵏ/k! ≤ exp(x)

For log(φ) > 0.48, we need exp(0.48) < φ = 1.618...
For log(φ) < 0.49, we need φ < exp(0.49)

We use that exp is monotonic and bounded by Taylor sums.
-/

/-- exp(0.48) < 1.617.
    Using exp_one_lt and monotonicity: exp(0.48) < exp(0.5) < exp(1) < 2.72
    But 2.72 > 1.617, so we need the Taylor lower bound on φ instead.
    Since φ > 1.618 > 1.617, we just need exp(0.48) < 1.618.

    Alternative: 5-term Taylor sum at 0.48 is approximately 1.6158,
    and exp(0.48) < sum + error < 1.6162 < 1.617 -/
theorem exp_048_lt : exp ((48 : ℝ) / 100) < (1617 : ℝ) / 1000 := by
  -- We use the Taylor upper bound: exp(x) ≤ sum + error term
  -- For x = 0.48, the 5-term sum is about 1.6158 and error < 0.0003
  -- So exp(0.48) < 1.6162 < 1.617
  have hx : |((48 : ℝ) / 100)| ≤ 1 := by norm_num
  have hn : (0 : ℕ) < 5 := by norm_num
  have hbound := Real.exp_bound hx hn
  -- exp_bound gives: |exp x - sum| ≤ |x|^n * (n.succ / (n! * n))
  -- For upper bound: exp x ≤ sum + error
  -- sum = 1 + 0.48 + 0.48²/2 + 0.48³/6 + 0.48⁴/24 ≈ 1.6158
  -- error = 0.48^5 * 6/(120*5) ≈ 0.000255
  -- So exp(0.48) < 1.6161 < 1.617

  -- Expand the sum to its explicit value
  have hsum : (Finset.range 5).sum (fun m => ((48 : ℝ)/100)^m / ↑(m.factorial))
              = 1 + 48/100 + (48/100)^2/2 + (48/100)^3/6 + (48/100)^4/24 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
               Nat.factorial, Nat.cast_one, pow_zero, pow_one]
    ring

  -- Error term computation
  have herr_eq : |((48 : ℝ)/100)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5))
                 = (48/100)^5 * (6 / 600) := by
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    norm_num

  -- Combined bound value
  have hval : 1 + 48/100 + (48/100)^2/2 + (48/100)^3/6 + (48/100)^4/24 + (48/100)^5 * (6/600)
              < (1617 : ℝ) / 1000 := by norm_num

  -- From |exp x - sum| ≤ err, we get exp x ≤ sum + err
  have h := abs_sub_le_iff.mp hbound
  have hupper : exp (48/100) ≤ (Finset.range 5).sum (fun m => ((48 : ℝ)/100)^m / ↑(m.factorial)) +
                               |((48 : ℝ)/100)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := by
    linarith [h.1]

  -- Now combine everything
  calc exp (48/100)
      ≤ (Finset.range 5).sum (fun m => ((48 : ℝ)/100)^m / ↑(m.factorial)) +
        |((48 : ℝ)/100)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := hupper
    _ = 1 + 48/100 + (48/100)^2/2 + (48/100)^3/6 + (48/100)^4/24 + (48/100)^5 * (6/600) := by
        rw [hsum, herr_eq]
    _ < 1617/1000 := hval

/-- exp(0.49) > 1.631 using Taylor lower bound.
    Taylor sum gives lower bound since all terms are positive for x > 0 -/
theorem exp_049_gt : (1631 : ℝ) / 1000 < exp ((49 : ℝ) / 100) := by
  -- For x ≥ 0, exp(x) ≥ partial sum (Real.sum_le_exp_of_nonneg)
  have hpos : (0 : ℝ) ≤ 49/100 := by norm_num

  -- Expand the sum to its explicit value
  have hsum : (Finset.range 5).sum (fun m => ((49 : ℝ)/100)^m / ↑(m.factorial))
              = 1 + 49/100 + (49/100)^2/2 + (49/100)^3/6 + (49/100)^4/24 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
               Nat.factorial, Nat.cast_one, pow_zero, pow_one]
    ring

  have hval : (1631 : ℝ) / 1000 < 1 + 49/100 + (49/100)^2/2 + (49/100)^3/6 + (49/100)^4/24 := by
    norm_num

  calc (1631 : ℝ) / 1000
      < 1 + 49/100 + (49/100)^2/2 + (49/100)^3/6 + (49/100)^4/24 := hval
    _ = (Finset.range 5).sum (fun m => ((49 : ℝ)/100)^m / ↑(m.factorial)) := hsum.symm
    _ ≤ exp (49/100) := Real.sum_le_exp_of_nonneg hpos 5

/-- log(φ) > 0.48. PROVEN via Taylor bounds on exp. -/
theorem log_phi_gt_048 : (48 : ℝ) / 100 < log GIFT.Foundations.GoldenRatio.phi := by
  rw [← exp_lt_exp, exp_log phi_pos]
  calc exp (48/100)
      < 1617/1000 := exp_048_lt
    _ < 1618/1000 := by norm_num
    _ < GIFT.Foundations.GoldenRatio.phi := phi_gt_1618

/-- log(φ) < 0.49. PROVEN via Taylor bounds on exp. -/
theorem log_phi_lt_049 : log GIFT.Foundations.GoldenRatio.phi < (49 : ℝ) / 100 := by
  rw [← exp_lt_exp, exp_log phi_pos]
  calc GIFT.Foundations.GoldenRatio.phi
      < 16185/10000 := phi_lt_16185
    _ < 1631/1000 := by norm_num
    _ < exp (49/100) := exp_049_gt

/-- log(φ) bounds: 0.48 < log(φ) < 0.49. PROVEN! -/
theorem log_phi_bounds : (48 : ℝ) / 100 < log GIFT.Foundations.GoldenRatio.phi ∧
    log GIFT.Foundations.GoldenRatio.phi < (49 : ℝ) / 100 :=
  ⟨log_phi_gt_048, log_phi_lt_049⟩

/-!
## Section 11: Tighter log(5) bounds via Taylor series

We need: 1.6 < log(5) < 1.7
Proof:
- exp(1.6) < 5 implies log(5) > 1.6
- exp(1.7) > 5 implies log(5) < 1.7
-/

/-- exp(1.6) < 5 using Taylor upper bound. -/
theorem exp_16_lt_5 : exp ((16 : ℝ) / 10) < 5 := by
  have hx : |((16 : ℝ) / 10)| ≤ 2 := by norm_num
  -- Use that exp(1.6) = exp(1) * exp(0.6) and bound both
  -- Actually, let's use direct Taylor series at x = 1.6 with n = 8 for precision
  -- exp(1.6) ≈ 4.953 < 5
  -- Use exp composition: exp(1.6) = exp(0.8)²
  -- exp(1.6) = exp(0.8 + 0.8) = exp(0.8)²
  -- exp(0.8) can be bounded by Taylor series
  have h08_bound : exp ((8 : ℝ) / 10) < (223 : ℝ) / 100 := by
    have hx : |((8 : ℝ) / 10)| ≤ 1 := by norm_num
    have hn : (0 : ℕ) < 5 := by norm_num
    have hbound := Real.exp_bound hx hn
    have hsum : (Finset.range 5).sum (fun m => ((8 : ℝ)/10)^m / ↑(m.factorial))
                = 1 + 8/10 + (8/10)^2/2 + (8/10)^3/6 + (8/10)^4/24 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
                 Nat.factorial, Nat.cast_one, pow_zero, pow_one]
      ring
    have herr_eq : |((8 : ℝ)/10)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5))
                   = (8/10)^5 * (6 / 600) := by
      simp only [Nat.factorial, Nat.succ_eq_add_one]
      norm_num
    have hval : 1 + 8/10 + (8/10)^2/2 + (8/10)^3/6 + (8/10)^4/24 + (8/10)^5 * (6/600)
                < (223 : ℝ) / 100 := by norm_num
    have h := abs_sub_le_iff.mp hbound
    have hupper : exp (8/10) ≤ (Finset.range 5).sum (fun m => ((8 : ℝ)/10)^m / ↑(m.factorial)) +
                                 |((8 : ℝ)/10)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := by
      linarith [h.1]
    calc exp (8/10)
        ≤ (Finset.range 5).sum (fun m => ((8 : ℝ)/10)^m / ↑(m.factorial)) +
          |((8 : ℝ)/10)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := hupper
      _ = 1 + 8/10 + (8/10)^2/2 + (8/10)^3/6 + (8/10)^4/24 + (8/10)^5 * (6/600) := by
          rw [hsum, herr_eq]
      _ < 223/100 := hval

  -- Now exp(1.6) = exp(0.8)² < 2.23² = 4.9729 < 5
  have hsq : (223 : ℝ) / 100 * (223 / 100) < 5 := by norm_num
  calc exp (16/10)
      = exp (8/10 + 8/10) := by ring_nf
    _ = exp (8/10) * exp (8/10) := by rw [exp_add]
    _ < (223/100) * (223/100) := by nlinarith [exp_pos (8/10 : ℝ), h08_bound]
    _ < 5 := hsq

/-- exp(1.7) > 5 using Taylor lower bound. -/
theorem exp_17_gt_5 : 5 < exp ((17 : ℝ) / 10) := by
  -- exp(1.7) = exp(0.85)² and exp(0.85) > 2.24 (since 2.24² = 5.0176 > 5)
  -- Taylor sum for exp(0.85) ≈ 2.3354 > 2.24 ✓
  have h085_bound : (224 : ℝ) / 100 < exp ((85 : ℝ) / 100) := by
    have hpos : (0 : ℝ) ≤ 85/100 := by norm_num
    have hsum : (Finset.range 5).sum (fun m => ((85 : ℝ)/100)^m / ↑(m.factorial))
                = 1 + 85/100 + (85/100)^2/2 + (85/100)^3/6 + (85/100)^4/24 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
                 Nat.factorial, Nat.cast_one, pow_zero, pow_one]
      ring
    have hval : (224 : ℝ) / 100 < 1 + 85/100 + (85/100)^2/2 + (85/100)^3/6 + (85/100)^4/24 := by
      norm_num
    calc (224 : ℝ) / 100
        < 1 + 85/100 + (85/100)^2/2 + (85/100)^3/6 + (85/100)^4/24 := hval
      _ = (Finset.range 5).sum (fun m => ((85 : ℝ)/100)^m / ↑(m.factorial)) := hsum.symm
      _ ≤ exp (85/100) := Real.sum_le_exp_of_nonneg hpos 5

  -- Now exp(1.7) = exp(0.85)² > 2.24² = 5.0176 > 5
  have hsq : 5 < (224 : ℝ) / 100 * (224 / 100) := by norm_num
  calc 5
      < (224/100) * (224/100) := hsq
    _ < exp (85/100) * exp (85/100) := by nlinarith [exp_pos (85/100 : ℝ), h085_bound]
    _ = exp (85/100 + 85/100) := by rw [exp_add]
    _ = exp (17/10) := by ring_nf

/-- log(5) > 1.6 since exp(1.6) < 5 -/
theorem log_five_gt_16 : (16 : ℝ) / 10 < log 5 := by
  rw [← exp_lt_exp, exp_log (by norm_num : (0 : ℝ) < 5)]
  exact exp_16_lt_5

/-- log(5) < 1.7 since exp(1.7) > 5 -/
theorem log_five_lt_17 : log 5 < (17 : ℝ) / 10 := by
  rw [← exp_lt_exp, exp_log (by norm_num : (0 : ℝ) < 5)]
  exact exp_17_gt_5

/-- log(5) tight bounds: 1.6 < log(5) < 1.7 -/
theorem log_five_bounds_tight : (16 : ℝ) / 10 < log 5 ∧ log 5 < (17 : ℝ) / 10 :=
  ⟨log_five_gt_16, log_five_lt_17⟩

/-!
## Section 12: Tight log(10) bounds

log(10) = log(2) + log(5)
With log(2) ∈ (0.693, 0.694) and log(5) ∈ (1.6, 1.7):
log(10) ∈ (2.293, 2.394)
-/

/-- log(10) > 2.293 -/
theorem log_ten_gt : (2293 : ℝ) / 1000 < log 10 := by
  rw [log_ten_eq]
  have h2 := log_two_gt       -- 0.693 < log(2)
  have h5 := log_five_gt_16   -- 1.6 < log(5)
  linarith

/-- log(10) < 2.394 -/
theorem log_ten_lt : log 10 < (2394 : ℝ) / 1000 := by
  rw [log_ten_eq]
  have h2 := log_two_lt       -- log(2) < 0.694
  have h5 := log_five_lt_17   -- log(5) < 1.7
  linarith

/-- log(10) tight bounds: 2.293 < log(10) < 2.394 -/
theorem log_ten_bounds_tight : (2293 : ℝ) / 1000 < log 10 ∧ log 10 < (2394 : ℝ) / 1000 :=
  ⟨log_ten_gt, log_ten_lt⟩

/-!
## Section 13: Tight log(3) bounds via Taylor series

We need: 1.098 < log(3) < 1.100
Proof:
- exp(1.098) < 3 implies log(3) > 1.098
- exp(1.100) > 3 implies log(3) < 1.100

Using composition: exp(1.098) = exp(0.549)²
-/

/-- exp(0.549) < 1.732 using Taylor upper bound -/
theorem exp_0549_lt : exp ((549 : ℝ) / 1000) < (1732 : ℝ) / 1000 := by
  have hx : |((549 : ℝ) / 1000)| ≤ 1 := by norm_num
  have hn : (0 : ℕ) < 5 := by norm_num
  have hbound := Real.exp_bound hx hn
  have hsum : (Finset.range 5).sum (fun m => ((549 : ℝ)/1000)^m / ↑(m.factorial))
              = 1 + 549/1000 + (549/1000)^2/2 + (549/1000)^3/6 + (549/1000)^4/24 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
               Nat.factorial, Nat.cast_one, pow_zero, pow_one]
    ring
  have herr_eq : |((549 : ℝ)/1000)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5))
                 = (549/1000)^5 * (6 / 600) := by
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have hval : 1 + 549/1000 + (549/1000)^2/2 + (549/1000)^3/6 + (549/1000)^4/24 + (549/1000)^5 * (6/600)
              < (1732 : ℝ) / 1000 := by norm_num
  have h := abs_sub_le_iff.mp hbound
  have hupper : exp (549/1000) ≤ (Finset.range 5).sum (fun m => ((549 : ℝ)/1000)^m / ↑(m.factorial)) +
                               |((549 : ℝ)/1000)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := by
    linarith [h.1]
  calc exp (549/1000)
      ≤ (Finset.range 5).sum (fun m => ((549 : ℝ)/1000)^m / ↑(m.factorial)) +
        |((549 : ℝ)/1000)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := hupper
    _ = 1 + 549/1000 + (549/1000)^2/2 + (549/1000)^3/6 + (549/1000)^4/24 + (549/1000)^5 * (6/600) := by
        rw [hsum, herr_eq]
    _ < 1732/1000 := hval

/-- exp(1.098) < 3 using exp(1.098) = exp(0.549)² < 1.732² < 3 -/
theorem exp_1098_lt_3 : exp ((1098 : ℝ) / 1000) < 3 := by
  have h0549 := exp_0549_lt  -- exp(0.549) < 1.732
  have hsq : (1732 : ℝ) / 1000 * (1732 / 1000) < 3 := by norm_num
  calc exp (1098/1000)
      = exp (549/1000 + 549/1000) := by ring_nf
    _ = exp (549/1000) * exp (549/1000) := by rw [exp_add]
    _ < (1732/1000) * (1732/1000) := by nlinarith [exp_pos (549/1000 : ℝ), h0549]
    _ < 3 := hsq

/-- exp(0.55) > 1.733 using Taylor lower bound -/
theorem exp_055_gt : (1733 : ℝ) / 1000 < exp ((55 : ℝ) / 100) := by
  have hpos : (0 : ℝ) ≤ 55/100 := by norm_num
  have hsum : (Finset.range 5).sum (fun m => ((55 : ℝ)/100)^m / ↑(m.factorial))
              = 1 + 55/100 + (55/100)^2/2 + (55/100)^3/6 + (55/100)^4/24 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
               Nat.factorial, Nat.cast_one, pow_zero, pow_one]
    ring
  have hval : (1733 : ℝ) / 1000 < 1 + 55/100 + (55/100)^2/2 + (55/100)^3/6 + (55/100)^4/24 := by
    norm_num
  calc (1733 : ℝ) / 1000
      < 1 + 55/100 + (55/100)^2/2 + (55/100)^3/6 + (55/100)^4/24 := hval
    _ = (Finset.range 5).sum (fun m => ((55 : ℝ)/100)^m / ↑(m.factorial)) := hsum.symm
    _ ≤ exp (55/100) := Real.sum_le_exp_of_nonneg hpos 5

/-- exp(1.1) > 3 using exp(1.1) = exp(0.55)² > 1.733² > 3 -/
theorem exp_11_gt_3 : 3 < exp ((11 : ℝ) / 10) := by
  have h055 := exp_055_gt  -- exp(0.55) > 1.733
  have hsq : 3 < (1733 : ℝ) / 1000 * (1733 / 1000) := by norm_num
  calc 3
      < (1733/1000) * (1733/1000) := hsq
    _ < exp (55/100) * exp (55/100) := by nlinarith [exp_pos (55/100 : ℝ), h055]
    _ = exp (55/100 + 55/100) := by rw [exp_add]
    _ = exp (11/10) := by ring_nf

/-- exp(0.5495) > 1.7321 using Taylor lower bound (tighter for log(3) < 1.099) -/
theorem exp_05495_gt : (17321 : ℝ) / 10000 < exp ((5495 : ℝ) / 10000) := by
  have hpos : (0 : ℝ) ≤ 5495/10000 := by norm_num
  have hsum : (Finset.range 5).sum (fun m => ((5495 : ℝ)/10000)^m / ↑(m.factorial))
              = 1 + 5495/10000 + (5495/10000)^2/2 + (5495/10000)^3/6 + (5495/10000)^4/24 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
               Nat.factorial, Nat.cast_one, pow_zero, pow_one]
    ring
  have hval : (17321 : ℝ) / 10000 < 1 + 5495/10000 + (5495/10000)^2/2 + (5495/10000)^3/6 + (5495/10000)^4/24 := by
    norm_num
  calc (17321 : ℝ) / 10000
      < 1 + 5495/10000 + (5495/10000)^2/2 + (5495/10000)^3/6 + (5495/10000)^4/24 := hval
    _ = (Finset.range 5).sum (fun m => ((5495 : ℝ)/10000)^m / ↑(m.factorial)) := hsum.symm
    _ ≤ exp (5495/10000) := Real.sum_le_exp_of_nonneg hpos 5

/-- exp(1.099) > 3 using exp(1.099) = exp(0.5495)² > 1.7321² > 3 -/
theorem exp_1099_gt_3 : 3 < exp ((1099 : ℝ) / 1000) := by
  have h05495 := exp_05495_gt  -- exp(0.5495) > 1.7321
  have hsq : 3 < (17321 : ℝ) / 10000 * (17321 / 10000) := by norm_num
  calc 3
      < (17321/10000) * (17321/10000) := hsq
    _ < exp (5495/10000) * exp (5495/10000) := by nlinarith [exp_pos (5495/10000 : ℝ), h05495]
    _ = exp (5495/10000 + 5495/10000) := by rw [exp_add]
    _ = exp (1099/1000) := by ring_nf

/-- log(3) > 1.098 since exp(1.098) < 3 -/
theorem log_three_gt_1098 : (1098 : ℝ) / 1000 < log 3 := by
  rw [← exp_lt_exp, exp_log (by norm_num : (0 : ℝ) < 3)]
  exact exp_1098_lt_3

/-- log(3) < 1.1 since exp(1.1) > 3 -/
theorem log_three_lt_11 : log 3 < (11 : ℝ) / 10 := by
  rw [← exp_lt_exp, exp_log (by norm_num : (0 : ℝ) < 3)]
  exact exp_11_gt_3

/-- log(3) < 1.099 since exp(1.099) > 3 (tighter bound) -/
theorem log_three_lt_1099 : log 3 < (1099 : ℝ) / 1000 := by
  rw [← exp_lt_exp, exp_log (by norm_num : (0 : ℝ) < 3)]
  exact exp_1099_gt_3

/-- log(3) tight bounds: 1.098 < log(3) < 1.1 -/
theorem log_three_bounds_tight : (1098 : ℝ) / 1000 < log 3 ∧ log 3 < (11 : ℝ) / 10 :=
  ⟨log_three_gt_1098, log_three_lt_11⟩

/-- log(3) very tight bounds: 1.098 < log(3) < 1.099 -/
theorem log_three_bounds_very_tight : (1098 : ℝ) / 1000 < log 3 ∧ log 3 < (1099 : ℝ) / 1000 :=
  ⟨log_three_gt_1098, log_three_lt_1099⟩

/-!
## Section 14: log(27) bounds

log(27) = log(3³) = 3 * log(3)
With 1.098 < log(3) < 1.1:
log(27) ∈ (3.294, 3.3)
-/

/-- log(27) = 3 * log(3) -/
theorem log_27_eq : log 27 = 3 * log 3 := by
  have h : (27 : ℝ) = 3^3 := by norm_num
  rw [h, log_pow]
  norm_cast

/-- log(27) > 3.294 -/
theorem log_27_gt : (3294 : ℝ) / 1000 < log 27 := by
  rw [log_27_eq]
  have h := log_three_gt_1098
  linarith

/-- log(27) < 3.3 -/
theorem log_27_lt : log 27 < (33 : ℝ) / 10 := by
  rw [log_27_eq]
  have h := log_three_lt_11
  linarith

/-- log(27) < 3.297 (tighter bound from log(3) < 1.099) -/
theorem log_27_lt_tight : log 27 < (3297 : ℝ) / 1000 := by
  rw [log_27_eq]
  have h := log_three_lt_1099
  linarith

/-- log(27) bounds: 3.294 < log(27) < 3.3 -/
theorem log_27_bounds : (3294 : ℝ) / 1000 < log 27 ∧ log 27 < (33 : ℝ) / 10 :=
  ⟨log_27_gt, log_27_lt⟩

/-- log(27) tight bounds: 3.294 < log(27) < 3.297 -/
theorem log_27_bounds_tight : (3294 : ℝ) / 1000 < log 27 ∧ log 27 < (3297 : ℝ) / 1000 :=
  ⟨log_27_gt, log_27_lt_tight⟩

/-!
## Section 15: 27^1.618 > 206 and 27^1.6185 < 208

Using rpow_def_of_pos: 27^x = exp(x * log(27))

For 27^1.618:
- x * log(27) > 1.618 * 3.294 = 5.330
- Need: exp(5.33) > 206

For 27^1.6185:
- x * log(27) < 1.6185 * 3.297 = 5.336
- Need: exp(5.336) < 208
-/

/-- Argument bound: 1.618 * log(27) > 5.33 -/
theorem rpow_arg_lower : (533 : ℝ) / 100 < (1618 : ℝ) / 1000 * log 27 := by
  have h := log_27_gt
  nlinarith

/-- Argument bound: 1.6185 * log(27) < 5.336 (using tight log(27) bound) -/
theorem rpow_arg_upper_tight : (16185 : ℝ) / 10000 * log 27 < (5336 : ℝ) / 1000 := by
  have h := log_27_lt_tight
  nlinarith

/-- Argument bound: 1.6185 * log(27) < 5.342 (looser, kept for compatibility) -/
theorem rpow_arg_upper : (16185 : ℝ) / 10000 * log 27 < (5342 : ℝ) / 1000 := by
  have h := log_27_lt
  nlinarith

/-- exp(5.33) > 206 via exp(5.33) = exp(1)^5 * exp(0.33)
    Using e > 2.718 and exp(0.33) > 1.39:
    2.718^5 * 1.39 > 148 * 1.39 > 206 -/
theorem exp_533_gt_206 : (206 : ℝ) < exp ((533 : ℝ) / 100) := by
  -- exp(5.33) = exp(5) * exp(0.33)
  -- exp(5) = exp(1)^5 and we have exp(1) > 2.7182...
  -- exp(0.33) > 1.39 by Taylor
  have he := Real.exp_one_gt_d9  -- 2.7182818283 < exp(1)
  have he_bound : (2718 : ℝ) / 1000 < exp 1 := by linarith

  -- exp(0.33) > 1.39 by Taylor lower bound
  have hexp033 : (139 : ℝ) / 100 < exp ((33 : ℝ) / 100) := by
    have hpos : (0 : ℝ) ≤ 33/100 := by norm_num
    have hsum : (Finset.range 5).sum (fun m => ((33 : ℝ)/100)^m / ↑(m.factorial))
                = 1 + 33/100 + (33/100)^2/2 + (33/100)^3/6 + (33/100)^4/24 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
                 Nat.factorial, Nat.cast_one, pow_zero, pow_one]
      ring
    have hval : (139 : ℝ) / 100 < 1 + 33/100 + (33/100)^2/2 + (33/100)^3/6 + (33/100)^4/24 := by
      norm_num
    calc (139 : ℝ) / 100
        < 1 + 33/100 + (33/100)^2/2 + (33/100)^3/6 + (33/100)^4/24 := hval
      _ = (Finset.range 5).sum (fun m => ((33 : ℝ)/100)^m / ↑(m.factorial)) := hsum.symm
      _ ≤ exp (33/100) := Real.sum_le_exp_of_nonneg hpos 5

  -- exp(5) = exp(1)^5 > 2.718^5
  have hexp5_bound : (2718 : ℝ) / 1000 ^ 5 < exp 5 := by
    have hpos1 : (0 : ℝ) < exp 1 := exp_pos 1
    calc (2718 : ℝ) / 1000 ^ 5
        < (exp 1) ^ 5 := by nlinarith [he_bound]
      _ = exp (1 * 5) := by rw [← exp_nat_mul]
      _ = exp 5 := by ring_nf

  -- 2.718^5 * 1.39 > 206
  have hprod : (206 : ℝ) < (2718 : ℝ) / 1000 ^ 5 * (139 / 100) := by norm_num

  -- Combine
  have hexp5_pos : (0 : ℝ) < exp 5 := exp_pos 5
  have hexp033_pos : (0 : ℝ) < exp (33/100) := exp_pos (33/100)
  calc (206 : ℝ)
      < (2718 / 1000) ^ 5 * (139 / 100) := hprod
    _ < exp 5 * exp (33/100) := by nlinarith [hexp5_bound, hexp033]
    _ = exp (5 + 33/100) := by rw [exp_add]
    _ = exp (533/100) := by ring_nf

/-- exp(0.336) < 1.40 using Taylor upper bound -/
theorem exp_0336_lt : exp ((336 : ℝ) / 1000) < (14 : ℝ) / 10 := by
  have hx : |((336 : ℝ) / 1000)| ≤ 1 := by norm_num
  have hn : (0 : ℕ) < 5 := by norm_num
  have hbound := Real.exp_bound hx hn
  have hsum : (Finset.range 5).sum (fun m => ((336 : ℝ)/1000)^m / ↑(m.factorial))
              = 1 + 336/1000 + (336/1000)^2/2 + (336/1000)^3/6 + (336/1000)^4/24 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
               Nat.factorial, Nat.cast_one, pow_zero, pow_one]
    ring
  have herr_eq : |((336 : ℝ)/1000)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5))
                 = (336/1000)^5 * (6 / 600) := by
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have hval : 1 + 336/1000 + (336/1000)^2/2 + (336/1000)^3/6 + (336/1000)^4/24 + (336/1000)^5 * (6/600)
              < (14 : ℝ) / 10 := by norm_num
  have h := abs_sub_le_iff.mp hbound
  have hupper : exp (336/1000) ≤ (Finset.range 5).sum (fun m => ((336 : ℝ)/1000)^m / ↑(m.factorial)) +
                               |((336 : ℝ)/1000)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := by
    linarith [h.1]
  calc exp (336/1000)
      ≤ (Finset.range 5).sum (fun m => ((336 : ℝ)/1000)^m / ↑(m.factorial)) +
        |((336 : ℝ)/1000)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := hupper
    _ = 1 + 336/1000 + (336/1000)^2/2 + (336/1000)^3/6 + (336/1000)^4/24 + (336/1000)^5 * (6/600) := by
        rw [hsum, herr_eq]
    _ < 14/10 := hval

/-- exp(5.336) < 208 via exp(5.336) = exp(5) * exp(0.336)
    Using e < 2.7182818286 and exp(0.336) < 1.40:
    exp(1)^5 * 1.40 < 148.414 * 1.40 < 207.78 < 208 -/
theorem exp_5336_lt_208 : exp ((5336 : ℝ) / 1000) < (208 : ℝ) := by
  have he := Real.exp_one_lt_d9  -- exp(1) < 2.7182818286
  have he_bound : exp 1 < (27182818286 : ℝ) / 10000000000 := by linarith

  -- exp(5) = exp(1)^5 < (2.7182818286)^5
  have hexp5_bound : exp 5 < (27182818286 : ℝ) / 10000000000 ^ 5 := by
    have hpos1 : (0 : ℝ) < exp 1 := exp_pos 1
    calc exp 5
        = exp (1 * 5) := by ring_nf
      _ = (exp 1) ^ 5 := by rw [exp_nat_mul]
      _ < (27182818286 / 10000000000) ^ 5 := by nlinarith [he_bound]

  -- exp(0.336) < 1.40
  have hexp0336 := exp_0336_lt

  -- (2.7182818286)^5 * 1.40 < 208
  have hprod : (27182818286 : ℝ) / 10000000000 ^ 5 * (14 / 10) < 208 := by norm_num

  -- Combine
  have hexp5_pos : (0 : ℝ) < exp 5 := exp_pos 5
  have hexp0336_pos : (0 : ℝ) < exp (336/1000) := exp_pos (336/1000)
  calc exp (5336/1000)
      = exp (5 + 336/1000) := by ring_nf
    _ = exp 5 * exp (336/1000) := by rw [exp_add]
    _ < (27182818286 / 10000000000) ^ 5 * (14 / 10) := by nlinarith [hexp5_bound, hexp0336]
    _ < 208 := hprod

/-- exp(5.342) < 209 (looser bound kept for compatibility) -/
theorem exp_5342_lt_209 : exp ((5342 : ℝ) / 1000) < (209 : ℝ) := by
  have he := Real.exp_one_lt_d9
  have he_bound : exp 1 < (27183 : ℝ) / 10000 := by linarith

  have hexp0342 : exp ((342 : ℝ) / 1000) < (1408 : ℝ) / 1000 := by
    have hx : |((342 : ℝ) / 1000)| ≤ 1 := by norm_num
    have hn : (0 : ℕ) < 5 := by norm_num
    have hbound := Real.exp_bound hx hn
    have hsum : (Finset.range 5).sum (fun m => ((342 : ℝ)/1000)^m / ↑(m.factorial))
                = 1 + 342/1000 + (342/1000)^2/2 + (342/1000)^3/6 + (342/1000)^4/24 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
                 Nat.factorial, Nat.cast_one, pow_zero, pow_one]
      ring
    have herr_eq : |((342 : ℝ)/1000)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5))
                   = (342/1000)^5 * (6 / 600) := by
      simp only [Nat.factorial, Nat.succ_eq_add_one]
      norm_num
    have hval : 1 + 342/1000 + (342/1000)^2/2 + (342/1000)^3/6 + (342/1000)^4/24 + (342/1000)^5 * (6/600)
                < (1408 : ℝ) / 1000 := by norm_num
    have h := abs_sub_le_iff.mp hbound
    have hupper : exp (342/1000) ≤ (Finset.range 5).sum (fun m => ((342 : ℝ)/1000)^m / ↑(m.factorial)) +
                                 |((342 : ℝ)/1000)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := by
      linarith [h.1]
    calc exp (342/1000)
        ≤ (Finset.range 5).sum (fun m => ((342 : ℝ)/1000)^m / ↑(m.factorial)) +
          |((342 : ℝ)/1000)|^5 * (↑(Nat.succ 5) / (↑(Nat.factorial 5) * 5)) := hupper
      _ = 1 + 342/1000 + (342/1000)^2/2 + (342/1000)^3/6 + (342/1000)^4/24 + (342/1000)^5 * (6/600) := by
          rw [hsum, herr_eq]
      _ < 1408/1000 := hval

  have hexp5_bound : exp 5 < (27183 : ℝ) / 10000 ^ 5 := by
    have hpos1 : (0 : ℝ) < exp 1 := exp_pos 1
    calc exp 5
        = exp (1 * 5) := by ring_nf
      _ = (exp 1) ^ 5 := by rw [exp_nat_mul]
      _ < (27183 / 10000) ^ 5 := by nlinarith [he_bound]

  have hprod : (27183 : ℝ) / 10000 ^ 5 * (1408 / 1000) < 209 := by norm_num
  have hexp5_pos : (0 : ℝ) < exp 5 := exp_pos 5
  have hexp0342_pos : (0 : ℝ) < exp (342/1000) := exp_pos (342/1000)
  calc exp (5342/1000)
      = exp (5 + 342/1000) := by ring_nf
    _ = exp 5 * exp (342/1000) := by rw [exp_add]
    _ < (27183 / 10000) ^ 5 * (1408 / 1000) := by nlinarith [hexp5_bound, hexp0342]
    _ < 209 := hprod

/-!
## Section 16: Final rpow theorems

Replace the axioms with proven theorems!
-/

/-- 27^1.618 > 206 PROVEN.
    Uses: 27^x = exp(x * log(27)), and bounds on the argument and exp. -/
theorem rpow_27_1618_gt_206_proven : (206 : ℝ) < (27 : ℝ) ^ ((1618 : ℝ) / 1000) := by
  have h27pos : (0 : ℝ) < 27 := by norm_num
  rw [Real.rpow_def_of_pos h27pos]
  -- 1.618 * log(27) > 5.33, and exp(5.33) > 206
  have harg := rpow_arg_lower  -- 5.33 < 1.618 * log(27)
  have hexp := exp_533_gt_206  -- 206 < exp(5.33)
  calc (206 : ℝ)
      < exp (533/100) := hexp
    _ < exp ((1618 : ℝ) / 1000 * log 27) := by
        apply exp_lt_exp.mpr
        linarith

/-- 27^1.6185 < 208 PROVEN.
    Using tight bounds: 1.6185 * log(27) < 5.336 and exp(5.336) < 208 -/
theorem rpow_27_16185_lt_208_proven : (27 : ℝ) ^ ((16185 : ℝ) / 10000) < (208 : ℝ) := by
  have h27pos : (0 : ℝ) < 27 := by norm_num
  rw [Real.rpow_def_of_pos h27pos]
  -- 1.6185 * log(27) < 5.336, and exp(5.336) < 208
  have harg := rpow_arg_upper_tight  -- 1.6185 * log(27) < 5.336
  have hexp := exp_5336_lt_208  -- exp(5.336) < 208
  calc exp ((16185 : ℝ) / 10000 * log 27)
      < exp (5336/1000) := by
        apply exp_lt_exp.mpr
        linarith
    _ < 208 := hexp

/-- 27^1.6185 < 209 (looser bound, kept for compatibility) -/
theorem rpow_27_16185_lt_209_proven : (27 : ℝ) ^ ((16185 : ℝ) / 10000) < (209 : ℝ) := by
  have h := rpow_27_16185_lt_208_proven
  linarith

end GIFT.Foundations.NumericalBounds
