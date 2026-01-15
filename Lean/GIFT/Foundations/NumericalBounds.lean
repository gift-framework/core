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

end GIFT.Foundations.NumericalBounds
