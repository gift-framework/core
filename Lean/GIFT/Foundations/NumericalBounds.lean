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
    field_simp
    calc GIFT.Foundations.GoldenRatio.phi * (GIFT.Foundations.GoldenRatio.phi - 1)
        = GIFT.Foundations.GoldenRatio.phi^2 - GIFT.Foundations.GoldenRatio.phi := by ring
      _ = (GIFT.Foundations.GoldenRatio.phi + 1) - GIFT.Foundations.GoldenRatio.phi := by rw [hsq]
      _ = 1 := by ring
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

end GIFT.Foundations.NumericalBounds
