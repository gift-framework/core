/-
GIFT Foundations: Pi Bounds
===========================

Axiom-free proofs of π bounds used in the Selection Principle.

This file eliminates the following axioms from SelectionPrinciple.lean:
- `pi_gt_three` : Real.pi > 3
- `pi_lt_four` : Real.pi < 4
- `pi_lt_sqrt_ten` : Real.pi < Real.sqrt 10

## Proof Strategy

### Option 1: Mathlib certified bounds (preferred)
Mathlib 4.27+ provides `Real.pi_gt_314` and `Real.pi_lt_315`:
- π > 3.14 > 3 ✓
- π < 3.15 < 4 ✓
- π < 3.15 < √10 ≈ 3.162 ✓

### Option 2: Trigonometric bounds (fallback)
If Mathlib bounds unavailable:
- cos(1) > 0.54 implies π > 3 (via monotonicity)
- sin(1) > 0.84 implies π < 4 (contradiction if π = 4)

## Status

PROVEN (using Mathlib certified decimal bounds).

Version: 1.0.0
-/

import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace GIFT.Foundations.PiBounds

open Real

/-!
## Section 1: Basic π bounds from Mathlib

Mathlib provides certified bounds via interval arithmetic:
- `Real.pi_gt_314` : (157 : ℚ) / 50 < π (i.e., 3.14 < π)
- `Real.pi_lt_315` : π < (63 : ℚ) / 20 (i.e., π < 3.15)
-/

/-- π > 3.14 (from Mathlib).
    Mathlib proves this via certified decimal computation. -/
theorem pi_gt_314 : (314 : ℝ) / 100 < Real.pi := by
  have h := Real.pi_gt_314  -- (157 : ℚ) / 50 < π
  -- 157/50 = 3.14 as rationals
  have heq : ((157 : ℚ) / 50 : ℝ) = 314 / 100 := by norm_num
  rw [heq] at h
  exact h

/-- π < 3.15 (from Mathlib).
    Mathlib proves this via certified decimal computation. -/
theorem pi_lt_315 : Real.pi < (315 : ℝ) / 100 := by
  have h := Real.pi_lt_315  -- π < (63 : ℚ) / 20
  -- 63/20 = 3.15 as rationals
  have heq : ((63 : ℚ) / 20 : ℝ) = 315 / 100 := by norm_num
  rw [heq] at h
  exact h

/-!
## Section 2: The three axioms, now theorems

These replace the axioms in SelectionPrinciple.lean.
-/

/-- π > 3. PROVEN via Mathlib's pi_gt_314.
    Since 3.14 > 3, and π > 3.14, we have π > 3. -/
theorem pi_gt_three : Real.pi > 3 := by
  have h := pi_gt_314  -- 3.14 < π
  linarith

/-- π < 4. PROVEN via Mathlib's pi_lt_315.
    Since π < 3.15 < 4, we have π < 4. -/
theorem pi_lt_four : Real.pi < 4 := by
  have h := pi_lt_315  -- π < 3.15
  linarith

/-- π < √10. PROVEN via Mathlib's pi_lt_315 and squaring.
    √10 ≈ 3.162..., and π < 3.15, so π < √10.

    Proof: π < 3.15 and 3.15² = 9.9225 < 10 implies 3.15 < √10.
    Therefore π < 3.15 < √10. -/
theorem pi_lt_sqrt_ten : Real.pi < Real.sqrt 10 := by
  have hpi := pi_lt_315  -- π < 3.15
  -- 3.15 < √10 because 3.15² = 9.9225 < 10
  have h315_lt_sqrt10 : (315 : ℝ) / 100 < Real.sqrt 10 := by
    have h : ((315 : ℝ) / 100)^2 < 10 := by norm_num
    have hpos : (0 : ℝ) ≤ 315 / 100 := by norm_num
    rw [← sqrt_sq hpos]
    exact sqrt_lt_sqrt (by norm_num) h
  linarith

/-!
## Section 3: Derived bounds on π²
-/

/-- π² > 9 (from π > 3) -/
theorem pi_squared_gt_9 : Real.pi ^ 2 > 9 := by
  have h : Real.pi > 3 := pi_gt_three
  have h3 : (3 : ℝ)^2 = 9 := by norm_num
  rw [← h3]
  exact sq_lt_sq' (by linarith) h

/-- π² < 10 (from π < √10) -/
theorem pi_squared_lt_10 : Real.pi ^ 2 < 10 := by
  have h : Real.pi < Real.sqrt 10 := pi_lt_sqrt_ten
  have hpi_pos : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have h10_pos : (0 : ℝ) ≤ 10 := by norm_num
  calc Real.pi ^ 2
      < (Real.sqrt 10) ^ 2 := sq_lt_sq' (by linarith [Real.pi_pos]) h
    _ = 10 := Real.sq_sqrt h10_pos

/-- π² < 16 (from π < 4) - looser bound -/
theorem pi_squared_lt_16 : Real.pi ^ 2 < 16 := by
  have h : Real.pi < 4 := pi_lt_four
  have hpi_pos : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have h4 : (4 : ℝ)^2 = 16 := by norm_num
  rw [← h4]
  exact sq_lt_sq' (by linarith [Real.pi_pos]) h

/-!
## Section 4: Additional useful bounds
-/

/-- π > 3.1 (slightly tighter than 3) -/
theorem pi_gt_31 : Real.pi > (31 : ℝ) / 10 := by
  have h := pi_gt_314
  linarith

/-- π < 3.2 (slightly tighter than 4) -/
theorem pi_lt_32 : Real.pi < (32 : ℝ) / 10 := by
  have h := pi_lt_315
  linarith

/-- π is strictly between 3 and 4 -/
theorem pi_between_3_and_4 : 3 < Real.pi ∧ Real.pi < 4 :=
  ⟨pi_gt_three, pi_lt_four⟩

/-- π² is strictly between 9 and 10 -/
theorem pi_squared_between_9_and_10 : 9 < Real.pi ^ 2 ∧ Real.pi ^ 2 < 10 :=
  ⟨pi_squared_gt_9, pi_squared_lt_10⟩

end GIFT.Foundations.PiBounds
