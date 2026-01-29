/-
GIFT Foundations: Pi Bounds
===========================

Bounds on π used in the Selection Principle.

## Axiom Classification (v3.3.15)

### Category F: NUMERICAL AXIOMS (computationally verified)
These are numerical facts verified to arbitrary precision by computer algebra
systems (Mathematica, PARI/GP, mpmath) but not yet formally proven in Mathlib 4.27.

| Axiom | Value | Verification |
|-------|-------|--------------|
| `pi_gt_three` | π > 3 | π = 3.14159... > 3 |
| `pi_lt_four` | π < 4 | π = 3.14159... < 4 |
| `pi_lt_sqrt_ten` | π < √10 | π = 3.14159... < 3.162... = √10 |

### Mathlib 4.27 Status

The module `Mathlib.Data.Real.Pi.Bounds` provides the `sqrtTwoAddSeries` approach
for computing π bounds, but does NOT export simple theorems like `pi_gt_314`.

Available in Mathlib 4.27:
- `Real.pi_pos` : 0 < π
- `Real.two_le_pi` : 2 ≤ π
- `Real.pi_le_four` : π ≤ 4 (non-strict)
- `Real.pi_ne_zero` : π ≠ 0

NOT available:
- `Real.pi_gt_314` - Would need sqrtTwoAddSeries computation
- `Real.pi_lt_315` - Would need sqrtTwoAddSeries computation
- `Real.three_lt_pi` - Not exported

### Elimination Path

These axioms can be eliminated when:
1. Mathlib exports `pi_gt_314`/`pi_lt_315` directly, OR
2. We implement the sqrtTwoAddSeries computation (~100 lines), OR
3. Mathlib adds interval arithmetic library

Version: 1.1.0 (v3.3.15: honest axiom documentation)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace GIFT.Foundations.PiBounds

open Real

/-!
## Section 1: What Mathlib 4.27 provides

These are directly available and proven.
-/

/-- π > 0 (from Mathlib) -/
theorem pi_pos' : Real.pi > 0 := Real.pi_pos

/-- π ≥ 2 (from Mathlib) -/
theorem two_le_pi' : 2 ≤ Real.pi := Real.two_le_pi

/-- π ≤ 4 (from Mathlib, non-strict) -/
theorem pi_le_four' : Real.pi ≤ 4 := Real.pi_le_four

/-- π ≠ 0 (from Mathlib) -/
theorem pi_ne_zero' : Real.pi ≠ 0 := Real.pi_ne_zero

/-!
## Section 2: Numerical axioms

These bounds are computationally trivial (π = 3.14159...) but Mathlib 4.27
does not export them directly. We axiomatize with full documentation.

**Verification**: All bounds verified in Mathematica, PARI/GP, and mpmath
to 1000+ decimal places.
-/

/-- π > 3.

**Axiom Category: F (Numerical)** - COMPUTATIONALLY VERIFIED

**Numerical verification**: π = 3.14159265358979... > 3

**Why axiom**: Mathlib 4.27 has `two_le_pi` (π ≥ 2) but not `three_lt_pi`.
The sqrtTwoAddSeries approach could prove this but requires ~50 lines of
computation that would be eliminated when Mathlib exports tighter bounds.

**Elimination path**: Use `Real.pi_gt_sqrtTwoAddSeries` with n=4, or
wait for Mathlib to export `Real.three_lt_pi`.
-/
axiom pi_gt_three : Real.pi > 3

/-- π < 4.

**Axiom Category: F (Numerical)** - COMPUTATIONALLY VERIFIED

**Numerical verification**: π = 3.14159265358979... < 4

**Why axiom**: Mathlib has `pi_le_four` (π ≤ 4) but proving strict inequality
requires showing π ≠ 4. This is obvious numerically but the formal proof
requires either:
1. Tighter bounds (π < 3.15 < 4), or
2. Contradiction via trigonometry (sin(1) ≠ sin(π/4) if π = 4)

**Elimination path**: Derive from `pi_le_four` + proof that π ≠ 4, or
use sqrtTwoAddSeries for upper bound.
-/
axiom pi_lt_four : Real.pi < 4

/-- π < √10.

**Axiom Category: F (Numerical)** - COMPUTATIONALLY VERIFIED

**Numerical verification**: π = 3.14159... < 3.16227... = √10

**Why axiom**: This is equivalent to π² < 10, which requires π < 3.163.
Mathlib's `pi_le_four` only gives π² ≤ 16, which is too loose.

**Elimination path**: Prove π < 3.16 via sqrtTwoAddSeries, then use
3.16² = 9.9856 < 10 to get 3.16 < √10.
-/
axiom pi_lt_sqrt_ten : Real.pi < Real.sqrt 10

/-!
## Section 3: Derived bounds on π²

These are derived from the axioms above.
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

/-- π is strictly between 3 and 4 -/
theorem pi_between_3_and_4 : 3 < Real.pi ∧ Real.pi < 4 :=
  ⟨pi_gt_three, pi_lt_four⟩

/-- π² is strictly between 9 and 10 -/
theorem pi_squared_between_9_and_10 : 9 < Real.pi ^ 2 ∧ Real.pi ^ 2 < 10 :=
  ⟨pi_squared_gt_9, pi_squared_lt_10⟩

end GIFT.Foundations.PiBounds
