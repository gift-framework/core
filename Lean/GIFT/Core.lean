-- Import derived constants from Algebraic modules
import GIFT.Algebraic.Octonions
import GIFT.Algebraic.G2
import GIFT.Algebraic.BettiNumbers

/-!
# GIFT Core Constants

Single source of truth for all GIFT constants.

## Design Philosophy

All constants are defined in ONE place (here or in Algebraic.*).
Other modules import `GIFT.Core` and use these definitions.

## Constant Hierarchy

### Derived from Octonions (foundational)
- `imaginary_count = 7` — number of imaginary units in O
- `dim_G2 = 2 × 7 = 14` — Aut(O) dimension
- `b2 = C(7,2) = 21` — harmonic 2-forms from imaginary pairs
- `b3 = b2 + fund_E7 = 77` — harmonic 3-forms
- `H_star = b2 + b3 + 1 = 99` — total topological degrees of freedom

### Exceptional Lie Algebras
- `dim_E8 = 248` — **derived** via Mathlib Coxeter (see `Foundations.E8Mathlib`)
- `rank_E8 = 8`
- `dim_E7 = 133`, `dim_E6 = 78`, `dim_F4 = 52`
- `dim_G2 = 14`, `rank_G2 = 2`

### Physical/Geometric
- `dim_K7 = 7` — compact manifold dimension
- `D_bulk = 11` — M-theory bulk dimension
- `p2 = 2` — Pontryagin class contribution
- `Weyl_factor = 5` — from Weyl group factorization

## Usage

```lean
import GIFT.Core
open GIFT.Core

#check b2        -- 21
#check dim_E8    -- 248
#check H_star    -- 99
```
-/

namespace GIFT.Core

-- =============================================================================
-- RE-EXPORT FROM ALGEBRAIC (derived, justified)
-- =============================================================================

-- From Octonions: the foundational constant
export Algebraic.Octonions (imaginary_count octonion_dim)

-- From G2: automorphism group
export Algebraic.G2 (dim_G2 rank_G2 omega2_7 omega2_14 omega3_1 omega3_7 omega3_27)

-- From BettiNumbers: topological invariants (DERIVED from octonions!)
export Algebraic.BettiNumbers (b2 b3 H_star fund_E7)

-- =============================================================================
-- EXCEPTIONAL LIE ALGEBRAS
-- =============================================================================

/-- Dimension of E8 = 248 (= 240 roots + 8 Cartan)

Mathematical derivation in `GIFT.Foundations.E8Mathlib`:
- 240 roots = h × rank = 30 × 8 (Coxeter formula)
- 240 roots verified by explicit enumeration in `GIFT.Foundations.RootSystems`
- Uses `CoxeterMatrix.E₈` from Mathlib

See `GIFT.Foundations.E8Mathlib.E8_dimension_certified` for the formal proof.
-/
def dim_E8 : ℕ := 248

/-- Rank of E8 -/
def rank_E8 : ℕ := 8

/-- Dimension of E8 × E8 -/
def dim_E8xE8 : ℕ := 2 * dim_E8

/-- Dimension of E7 -/
def dim_E7 : ℕ := 133

/-- Fundamental representation of E7 -/
def dim_fund_E7 : ℕ := 56

/-- Dimension of E6 -/
def dim_E6 : ℕ := 78

/-- Dimension of F4 -/
def dim_F4 : ℕ := 52

-- Note: dim_G2 and rank_G2 come from Algebraic.G2

-- =============================================================================
-- GEOMETRY: K7 MANIFOLD
-- =============================================================================

/-- Real dimension of K7 manifold -/
def dim_K7 : ℕ := 7

/-- Dimension of Jordan algebra J3(O) -/
def dim_J3O : ℕ := 27

/-- Dimension of traceless Jordan algebra -/
def dim_J3O_traceless : ℕ := 26

/-- M-theory bulk dimension -/
def D_bulk : ℕ := 11

-- =============================================================================
-- TOPOLOGY
-- =============================================================================

/-- Pontryagin class contribution -/
def p2 : ℕ := 2

-- Note: b2, b3, H_star come from Algebraic.BettiNumbers

-- =============================================================================
-- WEYL GROUP AND PHYSICS
-- =============================================================================

/-- Weyl factor from |W(E8)| = 2^14 × 3^5 × 5^2 × 7 -/
def Weyl_factor : ℕ := 5

/-- Weyl squared (pentagonal structure) -/
def Weyl_sq : ℕ := Weyl_factor * Weyl_factor

/-- Order of Weyl group of E8 -/
def weyl_E8_order : ℕ := 696729600

-- =============================================================================
-- STANDARD MODEL
-- =============================================================================

/-- Number of fermion generations (from K₄ perfect matchings = 3) -/
def N_gen : ℕ := 3

/-- SU(3) color dimension -/
def dim_SU3 : ℕ := 8

/-- SU(2) weak isospin dimension -/
def dim_SU2 : ℕ := 3

/-- U(1) hypercharge dimension -/
def dim_U1 : ℕ := 1

/-- Total SM gauge dimension -/
def dim_SM_gauge : ℕ := dim_SU3 + dim_SU2 + dim_U1

-- =============================================================================
-- PRIME SEQUENCE (for exceptional chain)
-- =============================================================================

/-- 6th prime (for E6) -/
def prime_6 : ℕ := 13

/-- 8th prime (for E7) -/
def prime_8 : ℕ := 19

/-- 11th prime (for E8) -/
def prime_11 : ℕ := 31

-- =============================================================================
-- METRIC PARAMETERS
-- =============================================================================

/-- Metric determinant numerator: det(g) = 65/32 -/
def det_g_num : ℕ := 65

/-- Metric determinant denominator -/
def det_g_den : ℕ := 32

/-- Torsion coefficient denominator: κ_T = 1/61 -/
def kappa_T_den : ℕ := 61

-- =============================================================================
-- BASIC CERTIFIED THEOREMS
-- =============================================================================

theorem dim_E8_certified : dim_E8 = 248 := rfl
theorem rank_E8_certified : rank_E8 = 8 := rfl
theorem dim_E8xE8_certified : dim_E8xE8 = 496 := rfl
theorem dim_K7_certified : dim_K7 = 7 := rfl
theorem dim_J3O_certified : dim_J3O = 27 := rfl
theorem p2_certified : p2 = 2 := rfl
theorem Weyl_sq_certified : Weyl_sq = 25 := rfl
theorem D_bulk_certified : D_bulk = 11 := rfl
theorem SM_gauge_certified : dim_SM_gauge = 12 := rfl
theorem N_gen_certified : N_gen = 3 := rfl

-- From Algebraic.BettiNumbers (re-proven here for convenience)
theorem b2_value : b2 = 21 := rfl
theorem b3_value : b3 = 77 := rfl
theorem H_star_value : H_star = 99 := rfl

-- Core identity: H* = b2 + b3 + 1
theorem H_star_structure : H_star = b2 + b3 + 1 := rfl

-- Exceptional group dimensions
theorem dim_F4_certified : dim_F4 = 52 := rfl
theorem dim_E6_certified : dim_E6 = 78 := rfl
theorem dim_E7_certified : dim_E7 = 133 := rfl
theorem weyl_E8_order_certified : weyl_E8_order = 696729600 := rfl

end GIFT.Core
