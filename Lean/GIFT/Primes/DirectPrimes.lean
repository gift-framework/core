-- GIFT Prime Atlas - Direct Primes
-- v2.0.0: Primes appearing directly as GIFT constants
--
-- Direct primes are those that appear directly as GIFT constants:
--   2  = p2 (Pontryagin class)
--   3  = N_gen (generations)
--   5  = Weyl_factor
--   7  = dim_K7
--   11 = D_bulk (M-theory dimension)
--   13 = alpha_sq_B_sum
--   17 = lambda_H_num
--   19 = prime(8)
--   31 = prime(11)
--   61 = kappa_T_inv

import GIFT.Core
import GIFT.Relations
import Mathlib.Data.Nat.Prime.Basic

namespace GIFT.Primes.Tier1

open GIFT.Core GIFT.Relations

-- =============================================================================
-- DIRECT PRIMES: GIFT CONSTANTS (Relations 101-110)
-- =============================================================================

/-- RELATION 101: p2 = 2 is prime -/
theorem p2_is_prime : Nat.Prime p2 := by native_decide

/-- RELATION 102: N_gen = 3 is prime -/
theorem N_gen_is_prime : Nat.Prime N_gen := by native_decide

/-- RELATION 103: Weyl_factor = 5 is prime -/
theorem Weyl_is_prime : Nat.Prime Weyl_factor := by native_decide

/-- RELATION 104: dim_K7 = 7 is prime -/
theorem dim_K7_is_prime : Nat.Prime dim_K7 := by native_decide

/-- RELATION 105: D_bulk = 11 is prime -/
theorem D_bulk_is_prime : Nat.Prime D_bulk := by native_decide

/-- RELATION 106: alpha_sq_B_sum = 13 is prime -/
def alpha_sq_B_sum : Nat := 13
theorem alpha_B_sum_is_prime : Nat.Prime alpha_sq_B_sum := by native_decide

/-- RELATION 107: lambda_H_num = 17 is prime -/
theorem lambda_H_is_prime : Nat.Prime lambda_H_num := by native_decide

/-- RELATION 108: prime_8 = 19 is prime -/
theorem prime_8_is_prime : Nat.Prime prime_8 := by native_decide

/-- RELATION 109: prime_11 = 31 is prime -/
theorem prime_11_is_prime : Nat.Prime prime_11 := by native_decide

/-- RELATION 110: kappa_T_inv = 61 is prime -/
def kappa_T_inv : Nat := 61
theorem kappa_T_inv_is_prime : Nat.Prime kappa_T_inv := by native_decide

-- =============================================================================
-- DIRECT PRIME SET
-- =============================================================================

/-- The set of direct primes (GIFT constants) -/
def tier1_primes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 31, 61]

/-- All direct prime values are prime -/
theorem tier1_all_prime : ∀ p ∈ tier1_primes, Nat.Prime p := by decide

/-- Count of direct primes -/
theorem tier1_count : tier1_primes.length = 10 := rfl

-- =============================================================================
-- DIRECT PRIME COVERAGE
-- =============================================================================

/-- Direct primes sorted -/
theorem tier1_sorted : tier1_primes = [2, 3, 5, 7, 11, 13, 17, 19, 31, 61] := rfl

/-- Tier 1 covers the first 6 primes (2, 3, 5, 7, 11, 13) -/
theorem tier1_covers_first_6 :
    (2 ∈ tier1_primes) ∧
    (3 ∈ tier1_primes) ∧
    (5 ∈ tier1_primes) ∧
    (7 ∈ tier1_primes) ∧
    (11 ∈ tier1_primes) ∧
    (13 ∈ tier1_primes) := by
  simp only [tier1_primes]
  repeat (first | constructor | decide)

/-- Tier 1 covers 17, 19, 31, 61 -/
theorem tier1_covers_special :
    (17 ∈ tier1_primes) ∧
    (19 ∈ tier1_primes) ∧
    (31 ∈ tier1_primes) ∧
    (61 ∈ tier1_primes) := by
  simp only [tier1_primes]
  repeat (first | constructor | decide)

-- =============================================================================
-- PRIME GAPS IN TIER 1
-- =============================================================================

/-- Missing small primes between 17 and 61 -/
-- 23, 29, 37, 41, 43, 47, 53, 59 need Tier 2 expressions
theorem tier1_gaps :
    ¬(23 ∈ tier1_primes) ∧
    ¬(29 ∈ tier1_primes) ∧
    ¬(37 ∈ tier1_primes) := by
  simp only [tier1_primes]
  repeat (first | constructor | decide)

-- =============================================================================
-- MASTER THEOREM
-- =============================================================================

/-- All 10 Tier 1 prime relations certified -/
theorem all_tier1_relations_certified :
    -- Direct GIFT constant primality
    Nat.Prime p2 ∧
    Nat.Prime N_gen ∧
    Nat.Prime Weyl_factor ∧
    Nat.Prime dim_K7 ∧
    Nat.Prime D_bulk ∧
    Nat.Prime (13 : Nat) ∧  -- alpha_sq_B_sum
    Nat.Prime lambda_H_num ∧
    Nat.Prime prime_8 ∧
    Nat.Prime prime_11 ∧
    Nat.Prime (61 : Nat) :=  -- kappa_T_inv
  ⟨p2_is_prime, N_gen_is_prime, Weyl_is_prime, dim_K7_is_prime, D_bulk_is_prime,
   alpha_B_sum_is_prime, lambda_H_is_prime, prime_8_is_prime, prime_11_is_prime,
   kappa_T_inv_is_prime⟩

end GIFT.Primes.Tier1
