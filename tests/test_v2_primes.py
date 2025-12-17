"""
Tests for GIFT v2.0 Primes module.
Verifies prime coverage and expressions.
"""

import pytest
from gift_core.primes import (
    TIER1_PRIMES, TIER2_PRIMES, TIER3_PRIMES, TIER4_PRIMES,
    HEEGNER_NUMBERS, SPECIAL_PRIMES, GENERATORS,
    prime_expression, prime_generator, is_gift_prime,
    is_heegner, verify_prime_coverage,
)
from gift_core import (
    P2, N_GEN, WEYL_FACTOR, DIM_K7, D_BULK, RANK_E8,
    B2, B3, H_STAR, DIM_E8, DIM_G2,
)


def is_prime(n: int) -> bool:
    """Simple primality test."""
    if n < 2:
        return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0:
            return False
    return True


class TestTier1Primes:
    """Test direct GIFT constant primes (p₂, N_gen, Weyl, etc.)."""

    def test_tier1_count(self):
        assert len(TIER1_PRIMES) == 10

    def test_tier1_primes_are_prime(self):
        for p in TIER1_PRIMES:
            assert is_prime(p), f"{p} is not prime"

    def test_tier1_p2(self):
        assert 2 in TIER1_PRIMES
        assert TIER1_PRIMES[2] == "p2"

    def test_tier1_N_gen(self):
        assert 3 in TIER1_PRIMES
        assert TIER1_PRIMES[3] == "N_gen"

    def test_tier1_Weyl(self):
        assert 5 in TIER1_PRIMES
        assert TIER1_PRIMES[5] == "Weyl_factor"

    def test_tier1_dim_K7(self):
        assert 7 in TIER1_PRIMES
        assert TIER1_PRIMES[7] == "dim_K7"

    def test_tier1_D_bulk(self):
        assert 11 in TIER1_PRIMES
        assert TIER1_PRIMES[11] == "D_bulk"

    def test_tier1_alpha_sum(self):
        assert 13 in TIER1_PRIMES
        assert TIER1_PRIMES[13] == "alpha_sq_B_sum"

    def test_tier1_lambda_H(self):
        assert 17 in TIER1_PRIMES
        assert TIER1_PRIMES[17] == "lambda_H_num"

    def test_tier1_kappa_T_inv(self):
        assert 61 in TIER1_PRIMES
        assert TIER1_PRIMES[61] == "kappa_T_inv"


class TestTier2Primes:
    """Test derived primes < 100 via GIFT expressions (23 = b₂ + p₂, etc.)."""

    def test_tier2_count(self):
        assert len(TIER2_PRIMES) == 15

    def test_tier2_primes_are_prime(self):
        for p in TIER2_PRIMES:
            assert is_prime(p), f"{p} is not prime"

    def test_prime_23(self):
        assert 23 in TIER2_PRIMES
        assert 23 == B2 + P2

    def test_prime_43(self):
        assert 43 in TIER2_PRIMES
        assert TIER2_PRIMES[43] == "visible_dim"

    def test_prime_67(self):
        assert 67 in TIER2_PRIMES
        assert 67 == B3 - 2 * WEYL_FACTOR

    def test_prime_71(self):
        assert 71 in TIER2_PRIMES
        assert 71 == B3 - 6

    def test_prime_73(self):
        assert 73 in TIER2_PRIMES
        assert 73 == B3 - P2 * P2

    def test_prime_97(self):
        assert 97 in TIER2_PRIMES
        assert 97 == H_STAR - P2


class TestPrimeCoverage:
    """Test complete prime coverage."""

    def test_verify_coverage_below_100(self):
        assert verify_prime_coverage(100) is True

    def test_all_primes_below_100_covered(self):
        primes_below_100 = [p for p in range(2, 100) if is_prime(p)]
        for p in primes_below_100:
            assert is_gift_prime(p), f"Prime {p} not GIFT-expressible"


class TestHeegnerNumbers:
    """Test Heegner number expressions."""

    def test_heegner_count(self):
        assert len(HEEGNER_NUMBERS) == 9

    def test_heegner_list(self):
        expected = [1, 2, 3, 7, 11, 19, 43, 67, 163]
        assert sorted(HEEGNER_NUMBERS.keys()) == expected

    def test_heegner_1(self):
        assert 1 in HEEGNER_NUMBERS

    def test_heegner_2_is_p2(self):
        assert 2 in HEEGNER_NUMBERS
        assert 2 == P2

    def test_heegner_3_is_N_gen(self):
        assert 3 in HEEGNER_NUMBERS
        assert 3 == N_GEN

    def test_heegner_7_is_dim_K7(self):
        assert 7 in HEEGNER_NUMBERS
        assert 7 == DIM_K7

    def test_heegner_11_is_D_bulk(self):
        assert 11 in HEEGNER_NUMBERS
        assert 11 == D_BULK

    def test_heegner_67(self):
        assert 67 in HEEGNER_NUMBERS
        assert 67 == B3 - 2 * WEYL_FACTOR

    def test_heegner_163(self):
        assert 163 in HEEGNER_NUMBERS
        assert 163 == DIM_E8 - RANK_E8 - B3

    def test_is_heegner_function(self):
        assert is_heegner(1) is True
        assert is_heegner(7) is True
        assert is_heegner(163) is True
        assert is_heegner(10) is False
        assert is_heegner(100) is False


class TestThreeGenerators:
    """Test three-generator structure."""

    def test_generators(self):
        assert GENERATORS["b3"] == 77
        assert GENERATORS["H_star"] == 99
        assert GENERATORS["dim_E8"] == 248

    def test_prime_generator_ranges(self):
        # b3 range: 30-90
        assert prime_generator(59) == "b3"
        assert prime_generator(67) == "b3"
        assert prime_generator(71) == "b3"

        # H* range: 90-150
        assert prime_generator(97) == "H_star"
        assert prime_generator(127) == "H_star"

        # E8 range: 150-250
        assert prime_generator(163) == "dim_E8"
        assert prime_generator(197) == "dim_E8"


class TestSpecialPrimes:
    """Test special mathematically significant primes."""

    def test_mersenne_127(self):
        assert 127 in SPECIAL_PRIMES
        assert 127 == 2**DIM_K7 - 1

    def test_delta_CP_197(self):
        assert 197 in SPECIAL_PRIMES
        assert 197 == DIM_K7 * DIM_G2 + H_STAR

    def test_hubble_primes(self):
        assert 67 in SPECIAL_PRIMES  # CMB
        assert 73 in SPECIAL_PRIMES  # Local

    def test_hubble_tension(self):
        assert 73 - 67 == 6
        assert 73 - 67 == 2 * N_GEN


class TestPrimeExpressions:
    """Test prime expression lookup."""

    def test_tier1_expressions(self):
        assert prime_expression(2) == "p2"
        assert prime_expression(7) == "dim_K7"
        assert prime_expression(61) == "kappa_T_inv"

    def test_tier2_expressions(self):
        assert prime_expression(23) == "b2 + p2"
        assert prime_expression(67) == "b3 - 2 * Weyl_factor"

    def test_nonexistent_expression(self):
        assert prime_expression(1000) is None
