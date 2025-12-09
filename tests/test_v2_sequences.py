"""
Tests for GIFT v2.0 Sequences module.
Verifies Fibonacci and Lucas embeddings in GIFT constants.
"""

import pytest
from gift_core.sequences import (
    fib, lucas,
    FIBONACCI_GIFT, LUCAS_GIFT,
    fibonacci_index, lucas_index,
    verify_fibonacci_recurrence,
    phi_deviation,
)
from gift_core import (
    P2, N_GEN, WEYL_FACTOR, RANK_E8, B2, DIM_K7, D_BULK,
    HIDDEN_DIM, DIM_E7, DIM_E6, B3, DIM_G2,
)


class TestFibonacciSequence:
    """Test Fibonacci sequence generation."""

    def test_fib_base_cases(self):
        assert fib(0) == 0
        assert fib(1) == 1
        assert fib(2) == 1

    def test_fib_values(self):
        assert fib(3) == 2
        assert fib(4) == 3
        assert fib(5) == 5
        assert fib(6) == 8
        assert fib(7) == 13
        assert fib(8) == 21
        assert fib(9) == 34
        assert fib(10) == 55
        assert fib(11) == 89
        assert fib(12) == 144


class TestLucasSequence:
    """Test Lucas sequence generation."""

    def test_lucas_base_cases(self):
        assert lucas(0) == 2
        assert lucas(1) == 1

    def test_lucas_values(self):
        assert lucas(2) == 3
        assert lucas(3) == 4
        assert lucas(4) == 7
        assert lucas(5) == 11
        assert lucas(6) == 18
        assert lucas(7) == 29
        assert lucas(8) == 47
        assert lucas(9) == 76


class TestFibonacciGIFTEmbedding:
    """Test Fibonacci embedding in GIFT constants."""

    def test_fib_3_is_p2(self):
        assert fib(3) == P2
        assert fib(3) == 2

    def test_fib_4_is_N_gen(self):
        assert fib(4) == N_GEN
        assert fib(4) == 3

    def test_fib_5_is_Weyl(self):
        assert fib(5) == WEYL_FACTOR
        assert fib(5) == 5

    def test_fib_6_is_rank_E8(self):
        assert fib(6) == RANK_E8
        assert fib(6) == 8

    def test_fib_7_is_alpha_sum(self):
        assert fib(7) == 13  # alpha_sq_B_sum
        assert fib(7) == RANK_E8 + WEYL_FACTOR

    def test_fib_8_is_b2(self):
        assert fib(8) == B2
        assert fib(8) == 21

    def test_fib_9_is_hidden_dim(self):
        assert fib(9) == HIDDEN_DIM
        assert fib(9) == 34

    def test_fib_10_is_E7_E6_gap(self):
        assert fib(10) == DIM_E7 - DIM_E6
        assert fib(10) == 55

    def test_fib_11_is_topological_sum(self):
        assert fib(11) == B3 + DIM_G2 - P2
        assert fib(11) == 89

    def test_fib_12_is_alpha_s_sq(self):
        assert fib(12) == (DIM_G2 - P2) ** 2
        assert fib(12) == 144


class TestLucasGIFTEmbedding:
    """Test Lucas embedding in GIFT constants."""

    def test_lucas_0_is_p2(self):
        assert lucas(0) == P2
        assert lucas(0) == 2

    def test_lucas_2_is_N_gen(self):
        assert lucas(2) == N_GEN
        assert lucas(2) == 3

    def test_lucas_4_is_dim_K7(self):
        assert lucas(4) == DIM_K7
        assert lucas(4) == 7

    def test_lucas_5_is_D_bulk(self):
        assert lucas(5) == D_BULK
        assert lucas(5) == 11

    def test_lucas_6_is_duality_gap(self):
        assert lucas(6) == 18
        assert lucas(6) == 61 - 43  # kappa_T_inv - visible_dim

    def test_lucas_8_is_monster_factor(self):
        assert lucas(8) == 47

    def test_lucas_9_is_b3_minus_1(self):
        assert lucas(9) == B3 - 1
        assert lucas(9) == 76


class TestRecurrenceRelations:
    """Test Fibonacci recurrence in GIFT constants."""

    def test_verify_fibonacci_recurrence(self):
        assert verify_fibonacci_recurrence() is True

    def test_weyl_recurrence(self):
        assert WEYL_FACTOR == N_GEN + P2

    def test_rank_recurrence(self):
        assert RANK_E8 == WEYL_FACTOR + N_GEN

    def test_alpha_recurrence(self):
        alpha_sum = 13
        assert alpha_sum == RANK_E8 + WEYL_FACTOR

    def test_b2_recurrence(self):
        alpha_sum = 13
        assert B2 == alpha_sum + RANK_E8

    def test_hidden_recurrence(self):
        alpha_sum = 13
        assert HIDDEN_DIM == B2 + alpha_sum

    def test_b3_is_lucas_product(self):
        # b3 = L_4 * L_5 = 7 * 11 = 77
        assert B3 == lucas(4) * lucas(5)


class TestPhiApproximation:
    """Test golden ratio approximation through GIFT ratios."""

    def test_phi_deviation_b2_alpha(self):
        # 21/13 = 1.615... vs phi = 1.618...
        dev = phi_deviation(21, 13)
        assert dev < 0.2  # Less than 0.2% deviation

    def test_phi_deviation_hidden_b2(self):
        # 34/21 = 1.619... vs phi = 1.618...
        dev = phi_deviation(34, 21)
        assert dev < 0.1  # Less than 0.1% deviation

    def test_phi_deviation_55_34(self):
        # 55/34 = 1.617... vs phi
        dev = phi_deviation(55, 34)
        assert dev < 0.05  # Less than 0.05% deviation


class TestIndexFunctions:
    """Test index lookup functions."""

    def test_fibonacci_index(self):
        assert fibonacci_index(2) == 3
        assert fibonacci_index(3) == 4
        assert fibonacci_index(21) == 8
        assert fibonacci_index(100) == -1  # Not a Fibonacci number

    def test_lucas_index(self):
        assert lucas_index(2) == 0
        assert lucas_index(7) == 4
        assert lucas_index(47) == 8
        assert lucas_index(100) == -1  # Not a Lucas number
