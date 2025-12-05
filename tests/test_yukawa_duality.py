"""
Tests for Yukawa Duality relations (v1.3.0).

All identities are formally verified in Lean 4 and Coq.
These tests validate the Python implementation matches the proofs.
"""
import pytest
from gift_core import (
    # Fundamental constants
    DIM_K7, DIM_G2, RANK_E8, DIM_J3O, B3, P2, N_GEN, WEYL_FACTOR,
    # Yukawa duality constants
    VISIBLE_DIM, HIDDEN_DIM,
    ALPHA_SQ_LEPTON_A, ALPHA_SQ_UP_A, ALPHA_SQ_DOWN_A,
    ALPHA_SUM_A, ALPHA_PROD_A,
    ALPHA_SQ_LEPTON_B, ALPHA_SQ_UP_B, ALPHA_SQ_DOWN_B,
    ALPHA_SUM_B, ALPHA_PROD_B,
    DUALITY_GAP, DUALITY_GAP_FROM_COLOR, KAPPA_T_INV,
)


class TestStructureA:
    """Tests for Structure A (Topological) alpha^2 = {2, 3, 7}."""

    def test_alpha_sq_lepton_a(self):
        """alpha^2_lepton (A) = 2 from Q = 2/3 constraint."""
        assert ALPHA_SQ_LEPTON_A == 2

    def test_alpha_sq_up_a(self):
        """alpha^2_up (A) = 3 from K3 signature_+."""
        assert ALPHA_SQ_UP_A == 3

    def test_alpha_sq_down_a(self):
        """alpha^2_down (A) = 7 = dim(K7)."""
        assert ALPHA_SQ_DOWN_A == 7
        assert ALPHA_SQ_DOWN_A == DIM_K7

    def test_alpha_sum_a(self):
        """Sum: 2 + 3 + 7 = 12 = dim(SM gauge)."""
        assert ALPHA_SUM_A == 12
        assert ALPHA_SQ_LEPTON_A + ALPHA_SQ_UP_A + ALPHA_SQ_DOWN_A == 12

    def test_alpha_prod_a(self):
        """Product: 2 * 3 * 7 = 42."""
        assert ALPHA_PROD_A == 42
        assert ALPHA_SQ_LEPTON_A * ALPHA_SQ_UP_A * ALPHA_SQ_DOWN_A == 42

    def test_alpha_prod_a_plus_one_visible(self):
        """Product + 1 = 43 = visible_dim."""
        assert ALPHA_PROD_A + 1 == 43
        assert ALPHA_PROD_A + 1 == VISIBLE_DIM


class TestStructureB:
    """Tests for Structure B (Dynamical) alpha^2 = {2, 5, 6}."""

    def test_alpha_sq_lepton_b(self):
        """alpha^2_lepton (B) = 2 (unchanged, no color)."""
        assert ALPHA_SQ_LEPTON_B == 2
        assert ALPHA_SQ_LEPTON_B == ALPHA_SQ_LEPTON_A

    def test_alpha_sq_up_b(self):
        """alpha^2_up (B) = 5 = Weyl factor."""
        assert ALPHA_SQ_UP_B == 5
        assert ALPHA_SQ_UP_B == WEYL_FACTOR

    def test_alpha_sq_up_b_from_k7(self):
        """alpha^2_up (B) = dim(K7) - p2."""
        assert ALPHA_SQ_UP_B == DIM_K7 - P2

    def test_alpha_sq_down_b(self):
        """alpha^2_down (B) = 6 = 2 * N_gen."""
        assert ALPHA_SQ_DOWN_B == 6
        assert ALPHA_SQ_DOWN_B == 2 * N_GEN

    def test_alpha_sq_down_b_from_g2(self):
        """alpha^2_down (B) = dim(G2) - rank(E8)."""
        assert ALPHA_SQ_DOWN_B == DIM_G2 - RANK_E8

    def test_alpha_sum_b(self):
        """Sum: 2 + 5 + 6 = 13 = rank(E8) + Weyl."""
        assert ALPHA_SUM_B == 13
        assert ALPHA_SUM_B == RANK_E8 + WEYL_FACTOR

    def test_alpha_prod_b(self):
        """Product: 2 * 5 * 6 = 60."""
        assert ALPHA_PROD_B == 60

    def test_alpha_prod_b_plus_one_kappa(self):
        """Product + 1 = 61 = kappa_T^{-1}."""
        assert ALPHA_PROD_B + 1 == 61
        assert ALPHA_PROD_B + 1 == KAPPA_T_INV


class TestDuality:
    """Tests for the A <-> B duality relations."""

    def test_duality_gap(self):
        """Gap: 61 - 43 = 18."""
        assert DUALITY_GAP == 18
        assert (ALPHA_PROD_B + 1) - (ALPHA_PROD_A + 1) == 18

    def test_gap_from_color(self):
        """Gap = p2 * N_gen^2 (colored sector correction)."""
        assert DUALITY_GAP_FROM_COLOR == 18
        assert DUALITY_GAP == P2 * N_GEN * N_GEN

    def test_transform_lepton(self):
        """Leptons: no transformation (colorless)."""
        assert ALPHA_SQ_LEPTON_A == ALPHA_SQ_LEPTON_B

    def test_transform_up(self):
        """Up quarks: A + p2 = B."""
        assert ALPHA_SQ_UP_A + P2 == ALPHA_SQ_UP_B

    def test_transform_down(self):
        """Down quarks: A - 1 = B."""
        assert ALPHA_SQ_DOWN_A - 1 == ALPHA_SQ_DOWN_B


class TestTorsionMediation:
    """Tests for torsion-mediated relations."""

    def test_kappa_t_inv_from_alpha_b(self):
        """kappa_T^{-1} = Pi(alpha^2_B) + 1."""
        assert KAPPA_T_INV == ALPHA_PROD_B + 1
        assert KAPPA_T_INV == 61

    def test_kappa_t_inv_from_betti(self):
        """kappa_T^{-1} = b3 - dim(G2) - p2."""
        assert KAPPA_T_INV == B3 - DIM_G2 - P2

    def test_gap_hidden_jordan(self):
        """61 - 34 = 27 = dim(J3(O))."""
        assert KAPPA_T_INV - HIDDEN_DIM == DIM_J3O
        assert 61 - 34 == 27

    def test_visible_hidden_gap(self):
        """43 - 34 = 9 = N_gen^2."""
        assert VISIBLE_DIM - HIDDEN_DIM == 9
        assert VISIBLE_DIM - HIDDEN_DIM == N_GEN * N_GEN


class TestVisibleHiddenSectors:
    """Tests for visible/hidden sector dimensions."""

    def test_visible_dim(self):
        """Visible sector = 43."""
        assert VISIBLE_DIM == 43

    def test_hidden_dim(self):
        """Hidden sector = 34."""
        assert HIDDEN_DIM == 34

    def test_visible_hidden_sum(self):
        """visible + hidden = b3."""
        assert VISIBLE_DIM + HIDDEN_DIM == B3
        assert VISIBLE_DIM + HIDDEN_DIM == 77
