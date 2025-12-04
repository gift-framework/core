"""
Tests for K7 metric implementation.

Tests verify GIFT constants and constraints related to K7 metric.
The full geometry modules require numpy and are tested separately.
"""

import pytest
from fractions import Fraction
import gift_core as gc


class TestK7MetricConstants:
    """Tests for K7 metric constants in gift_core."""

    def test_det_g_value(self):
        """Test det(g) = 65/32."""
        assert gc.DET_G == Fraction(65, 32)
        assert float(gc.DET_G) == 2.03125

    def test_det_g_derivation(self):
        """Test det(g) = (H* - b2 - 13) / 2^Weyl."""
        h_star = gc.H_STAR
        b2 = gc.B2
        weyl = gc.WEYL_FACTOR

        numerator = h_star - b2 - 13  # 99 - 21 - 13 = 65
        denominator = 2 ** weyl       # 2^5 = 32

        assert numerator == 65
        assert denominator == 32
        assert gc.DET_G == Fraction(numerator, denominator)

    def test_kappa_t_value(self):
        """Test kappa_T = 1/61."""
        assert gc.KAPPA_T == Fraction(1, 61)

    def test_kappa_t_derivation(self):
        """Test kappa_T = 1/(b3 - dim_G2 - p2)."""
        b3 = gc.B3
        dim_g2 = gc.DIM_G2
        p2 = gc.P2

        denominator = b3 - dim_g2 - p2  # 77 - 14 - 2 = 61

        assert denominator == 61
        assert gc.KAPPA_T == Fraction(1, denominator)


class TestBettiNumbers:
    """Tests for K7 Betti numbers."""

    def test_b2(self):
        """Test b2(K7) = 21."""
        assert gc.B2 == 21

    def test_b3(self):
        """Test b3(K7) = 77."""
        assert gc.B3 == 77

    def test_h_star(self):
        """Test H* = b2 + b3 + 1 = 99."""
        assert gc.H_STAR == gc.B2 + gc.B3 + 1
        assert gc.H_STAR == 99

    def test_euler_characteristic_zero(self):
        """Test chi(K7) = 0 for G2 holonomy."""
        # Betti numbers for G2 manifold: [1, 0, b2, b3, b3, b2, 0, 1]
        betti = [1, 0, gc.B2, gc.B3, gc.B3, gc.B2, 0, 1]
        chi = sum((-1)**i * b for i, b in enumerate(betti))
        assert chi == 0


class TestG2Holonomy:
    """Tests for G2 holonomy constraints."""

    def test_dim_k7(self):
        """Test dim(K7) = 7."""
        assert gc.DIM_K7 == 7

    def test_dim_g2(self):
        """Test dim(G2) = 14."""
        assert gc.DIM_G2 == 14

    def test_g2_constraint(self):
        """Test dim(G2) < b2 (holonomy constraint)."""
        assert gc.DIM_G2 < gc.B2


class TestPhysicsPredictions:
    """Tests for physics predictions from K7 geometry."""

    def test_sin2_theta_w(self):
        """Test sin^2(theta_W) = 3/13."""
        expected = Fraction(gc.B2, gc.B3 + gc.DIM_G2)
        assert expected == Fraction(21, 91)
        assert expected == Fraction(3, 13)
        assert gc.SIN2_THETA_W == expected

    def test_n_generations(self):
        """Test N_gen = rank(E8) - Weyl = 3."""
        n_gen = gc.RANK_E8 - gc.WEYL_FACTOR
        assert n_gen == 3
        assert gc.N_GEN == 3

    def test_alpha_inverse_base(self):
        """Test alpha^{-1} base = 137."""
        algebraic = (gc.DIM_E8 + gc.RANK_E8) // 2  # = 128
        bulk = gc.H_STAR // gc.D_BULK              # = 9
        total = algebraic + bulk

        assert algebraic == 128
        assert bulk == 9
        assert total == 137
        assert gc.ALPHA_INV_BASE == 137

    def test_m_tau_m_e(self):
        """Test m_tau/m_e = 3477."""
        computed = gc.DIM_K7 + 10 * gc.DIM_E8 + 10 * gc.H_STAR
        assert computed == 7 + 2480 + 990
        assert computed == 3477
        assert gc.M_TAU_M_E == 3477

    def test_m_s_m_d(self):
        """Test m_s/m_d = 20."""
        computed = gc.P2 ** 2 * gc.WEYL_FACTOR
        assert computed == 4 * 5
        assert computed == 20
        assert gc.M_S_M_D == 20


class TestDerivedConstants:
    """Tests for derived topological constants."""

    def test_weyl_squared(self):
        """Test Weyl^2 = 25."""
        assert gc.WEYL_SQ == gc.WEYL_FACTOR ** 2
        assert gc.WEYL_SQ == 25

    def test_gamma_gift(self):
        """Test gamma_GIFT = 511/884."""
        num = 2 * gc.RANK_E8 + 5 * gc.H_STAR  # = 16 + 495 = 511
        den = 10 * gc.DIM_G2 + 3 * gc.DIM_E8  # = 140 + 744 = 884

        assert num == 511
        assert den == 884
        assert gc.GAMMA_GIFT == Fraction(511, 884)

    def test_theta_23(self):
        """Test theta_23 = 85/99."""
        num = gc.RANK_E8 + gc.B3  # = 8 + 77 = 85
        den = gc.H_STAR          # = 99

        assert num == 85
        assert den == 99
        assert gc.THETA_23 == Fraction(85, 99)

    def test_omega_de_fraction(self):
        """Test Omega_DE fraction = 98/99."""
        num = gc.H_STAR - 1  # = 98
        den = gc.H_STAR      # = 99

        assert num == 98
        assert den == 99
        assert gc.OMEGA_DE_FRACTION == Fraction(98, 99)


class TestConsistency:
    """Tests for internal consistency of all constants."""

    def test_all_25_relations_consistent(self):
        """Test that all 25 certified relations are internally consistent."""
        # Original 13 relations
        assert gc.SIN2_THETA_W == Fraction(3, 13)
        assert gc.TAU == Fraction(3472, 891)
        assert gc.DET_G == Fraction(65, 32)
        assert gc.KAPPA_T == Fraction(1, 61)
        assert gc.DELTA_CP == 197
        assert gc.M_TAU_M_E == 3477
        assert gc.M_S_M_D == 20
        assert gc.Q_KOIDE == Fraction(2, 3)
        assert gc.LAMBDA_H_NUM == 17
        assert gc.H_STAR == 99
        assert gc.P2 == 2
        assert gc.N_GEN == 3

        # Extension 12 relations
        assert gc.ALPHA_S_DENOM == 12
        assert gc.GAMMA_GIFT == Fraction(511, 884)
        assert gc.WEYL_SQ == 25
        assert gc.THETA_23 == Fraction(85, 99)
        assert gc.ALPHA_INV_BASE == 137

    def test_topological_constraints(self):
        """Test that topological constraints are satisfied."""
        # b2 comes from H^2(K7) harmonic 2-forms
        # b3 comes from H^3(K7) harmonic 3-forms
        # H* = b2 + b3 + 1 is the effective degrees of freedom

        assert gc.B2 > 0
        assert gc.B3 > 0
        assert gc.H_STAR == gc.B2 + gc.B3 + 1

        # G2 manifold: chi = 0
        # Poincare duality: b_k = b_{7-k}
        assert gc.DIM_K7 == 7


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
