"""
Tests for K7 metric implementation.

Tests the geometry, G2 structure, harmonic forms, and physics modules.
"""

import pytest
import numpy as np
from fractions import Fraction


class TestGeometryModule:
    """Tests for the geometry module."""

    def test_k3_surface_betti(self):
        """Test K3 surface has correct Betti numbers."""
        from geometry.k3_surface import KummerK3

        k3 = KummerK3()
        assert k3.betti == [1, 0, 22, 0, 1], "K3 Betti numbers incorrect"
        assert k3.euler == 24, "K3 Euler characteristic incorrect"

    def test_k3_exceptional_divisors(self):
        """Test K3 has 16 exceptional divisors."""
        from geometry.k3_surface import KummerK3

        k3 = KummerK3()
        assert k3.resolution == 16, "Kummer K3 should have 16 exceptional divisors"

    def test_tcs_betti_numbers(self):
        """Test TCS manifold has GIFT Betti numbers."""
        from geometry.tcs_construction import TCSManifold

        k7 = TCSManifold.from_kovalev()
        betti = k7.betti_numbers()

        assert betti[2] == 21, f"b2 should be 21, got {betti[2]}"
        assert betti[3] == 77, f"b3 should be 77, got {betti[3]}"

    def test_tcs_euler_zero(self):
        """Test G2 manifold has Euler characteristic 0."""
        from geometry.tcs_construction import TCSManifold

        k7 = TCSManifold.from_kovalev()
        chi = k7.euler_characteristic

        assert chi == 0, f"G2 manifold should have chi=0, got {chi}"

    def test_k7_metric_dimension(self):
        """Test K7 metric has correct dimension."""
        from geometry.k7_metric import K7Metric

        metric = K7Metric.default()
        assert metric.dim == 7, "K7 should be 7-dimensional"

    def test_k7_metric_det_target(self):
        """Test K7 metric determinant target is 65/32."""
        from geometry.k7_metric import DET_G_TARGET

        assert DET_G_TARGET == Fraction(65, 32), "det(g) target should be 65/32"

    def test_k7_metric_kappa_target(self):
        """Test K7 kappa_T target is 1/61."""
        from geometry.k7_metric import KAPPA_T_TARGET

        assert KAPPA_T_TARGET == Fraction(1, 61), "kappa_T target should be 1/61"


class TestG2Module:
    """Tests for the G2 structure module."""

    def test_g2_form_components(self):
        """Test G2 3-form has 35 components."""
        from g2.g2_form import G2Form

        phi = G2Form.standard()
        assert phi.components.shape[-1] == 35, "G2 3-form should have 35 components"

    def test_standard_g2_form(self):
        """Test standard G2 form is normalized."""
        from g2.g2_form import standard_g2_form

        phi = standard_g2_form()
        # Standard form should have 7 non-zero components
        n_nonzero = np.sum(np.abs(phi.components) > 0.5)
        assert n_nonzero == 7, f"Standard G2 form should have 7 terms, got {n_nonzero}"

    def test_g2_constraints_targets(self):
        """Test G2 constraints have correct targets."""
        from g2.constraints import G2Constraints, DET_G_TARGET, KAPPA_T_TARGET

        constraints = G2Constraints()

        assert constraints.det_g_target == DET_G_TARGET
        assert constraints.kappa_t_target == KAPPA_T_TARGET
        assert constraints.b2_target == 21
        assert constraints.b3_target == 77


class TestHarmonicModule:
    """Tests for the harmonic forms module."""

    def test_betti_validation_gift(self):
        """Test GIFT Betti number validation."""
        from harmonic.betti_validation import BettiValidator, GIFT_BETTI

        validator = BettiValidator()

        # Test with correct values
        result = validator.validate(GIFT_BETTI)
        assert result['valid'], "GIFT Betti numbers should validate"

    def test_betti_h_star(self):
        """Test H* = b2 + b3 + 1 = 99."""
        from harmonic.betti_validation import GIFT_BETTI

        h_star = GIFT_BETTI[2] + GIFT_BETTI[3] + 1
        assert h_star == 99, f"H* should be 99, got {h_star}"


class TestPhysicsModule:
    """Tests for the physics module."""

    def test_sin2_theta_w(self):
        """Test Weinberg angle is 3/13."""
        from physics.coupling_constants import GIFT_COUPLINGS

        sin2 = GIFT_COUPLINGS.sin2_theta_w
        assert sin2 == Fraction(3, 13), f"sin^2(theta_W) should be 3/13, got {sin2}"

    def test_n_generations(self):
        """Test number of generations is 3."""
        from physics.coupling_constants import GIFT_COUPLINGS

        n_gen = GIFT_COUPLINGS.n_generations
        assert n_gen == 3, f"N_gen should be 3, got {n_gen}"

    def test_alpha_inverse_base(self):
        """Test alpha^{-1} base is 137."""
        from physics.coupling_constants import GIFT_COUPLINGS

        alpha_inv = GIFT_COUPLINGS.alpha_em_inverse_base
        assert alpha_inv == 137, f"alpha^{{-1}} base should be 137, got {alpha_inv}"

    def test_mass_ratios(self):
        """Test GIFT mass ratio predictions."""
        from physics.mass_spectrum import GIFT_MASS_RATIOS

        assert GIFT_MASS_RATIOS['m_tau_m_e'] == 3477
        assert GIFT_MASS_RATIOS['m_s_m_d'] == 20
        assert GIFT_MASS_RATIOS['m_mu_m_e_base'] == 27


class TestVerificationModule:
    """Tests for the verification module."""

    def test_interval_arithmetic(self):
        """Test interval arithmetic operations."""
        from verification.numerical_bounds import IntervalArithmetic

        a = IntervalArithmetic(1.0, 2.0)
        b = IntervalArithmetic(3.0, 4.0)

        # Addition
        c = a + b
        assert c.lo == 4.0 and c.hi == 6.0

        # Contains
        assert a.contains(1.5)
        assert not a.contains(3.0)

    def test_certificate_verification(self):
        """Test certificate verification logic."""
        from verification.certificate import G2Certificate
        from verification.numerical_bounds import IntervalArithmetic
        from fractions import Fraction

        # Create certificate with correct values
        cert = G2Certificate(
            det_g=IntervalArithmetic(2.03, 2.04),  # Contains 65/32 = 2.03125
            kappa_t=IntervalArithmetic(0.016, 0.017),  # Contains 1/61 ~ 0.0164
            betti_2=21,
            betti_3=77
        )

        assert cert.verify(), "Certificate should verify with correct values"

    def test_certificate_fails_wrong_betti(self):
        """Test certificate fails with wrong Betti numbers."""
        from verification.certificate import G2Certificate
        from verification.numerical_bounds import IntervalArithmetic

        cert = G2Certificate(
            det_g=IntervalArithmetic(2.03, 2.04),
            kappa_t=IntervalArithmetic(0.016, 0.017),
            betti_2=20,  # Wrong!
            betti_3=77
        )

        assert not cert.verify(), "Certificate should fail with wrong b2"


class TestPipelineModule:
    """Tests for the pipeline module."""

    def test_config_defaults(self):
        """Test default configuration values."""
        from pipeline.config import default_config

        config = default_config()

        assert config.geometry.resolution == 16
        assert config.training.n_epochs == 1000
        assert config.harmonic.b2_target == 21
        assert config.harmonic.b3_target == 77

    def test_fast_config(self):
        """Test fast configuration has reduced values."""
        from pipeline.config import fast_config

        config = fast_config()

        assert config.geometry.resolution < 16
        assert config.training.n_epochs < 1000


class TestIntegration:
    """Integration tests combining multiple modules."""

    def test_gift_constants_consistent(self):
        """Test all GIFT constants are internally consistent."""
        from gift_core.constants import (
            B2, B3, H_STAR, DIM_G2, DIM_E8, RANK_E8,
            SIN2_THETA_W, KAPPA_T, DET_G
        )

        # H* = b2 + b3 + 1
        assert H_STAR == B2 + B3 + 1, "H* consistency check failed"

        # sin^2(theta_W) = b2 / (b3 + dim_G2)
        expected_sin2 = Fraction(B2, B3 + DIM_G2)
        assert SIN2_THETA_W == expected_sin2, "Weinberg angle consistency failed"

        # kappa_T = 1 / (b3 - dim_G2 - 2)
        expected_kappa = Fraction(1, B3 - DIM_G2 - 2)
        assert KAPPA_T == expected_kappa, "kappa_T consistency failed"

    def test_k7_metric_constraints(self):
        """Test K7 metric satisfies all constraints."""
        from geometry.k7_metric import K7Metric

        metric = K7Metric.default()

        assert metric.b2 == 21
        assert metric.b3 == 77
        assert abs(metric.det_g - 65/32) < 0.01
        assert abs(metric.kappa_t - 1/61) < 0.01


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
