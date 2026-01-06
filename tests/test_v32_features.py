"""
Tests for GIFT v3.2 features:
- TCS Building Blocks
- Weyl Triple Identity
- PSL(2,7) = 168
- E8 Roots
- Fano Plane / G2 Cross Product
"""
import pytest
from fractions import Fraction


class TestTCSBuildingBlocks:
    """Test TCS construction derives both Betti numbers."""

    def test_b2_derivation(self):
        from gift_core.constants import M1_B2, M2_B2, B2
        assert M1_B2 + M2_B2 == B2
        assert B2 == 21

    def test_b3_derivation(self):
        from gift_core.constants import M1_B3, M2_B3, B3
        assert M1_B3 + M2_B3 == B3
        assert B3 == 77

    def test_h_star_derivation(self):
        from gift_core.constants import B2, B3, H_STAR
        assert B2 + B3 + 1 == H_STAR
        assert H_STAR == 99

    def test_building_block_values(self):
        from gift_core.constants import M1_B2, M1_B3, M2_B2, M2_B3
        # M1 = Quintic in CP^4
        assert M1_B2 == 11
        assert M1_B3 == 40
        # M2 = CI(2,2,2) in CP^6
        assert M2_B2 == 10
        assert M2_B3 == 37


class TestWeylTripleIdentity:
    """Test three independent derivations of Weyl = 5."""

    def test_path_1(self):
        from gift_core.constants import DIM_G2, N_GEN, WEYL_FACTOR
        assert (DIM_G2 + 1) // N_GEN == WEYL_FACTOR
        assert WEYL_FACTOR == 5

    def test_path_2(self):
        from gift_core.constants import B2, N_GEN, P2, WEYL_FACTOR
        assert B2 // N_GEN - P2 == WEYL_FACTOR

    def test_path_3(self):
        from gift_core.constants import DIM_G2, RANK_E8, WEYL_FACTOR
        assert DIM_G2 - RANK_E8 - 1 == WEYL_FACTOR


class TestPSL27:
    """Test PSL(2,7) = 168 derivations."""

    def test_order(self):
        from gift_core.constants import PSL27_ORDER
        assert PSL27_ORDER == 168

    def test_path_1(self):
        from gift_core.constants import B3, DIM_G2, PSL27_ORDER
        assert (B3 + DIM_G2) + B3 == PSL27_ORDER

    def test_path_2(self):
        from gift_core.constants import RANK_E8, B2, PSL27_ORDER
        assert RANK_E8 * B2 == PSL27_ORDER

    def test_path_3(self):
        from gift_core.constants import N_GEN, B3, B2, PSL27_ORDER
        assert N_GEN * (B3 - B2) == PSL27_ORDER


class TestE8Roots:
    """Test E8 root system."""

    def test_root_count(self):
        from gift_core.roots import E8_ROOTS, D8_ROOTS, HALF_INTEGER_ROOTS
        assert len(E8_ROOTS) == 240
        assert len(D8_ROOTS) == 112
        assert len(HALF_INTEGER_ROOTS) == 128

    def test_simple_roots(self):
        from gift_core.roots import E8_SIMPLE_ROOTS
        assert len(E8_SIMPLE_ROOTS) == 8

    def test_root_norm(self):
        from gift_core.roots import E8_ROOTS, norm_sq
        # All E8 roots have norm^2 = 2
        for root in E8_ROOTS[:10]:  # Test first 10
            assert abs(norm_sq(root) - 2.0) < 1e-10

    def test_simple_root_values(self):
        from gift_core.roots import ALPHA_1, ALPHA_8
        # α₁ = (1, -1, 0, 0, 0, 0, 0, 0)
        assert ALPHA_1 == (1, -1, 0, 0, 0, 0, 0, 0)
        # α₈ has half-integer coordinates
        assert ALPHA_8[0] == -0.5

    def test_weyl_reflection(self):
        from gift_core.roots import weyl_reflection, ALPHA_1, norm_sq
        v = (1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
        reflected = weyl_reflection(v, ALPHA_1)
        # Reflection preserves norm
        assert abs(norm_sq(v) - norm_sq(reflected)) < 1e-10


class TestFanoPlane:
    """Test Fano plane and G2 cross product."""

    def test_fano_lines(self):
        from gift_core.fano import FANO_LINES
        assert len(FANO_LINES) == 7
        for line in FANO_LINES:
            assert len(line) == 3

    def test_epsilon_antisymmetry(self):
        from gift_core.fano import epsilon
        for i in range(7):
            for j in range(7):
                for k in range(7):
                    assert epsilon(i, j, k) == -epsilon(j, i, k)

    def test_cross_product_antisymmetry(self):
        from gift_core.fano import cross_product
        u = (1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
        v = (0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0)
        uv = cross_product(u, v)
        vu = cross_product(v, u)
        # u × v = -v × u
        for k in range(7):
            assert abs(uv[k] + vu[k]) < 1e-10

    def test_lagrange_identity(self):
        from gift_core.fano import verify_lagrange_identity
        u = (1.0, 2.0, 0.0, 0.0, 0.0, 0.0, 0.0)
        v = (0.0, 1.0, 3.0, 0.0, 0.0, 0.0, 0.0)
        assert verify_lagrange_identity(u, v)

    def test_fano_properties(self):
        from gift_core.fano import verify_fano_properties
        props = verify_fano_properties()
        assert all(props.values())


class TestVerification:
    """Test verification module."""

    def test_verify_all_pass(self):
        from gift_core.verify import verify
        assert verify() is True

    def test_verify_summary(self):
        from gift_core.verify import verify_summary
        summary = verify_summary()
        assert summary['all_passed'] is True
        assert summary['failed'] == 0


class TestPhysicalRelations:
    """Test physical relations are correctly defined."""

    def test_weinberg_angle(self):
        from gift_core.constants import SIN2_THETA_W, B2, B3, DIM_G2
        assert SIN2_THETA_W == Fraction(3, 13)
        assert Fraction(B2, B3 + DIM_G2) == Fraction(3, 13)

    def test_koide(self):
        from gift_core.constants import Q_KOIDE, DIM_G2, B2
        assert Q_KOIDE == Fraction(2, 3)
        assert Fraction(DIM_G2, B2) == Fraction(2, 3)

    def test_kappa_t(self):
        from gift_core.constants import KAPPA_T, KAPPA_T_INV, B3, DIM_G2, P2
        assert KAPPA_T == Fraction(1, 61)
        assert KAPPA_T_INV == 61
        assert B3 - DIM_G2 - P2 == 61


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
