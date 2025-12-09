"""
Tests for GIFT v2.0 Monster and McKay modules.
Verifies Monster group and McKay correspondence relations.
"""

import pytest
from gift_core.monster import (
    MONSTER_DIM, MONSTER_FACTORS, MONSTER_FACTOR_EXPRESSIONS,
    verify_monster_factorization, monster_factor_arithmetic_progression,
    J_CONSTANT, J_CONSTANT_FACTORED, J_COEFF_1,
    verify_j_constant, verify_moonshine, j_E8_relations,
)
from gift_core.mckay import (
    COXETER_E8, ICOSAHEDRON, BINARY_GROUPS, E8_KISSING_NUMBER,
    verify_mckay_coxeter, verify_euler_icosahedron, verify_E8_kissing,
    ICOSAHEDRAL_ANGLE, PENTAGON_ANGLE, PHI_APPROX,
    golden_emergence_chain, phi_deviation, PHI_RATIOS,
    ADE_BINARY_ORDERS,
)
from gift_core import (
    N_GEN, DIM_E8, DIM_E8xE8, RANK_E8, B3, DIM_G2, P2, M_S_M_D,
    DIM_K7, WEYL_FACTOR,
)
from gift_core.sequences import lucas


class TestMonsterDimension:
    """Test Monster group dimension factorization."""

    def test_monster_dim_value(self):
        assert MONSTER_DIM == 196883

    def test_monster_factorization(self):
        assert verify_monster_factorization() is True
        assert 47 * 59 * 71 == MONSTER_DIM

    def test_monster_factors(self):
        assert MONSTER_FACTORS == (47, 59, 71)

    def test_factor_47_is_lucas_8(self):
        assert MONSTER_FACTORS[0] == lucas(8)
        assert 47 == lucas(8)

    def test_factor_59_from_b3(self):
        assert MONSTER_FACTORS[1] == B3 - 18
        assert 59 == B3 - lucas(6)

    def test_factor_71_from_b3(self):
        assert MONSTER_FACTORS[2] == B3 - 6
        assert 71 == B3 - 6

    def test_arithmetic_progression(self):
        d1, d2 = monster_factor_arithmetic_progression()
        assert d1 == 12
        assert d2 == 12
        # Common difference is alpha_s_denom
        assert 12 == DIM_G2 - P2


class TestJInvariant:
    """Test j-invariant relations."""

    def test_j_constant_value(self):
        assert J_CONSTANT == 744

    def test_j_constant_factorization(self):
        assert verify_j_constant() is True
        assert J_CONSTANT == N_GEN * DIM_E8
        assert 744 == 3 * 248

    def test_j_constant_factors(self):
        assert J_CONSTANT_FACTORED == (3, 248)

    def test_monstrous_moonshine(self):
        assert verify_moonshine() is True
        assert J_COEFF_1 == MONSTER_DIM + 1
        assert 196884 == 196883 + 1

    def test_j_E8_relations(self):
        relations = j_E8_relations()
        assert relations["j_constant"] == 744
        assert relations["j_div_3"] == 248  # = dim_E8
        assert relations["j_div_248"] == 3  # = N_gen
        assert relations["j_minus_E8"] == 496  # = dim_E8xE8


class TestMcKayCorrespondence:
    """Test McKay correspondence relations."""

    def test_coxeter_E8(self):
        assert COXETER_E8 == 30

    def test_coxeter_equals_icosahedron_edges(self):
        assert verify_mckay_coxeter() is True
        assert COXETER_E8 == ICOSAHEDRON["edges"]

    def test_icosahedron_geometry(self):
        assert ICOSAHEDRON["vertices"] == 12
        assert ICOSAHEDRON["edges"] == 30
        assert ICOSAHEDRON["faces"] == 20

    def test_icosahedron_vertices_gift(self):
        assert ICOSAHEDRON["vertices"] == DIM_G2 - P2

    def test_icosahedron_faces_gift(self):
        assert ICOSAHEDRON["faces"] == M_S_M_D

    def test_euler_icosahedron(self):
        assert verify_euler_icosahedron() is True
        V, E, F = 12, 30, 20
        assert V - E + F == 2
        assert V - E + F == P2

    def test_binary_icosahedral(self):
        assert BINARY_GROUPS["icosahedral"] == 120
        assert BINARY_GROUPS["octahedral"] == 48
        assert BINARY_GROUPS["tetrahedral"] == 24

    def test_E8_kissing_number(self):
        assert verify_E8_kissing() is True
        assert E8_KISSING_NUMBER == 240
        assert E8_KISSING_NUMBER == 2 * BINARY_GROUPS["icosahedral"]
        assert E8_KISSING_NUMBER == RANK_E8 * COXETER_E8


class TestGoldenEmergence:
    """Test golden ratio emergence from McKay chain."""

    def test_icosahedral_angle(self):
        assert ICOSAHEDRAL_ANGLE == 72
        assert ICOSAHEDRAL_ANGLE == 360 // WEYL_FACTOR

    def test_pentagon_angle(self):
        assert PENTAGON_ANGLE == 108
        assert ICOSAHEDRAL_ANGLE + PENTAGON_ANGLE == 180  # Supplementary

    def test_phi_approx(self):
        assert abs(PHI_APPROX - 1.618) < 0.01

    def test_golden_emergence_chain(self):
        chain = golden_emergence_chain()
        assert "E8" in chain["step1"]
        assert "icosahedral" in chain["step3"].lower()
        assert "phi" in chain["step5"].lower()

    def test_phi_deviation_function(self):
        # 21/13 = 1.615... vs phi = 1.618...
        dev = phi_deviation(21, 13)
        assert dev < 0.2  # Less than 0.2%

    def test_phi_ratios(self):
        assert "b2/alpha_sum" in PHI_RATIOS
        assert "hidden/b2" in PHI_RATIOS

    def test_coxeter_gift_expression(self):
        # 30 = 2 x 3 x 5 = p2 x N_gen x Weyl_factor
        assert COXETER_E8 == P2 * N_GEN * WEYL_FACTOR


class TestADEClassification:
    """Test ADE classification of binary groups."""

    def test_binary_group_orders(self):
        assert ADE_BINARY_ORDERS["E_6"] == 24
        assert ADE_BINARY_ORDERS["E_7"] == 48
        assert ADE_BINARY_ORDERS["E_8"] == 120

    def test_binary_group_progression(self):
        # 24 -> 48 -> 120
        assert BINARY_GROUPS["octahedral"] == 2 * BINARY_GROUPS["tetrahedral"]
