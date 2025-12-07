"""Tests for proven relations."""
from gift_core import PROVEN_RELATIONS, get_relation

def test_relation_count():
    assert len(PROVEN_RELATIONS) == 13

def test_all_have_lean_theorem():
    for r in PROVEN_RELATIONS:
        assert r.lean_theorem, f"{r.name} missing Lean theorem"

def test_all_have_coq_theorem():
    for r in PROVEN_RELATIONS:
        assert r.coq_theorem, f"{r.name} missing Coq theorem"

def test_get_relation():
    w = get_relation("sin^2(theta_W)")
    assert w.name == "Weinberg angle"

def test_get_relation_not_found():
    try:
        get_relation("unknown")
        assert False, "Should have raised KeyError"
    except KeyError as e:
        assert "unknown" in str(e)

def test_relation_repr():
    w = get_relation("sin^2(theta_W)")
    assert "sin^2(theta_W)" in repr(w)
    assert "3/13" in repr(w)


# =============================================================================
# EXCEPTIONAL GROUPS RELATIONS (v1.5.0)
# =============================================================================

from fractions import Fraction


def test_relation_40_alpha_s_squared():
    """alpha_s^2 = 1/72"""
    from gift_core import DIM_G2, DIM_K7, P2, ALPHA_S_SQUARED
    numerator = Fraction(DIM_G2, DIM_K7)
    denominator = (DIM_G2 - P2) ** 2
    result = numerator / denominator
    assert result == Fraction(1, 72)
    assert ALPHA_S_SQUARED == Fraction(1, 72)


def test_relation_41_dim_F4():
    """dim(F4) = p2^2 * sum(alpha^2_B)"""
    from gift_core import DIM_F4, P2, ALPHA_SQ_B_SUM, DIM_F4_FROM_STRUCTURE_B
    assert DIM_F4 == P2**2 * ALPHA_SQ_B_SUM
    assert DIM_F4 == 52
    assert DIM_F4_FROM_STRUCTURE_B == 52


def test_relation_42_delta_penta():
    """dim(F4) - dim(J3O) = 25 = Weyl^2"""
    from gift_core import DIM_F4, DIM_J3O, WEYL_FACTOR, DELTA_PENTA
    assert DIM_F4 - DIM_J3O == 25
    assert DIM_F4 - DIM_J3O == WEYL_FACTOR ** 2
    assert DELTA_PENTA == 25


def test_relation_43_jordan_traceless():
    """dim(E6) - dim(F4) = 26"""
    from gift_core import DIM_E6, DIM_F4, DIM_J3O, JORDAN_TRACELESS
    assert DIM_E6 - DIM_F4 == 26
    assert DIM_E6 - DIM_F4 == DIM_J3O - 1
    assert JORDAN_TRACELESS == 26


def test_relation_44_weyl_E8():
    """|W(E8)| = 2^14 * 3^5 * 5^2 * 7"""
    from gift_core import (
        WEYL_E8_ORDER, P2, DIM_G2, N_GEN, WEYL_FACTOR, DIM_K7, WEYL_E8_FORMULA
    )
    # Direct computation
    assert 2**14 * 3**5 * 5**2 * 7 == 696729600
    assert WEYL_E8_ORDER == 696729600
    # Topological factorization
    topological = P2**DIM_G2 * N_GEN**WEYL_FACTOR * WEYL_FACTOR**P2 * DIM_K7
    assert WEYL_E8_ORDER == topological
    assert WEYL_E8_FORMULA == 696729600


def test_exceptional_chain():
    """dim(E8) - dim(F4) - dim(J3O) = 169 = 13^2"""
    from gift_core import DIM_E8, DIM_F4, DIM_J3O, ALPHA_SQ_B_SUM, EXCEPTIONAL_CHAIN
    chain = DIM_E8 - DIM_F4 - DIM_J3O
    assert chain == 169
    assert chain == 13 ** 2
    assert chain == ALPHA_SQ_B_SUM ** 2
    assert EXCEPTIONAL_CHAIN == 169


def test_exceptional_groups_constants():
    """Verify all exceptional group constants"""
    from gift_core import DIM_F4, DIM_E6, DIM_J3O_TRACELESS, WEYL_E8_ORDER
    assert DIM_F4 == 52
    assert DIM_E6 == 78
    assert DIM_J3O_TRACELESS == 26
    assert WEYL_E8_ORDER == 696729600


# =============================================================================
# BASE DECOMPOSITION RELATIONS (v1.6.0)
# =============================================================================


def test_relation_45_kappa_T_inv_from_F4():
    """kappa_T^-1 = dim(F4) + N_gen^2 = 61"""
    from gift_core import DIM_F4, N_GEN, KAPPA_T_INV_FROM_F4, B3, DIM_G2, P2
    assert DIM_F4 + N_GEN ** 2 == 61
    assert KAPPA_T_INV_FROM_F4 == 61
    # Cross-check with b3 - dim(G2) - p2
    assert B3 - DIM_G2 - P2 == 61


def test_relation_46_b2_decomposition():
    """b2 = ALPHA_SUM_B + rank(E8) = 13 + 8 = 21"""
    from gift_core import B2, ALPHA_SUM_B, RANK_E8, B2_BASE_DECOMPOSITION
    assert ALPHA_SUM_B + RANK_E8 == 21
    assert B2 == 21
    assert B2_BASE_DECOMPOSITION == 21


def test_relation_47_b3_decomposition():
    """b3 = ALPHA_SUM_B * Weyl + 12 = 65 + 12 = 77"""
    from gift_core import (
        B3, ALPHA_SUM_B, WEYL_FACTOR,
        B3_INTERMEDIATE, B3_BASE_DECOMPOSITION
    )
    assert ALPHA_SUM_B * WEYL_FACTOR == 65
    assert B3_INTERMEDIATE == 65
    assert ALPHA_SUM_B * WEYL_FACTOR + 12 == 77
    assert B3 == 77
    assert B3_BASE_DECOMPOSITION == 77


def test_relation_48_H_star_decomposition():
    """H* = ALPHA_SUM_B * dim(K7) + rank(E8) = 91 + 8 = 99"""
    from gift_core import (
        H_STAR, ALPHA_SUM_B, DIM_K7, RANK_E8,
        H_STAR_INTERMEDIATE, H_STAR_BASE_DECOMPOSITION
    )
    assert ALPHA_SUM_B * DIM_K7 == 91
    assert H_STAR_INTERMEDIATE == 91
    assert ALPHA_SUM_B * DIM_K7 + RANK_E8 == 99
    assert H_STAR == 99
    assert H_STAR_BASE_DECOMPOSITION == 99


def test_relation_49_quotient_sum():
    """1 + 5 + 7 = 13 = ALPHA_SUM_B"""
    from gift_core import DIM_U1, WEYL_FACTOR, DIM_K7, ALPHA_SUM_B, QUOTIENT_SUM
    assert DIM_U1 == 1
    assert WEYL_FACTOR == 5
    assert DIM_K7 == 7
    assert DIM_U1 + WEYL_FACTOR + DIM_K7 == 13
    assert QUOTIENT_SUM == 13
    assert QUOTIENT_SUM == ALPHA_SUM_B


def test_relation_50_omega_DE_product():
    """dim(K7) * dim(G2) = 98 = H* - 1"""
    from gift_core import DIM_K7, DIM_G2, H_STAR, OMEGA_DE_PRODUCT
    assert DIM_K7 * DIM_G2 == 98
    assert OMEGA_DE_PRODUCT == 98
    assert OMEGA_DE_PRODUCT == H_STAR - 1


def test_base_decomposition_consistency():
    """All base decompositions are mutually consistent"""
    from gift_core import (
        B2, B3, H_STAR, ALPHA_SUM_B, RANK_E8, WEYL_FACTOR, DIM_K7
    )
    # b2 = 13 + 8
    assert B2 == ALPHA_SUM_B + RANK_E8
    # b3 = 13 * 5 + 12
    assert B3 == ALPHA_SUM_B * WEYL_FACTOR + 12
    # H* = 13 * 7 + 8
    assert H_STAR == ALPHA_SUM_B * DIM_K7 + RANK_E8
    # H* = b2 + b3 + 1
    assert H_STAR == B2 + B3 + 1
