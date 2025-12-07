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
