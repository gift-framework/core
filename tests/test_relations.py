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
