"""Tests for GIFT constants - verify against formal proofs."""
from fractions import Fraction
import gift_core as gc

def test_e8_dimension():
    assert gc.DIM_E8 == 248

def test_betti_numbers():
    assert gc.B2 == 21
    assert gc.B3 == 77

def test_weinberg_angle():
    # sin^2(theta_W) = b2/(b3 + dim(G2)) = 21/91 = 3/13
    computed = Fraction(gc.B2, gc.B3 + gc.DIM_G2)
    assert computed == Fraction(3, 13)
    assert gc.SIN2_THETA_W == Fraction(3, 13)

def test_tau():
    # tau = (496*21)/(27*99)
    computed = Fraction(gc.DIM_E8xE8 * gc.B2, gc.DIM_J3O * gc.H_STAR)
    assert computed == Fraction(3472, 891)
    assert gc.TAU == computed

def test_det_g():
    assert gc.DET_G == Fraction(65, 32)

def test_kappa_t():
    # kappa_T = 1/(b3 - dim(G2) - p2) = 1/61
    computed = Fraction(1, gc.B3 - gc.DIM_G2 - gc.P2)
    assert computed == Fraction(1, 61)
    assert gc.KAPPA_T == computed

def test_delta_cp():
    # delta_CP = 7*dim(G2) + H* = 7*14 + 99 = 197
    computed = 7 * gc.DIM_G2 + gc.H_STAR
    assert computed == 197
    assert gc.DELTA_CP == 197

def test_koide():
    # Q = 14/21 = 2/3
    computed = Fraction(gc.DIM_G2, gc.B2)
    assert computed == Fraction(2, 3)
    assert gc.Q_KOIDE == computed

def test_h_star():
    # H* = b2 + b3 + 1 = 21 + 77 + 1 = 99
    computed = gc.B2 + gc.B3 + 1
    assert computed == 99
    assert gc.H_STAR == computed

def test_p2():
    # p2 = dim(G2)/dim(K7) = 14/7 = 2
    computed = gc.DIM_G2 // gc.DIM_K7
    assert computed == 2
    assert gc.P2 == computed

def test_e8xe8_dimension():
    # dim(E8xE8) = 2 * 248 = 496
    computed = 2 * gc.DIM_E8
    assert computed == 496
    assert gc.DIM_E8xE8 == computed
