"""
E8 Root System - Actual vectors in R^8.

Provides the 240 roots of E8 as explicit vectors, organized by type:
- D8 roots: 112 vectors (permutations of ±e_i ± e_j)
- Half-integer roots: 128 vectors (even number of minus signs)

Also provides:
- Simple roots (Bourbaki convention)
- Cartan matrix
- Inner product and norm functions
- Root enumeration and filtering

Based on the formal Lean 4 proofs in GIFT.Foundations.RootSystems
and GIFT.Foundations.E8Lattice.
"""
from typing import List, Tuple, Iterator, Optional
from itertools import combinations, product
import math

# Type alias for R^8 vectors
Vector8 = Tuple[float, float, float, float, float, float, float, float]


def inner_product(u: Vector8, v: Vector8) -> float:
    """Compute inner product of two R^8 vectors."""
    return sum(u[i] * v[i] for i in range(8))


def norm_sq(v: Vector8) -> float:
    """Compute squared norm of an R^8 vector."""
    return inner_product(v, v)


def norm(v: Vector8) -> float:
    """Compute norm of an R^8 vector."""
    return math.sqrt(norm_sq(v))


def vector_add(u: Vector8, v: Vector8) -> Vector8:
    """Add two R^8 vectors."""
    return tuple(u[i] + v[i] for i in range(8))


def vector_sub(u: Vector8, v: Vector8) -> Vector8:
    """Subtract two R^8 vectors."""
    return tuple(u[i] - v[i] for i in range(8))


def scalar_mul(c: float, v: Vector8) -> Vector8:
    """Scalar multiplication."""
    return tuple(c * v[i] for i in range(8))


# =============================================================================
# E8 SIMPLE ROOTS (Bourbaki Convention)
# =============================================================================

# α₁ through α₆: D-type roots (e_i - e_{i+1})
ALPHA_1: Vector8 = (1, -1, 0, 0, 0, 0, 0, 0)
ALPHA_2: Vector8 = (0, 1, -1, 0, 0, 0, 0, 0)
ALPHA_3: Vector8 = (0, 0, 1, -1, 0, 0, 0, 0)
ALPHA_4: Vector8 = (0, 0, 0, 1, -1, 0, 0, 0)
ALPHA_5: Vector8 = (0, 0, 0, 0, 1, -1, 0, 0)
ALPHA_6: Vector8 = (0, 0, 0, 0, 0, 1, -1, 0)

# α₇: D-branch connection (e_6 + e_7)
ALPHA_7: Vector8 = (0, 0, 0, 0, 0, 1, 1, 0)

# α₈: Half-integer root
ALPHA_8: Vector8 = (-0.5, -0.5, -0.5, -0.5, -0.5, 0.5, 0.5, -0.5)

# Simple roots list
E8_SIMPLE_ROOTS: List[Vector8] = [
    ALPHA_1, ALPHA_2, ALPHA_3, ALPHA_4,
    ALPHA_5, ALPHA_6, ALPHA_7, ALPHA_8
]


# =============================================================================
# D8 ROOTS (112 total)
# Permutations of (±1, ±1, 0, 0, 0, 0, 0, 0)
# =============================================================================

def generate_d8_roots() -> List[Vector8]:
    """
    Generate all 112 D8 roots.

    These are vectors of the form ±e_i ± e_j where i < j.
    Total: C(8,2) * 4 = 28 * 4 = 112
    """
    roots = []

    for i, j in combinations(range(8), 2):
        for si, sj in product([1, -1], repeat=2):
            v = [0.0] * 8
            v[i] = float(si)
            v[j] = float(sj)
            roots.append(tuple(v))

    return roots


# =============================================================================
# HALF-INTEGER ROOTS (128 total)
# (±1/2, ±1/2, ±1/2, ±1/2, ±1/2, ±1/2, ±1/2, ±1/2) with even # of minus signs
# =============================================================================

def generate_half_integer_roots() -> List[Vector8]:
    """
    Generate all 128 half-integer roots.

    These are vectors with all coordinates ±1/2, and an even number
    of minus signs (equivalently, even coordinate sum).
    Total: 2^8 / 2 = 128
    """
    roots = []

    for signs in product([0.5, -0.5], repeat=8):
        # Check if sum is even (i.e., even number of -1/2's)
        # Sum of n coordinates of ±1/2 is (8-2k)/2 where k = # of -1/2's
        # This is even (integer) when k is even
        num_negative = sum(1 for s in signs if s < 0)
        if num_negative % 2 == 0:
            roots.append(signs)

    return roots


# =============================================================================
# ALL E8 ROOTS
# =============================================================================

D8_ROOTS: List[Vector8] = generate_d8_roots()
HALF_INTEGER_ROOTS: List[Vector8] = generate_half_integer_roots()
E8_ROOTS: List[Vector8] = D8_ROOTS + HALF_INTEGER_ROOTS

# Verification
assert len(D8_ROOTS) == 112, f"D8 roots: expected 112, got {len(D8_ROOTS)}"
assert len(HALF_INTEGER_ROOTS) == 128, f"Half-int roots: expected 128, got {len(HALF_INTEGER_ROOTS)}"
assert len(E8_ROOTS) == 240, f"E8 roots: expected 240, got {len(E8_ROOTS)}"


# =============================================================================
# E8 CARTAN MATRIX
# =============================================================================

def cartan_entry(i: int, j: int) -> int:
    """Compute (i,j) entry of E8 Cartan matrix."""
    if i == j:
        return 2
    alpha_i = E8_SIMPLE_ROOTS[i]
    alpha_j = E8_SIMPLE_ROOTS[j]
    # A_ij = 2 * <α_i, α_j> / <α_j, α_j>
    return round(2 * inner_product(alpha_i, alpha_j) / norm_sq(alpha_j))


E8_CARTAN_MATRIX: List[List[int]] = [
    [cartan_entry(i, j) for j in range(8)]
    for i in range(8)
]


# =============================================================================
# ROOT UTILITIES
# =============================================================================

def is_root(v: Vector8, tolerance: float = 1e-10) -> bool:
    """Check if a vector is an E8 root."""
    for root in E8_ROOTS:
        if all(abs(v[i] - root[i]) < tolerance for i in range(8)):
            return True
    return False


def is_positive_root(v: Vector8) -> bool:
    """
    Check if a root is positive.

    A root is positive if its first nonzero coordinate is positive.
    """
    for coord in v:
        if abs(coord) > 1e-10:
            return coord > 0
    return False


def positive_roots() -> List[Vector8]:
    """Return all 120 positive roots."""
    return [r for r in E8_ROOTS if is_positive_root(r)]


def negative_roots() -> List[Vector8]:
    """Return all 120 negative roots."""
    return [r for r in E8_ROOTS if not is_positive_root(r)]


def root_height(v: Vector8) -> int:
    """
    Compute the height of a root (sum of coefficients in simple root expansion).

    Note: This is approximate for non-simple roots.
    """
    # For simple roots, height = 1
    for i, alpha in enumerate(E8_SIMPLE_ROOTS):
        if all(abs(v[j] - alpha[j]) < 1e-10 for j in range(8)):
            return 1

    # For other positive roots, compute via Cartan matrix
    # This is a simplified version
    return sum(int(abs(c) + 0.5) for c in v if abs(c) > 0.1)


def highest_root() -> Vector8:
    """
    Return the highest root of E8.

    θ = 2α₁ + 3α₂ + 4α₃ + 6α₄ + 5α₅ + 4α₆ + 3α₇ + 2α₈
    """
    coeffs = [2, 3, 4, 6, 5, 4, 3, 2]
    result = [0.0] * 8
    for c, alpha in zip(coeffs, E8_SIMPLE_ROOTS):
        for i in range(8):
            result[i] += c * alpha[i]
    return tuple(result)


# =============================================================================
# WEYL REFLECTION
# =============================================================================

def weyl_reflection(v: Vector8, alpha: Vector8) -> Vector8:
    """
    Apply Weyl reflection s_α to vector v.

    s_α(v) = v - 2<v,α>/<α,α> * α
    """
    coeff = 2 * inner_product(v, alpha) / norm_sq(alpha)
    return tuple(v[i] - coeff * alpha[i] for i in range(8))


# =============================================================================
# E8 LATTICE
# =============================================================================

def is_in_E8_lattice(v: Vector8) -> bool:
    """
    Check if a vector is in the E8 lattice.

    E8 lattice = { v ∈ R^8 : all integer OR all half-integer, with even sum }
    """
    # Check all integer
    all_int = all(abs(v[i] - round(v[i])) < 1e-10 for i in range(8))
    # Check all half-integer
    all_half = all(abs(v[i] - round(v[i]) - 0.5) < 1e-10 or
                   abs(v[i] - round(v[i]) + 0.5) < 1e-10 for i in range(8))

    if not (all_int or all_half):
        return False

    # Check even sum
    s = sum(v)
    return abs(s - round(s)) < 1e-10 and round(s) % 2 == 0


def lattice_basis() -> List[Vector8]:
    """Return a Z-basis for the E8 lattice (the 8 simple roots)."""
    return list(E8_SIMPLE_ROOTS)


# =============================================================================
# SUMMARY STATISTICS
# =============================================================================

def root_statistics() -> dict:
    """Return summary statistics about E8 roots."""
    pos = positive_roots()
    return {
        'total_roots': len(E8_ROOTS),
        'positive_roots': len(pos),
        'negative_roots': len(E8_ROOTS) - len(pos),
        'd8_roots': len(D8_ROOTS),
        'half_integer_roots': len(HALF_INTEGER_ROOTS),
        'simple_roots': len(E8_SIMPLE_ROOTS),
        'root_norm_squared': norm_sq(E8_ROOTS[0]),  # All roots have norm^2 = 2
        'cartan_matrix_rank': 8,
        'coxeter_number': 30,
        'weyl_group_order': 696729600,
    }
