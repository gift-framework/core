"""
Fano Plane and G2 Cross Product.

The Fano plane is the smallest projective plane with 7 points and 7 lines.
It encodes:
- Octonion multiplication table
- G2 cross product structure constants
- PSL(2,7) = Aut(Fano) with order 168

Based on GIFT.Foundations.G2CrossProduct Lean formalization.
"""
from typing import List, Tuple, Dict, Set

# Type aliases
Vector7 = Tuple[float, float, float, float, float, float, float]
Line = Tuple[int, int, int]  # Triple of point indices (0-6)


# =============================================================================
# FANO PLANE STRUCTURE
# =============================================================================

# The 7 lines of the Fano plane (using 0-indexed points)
# Each line contains 3 points, and the orientation gives the sign
FANO_LINES: List[Line] = [
    (0, 1, 3),  # e1 * e2 = e4  (indices shifted: 0,1,3 -> e1,e2,e4)
    (1, 2, 4),  # e2 * e3 = e5
    (2, 3, 5),  # e3 * e4 = e6
    (3, 4, 6),  # e4 * e5 = e7
    (4, 5, 0),  # e5 * e6 = e1
    (5, 6, 1),  # e6 * e7 = e2
    (6, 0, 2),  # e7 * e1 = e3
]

# Alternative common representation (1-indexed, Cayley-Dickson)
FANO_LINES_1INDEXED = [
    (1, 2, 4),
    (2, 3, 5),
    (3, 4, 6),
    (4, 5, 7),
    (5, 6, 1),
    (6, 7, 2),
    (7, 1, 3),
]


def points_on_line(line_idx: int) -> Tuple[int, int, int]:
    """Return the 3 points on the given line (0-6)."""
    return FANO_LINES[line_idx]


def lines_through_point(point: int) -> List[int]:
    """Return indices of the 3 lines through a given point."""
    return [i for i, line in enumerate(FANO_LINES) if point in line]


def third_point(p1: int, p2: int) -> int:
    """
    Given two distinct points, return the third point on their line.

    Returns -1 if p1, p2 are the same or not collinear (shouldn't happen in Fano).
    """
    if p1 == p2:
        return -1
    for line in FANO_LINES:
        if p1 in line and p2 in line:
            for p in line:
                if p != p1 and p != p2:
                    return p
    return -1


def are_collinear(p1: int, p2: int, p3: int) -> bool:
    """Check if three points are collinear (lie on a Fano line)."""
    triple = tuple(sorted([p1, p2, p3]))
    for line in FANO_LINES:
        if tuple(sorted(line)) == triple:
            return True
    return False


# =============================================================================
# EPSILON TENSOR (G2 STRUCTURE CONSTANTS)
# =============================================================================

def compute_epsilon() -> Dict[Tuple[int, int, int], int]:
    """
    Compute the epsilon tensor ε(i,j,k) for the G2 cross product.

    ε(i,j,k) = +1 if (i,j,k) is a cyclic permutation of a Fano line
    ε(i,j,k) = -1 if (i,j,k) is an anti-cyclic permutation
    ε(i,j,k) = 0 otherwise
    """
    epsilon = {}

    # Initialize all to 0
    for i in range(7):
        for j in range(7):
            for k in range(7):
                epsilon[(i, j, k)] = 0

    # Set values from Fano lines
    for line in FANO_LINES:
        a, b, c = line
        # Cyclic permutations get +1
        epsilon[(a, b, c)] = 1
        epsilon[(b, c, a)] = 1
        epsilon[(c, a, b)] = 1
        # Anti-cyclic permutations get -1
        epsilon[(a, c, b)] = -1
        epsilon[(c, b, a)] = -1
        epsilon[(b, a, c)] = -1

    return epsilon


EPSILON = compute_epsilon()


def epsilon(i: int, j: int, k: int) -> int:
    """
    Return ε(i,j,k) for the G2 cross product.

    This is the structure constant: (e_i × e_j)_k = ε(i,j,k)
    """
    return EPSILON.get((i, j, k), 0)


# =============================================================================
# G2 CROSS PRODUCT IN R^7
# =============================================================================

def cross_product(u: Vector7, v: Vector7) -> Vector7:
    """
    Compute the G2-invariant cross product u × v in R^7.

    (u × v)_k = Σ_{i,j} ε(i,j,k) * u_i * v_j

    This cross product satisfies:
    - Bilinearity
    - Antisymmetry: u × v = -v × u
    - Lagrange identity: ||u × v||² = ||u||²||v||² - <u,v>²
    """
    result = [0.0] * 7

    for k in range(7):
        for i in range(7):
            for j in range(7):
                result[k] += epsilon(i, j, k) * u[i] * v[j]

    return tuple(result)


def inner_product_7(u: Vector7, v: Vector7) -> float:
    """Compute inner product in R^7."""
    return sum(u[i] * v[i] for i in range(7))


def norm_sq_7(v: Vector7) -> float:
    """Compute squared norm in R^7."""
    return inner_product_7(v, v)


def verify_lagrange_identity(u: Vector7, v: Vector7, tol: float = 1e-10) -> bool:
    """
    Verify the Lagrange identity: ||u × v||² = ||u||²||v||² - <u,v>²
    """
    cross = cross_product(u, v)
    lhs = norm_sq_7(cross)
    rhs = norm_sq_7(u) * norm_sq_7(v) - inner_product_7(u, v) ** 2
    return abs(lhs - rhs) < tol


# =============================================================================
# ASSOCIATIVE 3-FORM φ₀
# =============================================================================

def phi0(i: int, j: int, k: int) -> int:
    """
    The associative 3-form φ₀ defining the G2 structure.

    φ₀(e_i, e_j, e_k) = ε(i,j,k)
    """
    return epsilon(i, j, k)


def phi0_nonzero_components() -> List[Tuple[int, int, int, int]]:
    """
    Return all nonzero components of φ₀ as (i, j, k, value) tuples.

    There are 7 lines × 6 permutations / 2 (antisymmetry) = 21 nonzero
    """
    components = []
    for i in range(7):
        for j in range(i + 1, 7):
            for k in range(j + 1, 7):
                val = epsilon(i, j, k)
                if val != 0:
                    components.append((i, j, k, val))
    return components


# =============================================================================
# OCTONION MULTIPLICATION
# =============================================================================

def octonion_multiply_imaginaries(i: int, j: int) -> Tuple[int, int]:
    """
    Multiply two imaginary octonion units e_i * e_j.

    Returns (sign, index) where e_i * e_j = sign * e_index
    If i == j, returns (sign, -1) meaning e_i * e_i = -1

    Uses 0-indexing: e_0 through e_6 are the 7 imaginary units.
    """
    if i == j:
        return (-1, -1)  # e_i * e_i = -1

    k = third_point(i, j)
    sign = epsilon(i, j, k)
    return (sign, k)


# =============================================================================
# PSL(2,7) - AUTOMORPHISM GROUP
# =============================================================================

PSL27_ORDER = 168  # |PSL(2,7)| = |Aut(Fano)|

# The order can be computed from GIFT constants:
# 168 = 8 × 21 = rank_E8 × b2
# 168 = 3 × 56 = N_gen × fund_E7
# 168 = (b3 + dim_G2) + b3 = 91 + 77


def verify_fano_properties() -> Dict[str, bool]:
    """Verify key properties of the Fano plane structure."""
    results = {}

    # 7 points, 7 lines
    results['7_lines'] = len(FANO_LINES) == 7

    # 3 points per line
    results['3_points_per_line'] = all(len(line) == 3 for line in FANO_LINES)

    # 3 lines through each point
    results['3_lines_per_point'] = all(
        len(lines_through_point(p)) == 3 for p in range(7)
    )

    # Each pair of points determines a unique line
    results['unique_line'] = all(
        third_point(i, j) != -1
        for i in range(7) for j in range(7) if i != j
    )

    # Epsilon antisymmetry
    results['epsilon_antisymm'] = all(
        epsilon(i, j, k) == -epsilon(j, i, k)
        for i in range(7) for j in range(7) for k in range(7)
    )

    return results


# =============================================================================
# SUMMARY
# =============================================================================

def fano_summary() -> dict:
    """Return summary information about the Fano plane."""
    return {
        'points': 7,
        'lines': 7,
        'points_per_line': 3,
        'lines_per_point': 3,
        'automorphism_group': 'PSL(2,7)',
        'automorphism_order': PSL27_ORDER,
        'nonzero_epsilon': sum(1 for v in EPSILON.values() if v != 0),
        'cross_product_dimension': 7,
        'g2_dimension': 14,
    }
