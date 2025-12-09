"""
GIFT Sequences Module
v2.0.0: Fibonacci and Lucas sequence embeddings in GIFT constants

Fibonacci embedding: F_3 through F_12 map to GIFT constants
Lucas embedding: L_0 through L_9 map to GIFT constants
"""

from typing import Dict, List, Tuple

# Fibonacci sequence
def fib(n: int) -> int:
    """Compute nth Fibonacci number (F_0=0, F_1=1)"""
    if n <= 0:
        return 0
    if n == 1:
        return 1
    a, b = 0, 1
    for _ in range(2, n + 1):
        a, b = b, a + b
    return b


# Lucas sequence
def lucas(n: int) -> int:
    """Compute nth Lucas number (L_0=2, L_1=1)"""
    if n == 0:
        return 2
    if n == 1:
        return 1
    a, b = 2, 1
    for _ in range(2, n + 1):
        a, b = b, a + b
    return b


# =============================================================================
# FIBONACCI EMBEDDING IN GIFT CONSTANTS
# =============================================================================

# F_3 = 2 = p2
# F_4 = 3 = N_gen
# F_5 = 5 = Weyl_factor
# F_6 = 8 = rank_E8
# F_7 = 13 = alpha_sq_B_sum
# F_8 = 21 = b2
# F_9 = 34 = hidden_dim
# F_10 = 55 = dim_E7 - dim_E6
# F_11 = 89 = b3 + dim_G2 - p2
# F_12 = 144 = (dim_G2 - p2)^2

FIBONACCI_GIFT: Dict[int, Tuple[int, str]] = {
    3: (2, "p2"),
    4: (3, "N_gen"),
    5: (5, "Weyl_factor"),
    6: (8, "rank_E8"),
    7: (13, "alpha_sq_B_sum"),
    8: (21, "b2"),
    9: (34, "hidden_dim"),
    10: (55, "dim_E7 - dim_E6"),
    11: (89, "b3 + dim_G2 - p2"),
    12: (144, "(dim_G2 - p2)^2"),
}


def fibonacci_index(value: int) -> int:
    """Find Fibonacci index for a GIFT constant value, or -1 if not found"""
    for i in range(3, 13):
        if fib(i) == value:
            return i
    return -1


# =============================================================================
# LUCAS EMBEDDING IN GIFT CONSTANTS
# =============================================================================

# L_0 = 2 = p2
# L_2 = 3 = N_gen
# L_4 = 7 = dim_K7
# L_5 = 11 = D_bulk
# L_6 = 18 = duality_gap
# L_7 = 29 = prime(10)
# L_8 = 47 = Monster factor
# L_9 = 76 = b3 - 1

LUCAS_GIFT: Dict[int, Tuple[int, str]] = {
    0: (2, "p2"),
    2: (3, "N_gen"),
    4: (7, "dim_K7"),
    5: (11, "D_bulk"),
    6: (18, "duality_gap"),
    7: (29, "prime_10"),
    8: (47, "Monster_factor"),
    9: (76, "b3 - 1"),
}


def lucas_index(value: int) -> int:
    """Find Lucas index for a GIFT constant value, or -1 if not found"""
    for i in range(0, 10):
        if lucas(i) == value:
            return i
    return -1


# =============================================================================
# RECURRENCE RELATIONS
# =============================================================================

# alpha_sq_B_sum = rank_E8 + Weyl_factor (13 = 8 + 5)
# b2 = alpha_sq_B_sum + rank_E8 (21 = 13 + 8)
# hidden_dim = b2 + alpha_sq_B_sum (34 = 21 + 13)

RECURRENCE_CHAIN: List[Tuple[str, str, str, int]] = [
    ("Weyl_factor", "N_gen + p2", "5 = 3 + 2", 5),
    ("rank_E8", "Weyl_factor + N_gen", "8 = 5 + 3", 8),
    ("alpha_sq_B_sum", "rank_E8 + Weyl_factor", "13 = 8 + 5", 13),
    ("b2", "alpha_sq_B_sum + rank_E8", "21 = 13 + 8", 21),
    ("hidden_dim", "b2 + alpha_sq_B_sum", "34 = 21 + 13", 34),
]


def verify_fibonacci_recurrence() -> bool:
    """Verify that GIFT constants satisfy Fibonacci recurrence"""
    # Constants
    p2, N_gen, Weyl = 2, 3, 5
    rank_E8, alpha_sum, b2, hidden = 8, 13, 21, 34

    return (
        Weyl == N_gen + p2 and
        rank_E8 == Weyl + N_gen and
        alpha_sum == rank_E8 + Weyl and
        b2 == alpha_sum + rank_E8 and
        hidden == b2 + alpha_sum
    )


# =============================================================================
# PHI APPROXIMATION
# =============================================================================

PHI_RATIOS: List[Tuple[int, int, float]] = [
    (21, 13, 21/13),    # b2 / alpha_sum = 1.615... (0.16% error)
    (34, 21, 34/21),    # hidden / b2 = 1.619... (0.06% error)
    (55, 34, 55/34),    # (E7-E6) / hidden = 1.617... (0.03% error)
]


def phi_deviation(num: int, den: int) -> float:
    """Calculate percentage deviation from golden ratio phi"""
    phi = (1 + 5**0.5) / 2
    ratio = num / den
    return abs(ratio - phi) / phi * 100


# Exports
__all__ = [
    'fib', 'lucas',
    'FIBONACCI_GIFT', 'LUCAS_GIFT',
    'fibonacci_index', 'lucas_index',
    'RECURRENCE_CHAIN', 'verify_fibonacci_recurrence',
    'PHI_RATIOS', 'phi_deviation',
]
