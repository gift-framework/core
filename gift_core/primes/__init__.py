"""
GIFT Prime Atlas Module
v2.0.0: Complete prime coverage to 200

All primes < 200 can be expressed using GIFT constants.
Three generators: b3=77, H*=99, dim_E8=248
"""

from typing import Dict, List, Optional, Tuple

# =============================================================================
# DIRECT PRIMES: GIFT CONSTANTS THAT ARE PRIME
# =============================================================================

DIRECT_PRIMES: Dict[int, str] = {
    2: "p2",
    3: "N_gen",
    5: "Weyl_factor",
    7: "dim_K7",
    11: "D_bulk",
    13: "alpha_sq_B_sum",
    17: "lambda_H_num",
    19: "prime_8",
    31: "prime_11",
    61: "kappa_T_inv",
}

# =============================================================================
# DERIVED PRIMES: PRIMES < 100 VIA GIFT EXPRESSIONS
# =============================================================================

DERIVED_PRIMES: Dict[int, str] = {
    23: "b2 + p2",
    29: "dim_K7 * 4 + 1",
    37: "b2 + p2 * rank_E8",
    41: "b3 - 36",
    43: "visible_dim",
    47: "b3 - 30",
    53: "b3 - 24",
    59: "b3 - 18",
    67: "b3 - 2 * Weyl_factor",
    71: "b3 - 6",
    73: "b3 - p2 * p2",
    79: "b3 + p2",
    83: "b3 + 6",
    89: "b3 + dim_G2 - p2",
    97: "H_star - p2",
}

# =============================================================================
# H* PRIMES: 100-150 VIA H* = 99
# =============================================================================

HSTAR_PRIMES: Dict[int, str] = {
    101: "H_star + p2",
    103: "H_star + 4",
    107: "H_star + rank_E8",
    109: "H_star + 10",
    113: "H_star + dim_G2",
    127: "H_star + 4 * dim_K7",
    131: "H_star + 32",
    137: "H_star + 38",
    139: "H_star + 40",
    149: "H_star + 50",
}

# =============================================================================
# E8 PRIMES: 150-200 VIA dim_E8 = 248
# =============================================================================

E8_PRIMES: Dict[int, str] = {
    151: "dim_E8 - 97",
    157: "dim_E8 - 91",
    163: "dim_E8 - rank_E8 - b3",
    167: "dim_E8 - 81",
    173: "dim_E8 - 75",
    179: "dim_E8 - 69",
    181: "dim_E8 - 67",
    191: "dim_E8 - 57",
    193: "dim_E8 - 55",
    197: "dim_E8 - 51",
    199: "dim_E8 - 49",
}

# =============================================================================
# HEEGNER NUMBERS
# =============================================================================

HEEGNER_NUMBERS: Dict[int, str] = {
    1: "dim_U1",
    2: "p2",
    3: "N_gen",
    7: "dim_K7",
    11: "D_bulk",
    19: "prime_8",
    43: "visible_dim",
    67: "b3 - 2 * Weyl_factor",
    163: "dim_E8 - rank_E8 - b3",
}

# =============================================================================
# SPECIAL PRIMES
# =============================================================================

SPECIAL_PRIMES: Dict[int, str] = {
    127: "2^dim_K7 - 1 (Mersenne)",
    197: "delta_CP",
    67: "Hubble_CMB",
    73: "Hubble_local",
}

# =============================================================================
# THREE GENERATORS
# =============================================================================

GENERATORS = {
    "b3": 77,       # Generates primes 30-90
    "H_star": 99,   # Generates primes 90-150
    "dim_E8": 248,  # Generates primes 150-250
}


def prime_expression(p: int) -> Optional[str]:
    """Return GIFT expression for prime p < 200"""
    if p in DIRECT_PRIMES:
        return DIRECT_PRIMES[p]
    if p in DERIVED_PRIMES:
        return DERIVED_PRIMES[p]
    if p in HSTAR_PRIMES:
        return HSTAR_PRIMES[p]
    if p in E8_PRIMES:
        return E8_PRIMES[p]
    return None


def prime_generator(p: int) -> Optional[str]:
    """Return which generator (b3, H*, or dim_E8) expresses prime p"""
    if p < 30:
        return "direct"
    if 30 <= p < 90:
        return "b3"
    if 90 <= p < 150:
        return "H_star"
    if 150 <= p < 250:
        return "dim_E8"
    return None


def is_gift_prime(p: int) -> bool:
    """Check if prime p is GIFT-expressible"""
    return prime_expression(p) is not None


def is_heegner(n: int) -> bool:
    """Check if n is a Heegner number"""
    return n in HEEGNER_NUMBERS


def verify_prime_coverage(max_p: int = 100) -> bool:
    """Verify all primes < max_p are GIFT-expressible"""
    def is_prime(n: int) -> bool:
        if n < 2:
            return False
        for i in range(2, int(n**0.5) + 1):
            if n % i == 0:
                return False
        return True

    for p in range(2, max_p):
        if is_prime(p) and not is_gift_prime(p):
            return False
    return True


# Backwards compatibility aliases (deprecated, will be removed in v4.0)
TIER1_PRIMES = DIRECT_PRIMES
TIER2_PRIMES = DERIVED_PRIMES
TIER3_PRIMES = HSTAR_PRIMES
TIER4_PRIMES = E8_PRIMES

# Exports
__all__ = [
    'DIRECT_PRIMES', 'DERIVED_PRIMES', 'HSTAR_PRIMES', 'E8_PRIMES',
    'HEEGNER_NUMBERS', 'SPECIAL_PRIMES', 'GENERATORS',
    'prime_expression', 'prime_generator', 'is_gift_prime',
    'is_heegner', 'verify_prime_coverage',
    # Backwards compatibility (deprecated)
    'TIER1_PRIMES', 'TIER2_PRIMES', 'TIER3_PRIMES', 'TIER4_PRIMES',
]
