"""
GIFT Monster Group Module
v2.0.0: Monster group dimension and j-invariant connections

Monster group M has smallest faithful representation of dimension 196883.
DISCOVERY: 196883 = 47 x 59 x 71, all GIFT-expressible factors.
"""

from typing import Dict, Tuple

# =============================================================================
# MONSTER DIMENSION FACTORIZATION
# =============================================================================

MONSTER_DIM = 196883

# 196883 = 47 x 59 x 71
MONSTER_FACTORS: Tuple[int, int, int] = (47, 59, 71)

# Factor expressions in GIFT
MONSTER_FACTOR_EXPRESSIONS: Dict[int, str] = {
    47: "lucas_8",           # L_8 = 47
    59: "b3 - lucas_6",      # 77 - 18 = 59
    71: "b3 - 6",            # 77 - 6 = 71
}


def verify_monster_factorization() -> bool:
    """Verify 196883 = 47 x 59 x 71"""
    return 47 * 59 * 71 == MONSTER_DIM


def monster_factor_arithmetic_progression() -> Tuple[int, int]:
    """The factors 47, 59, 71 form arithmetic progression with d=12"""
    return (59 - 47, 71 - 59)  # Both should be 12


# =============================================================================
# j-INVARIANT
# =============================================================================

J_CONSTANT = 744  # Constant term of j-function

# 744 = 3 x 248 = N_gen x dim_E8
J_CONSTANT_FACTORED: Tuple[int, int] = (3, 248)


def verify_j_constant() -> bool:
    """Verify 744 = 3 x 248"""
    return 3 * 248 == J_CONSTANT


# j(tau) = q^-1 + 744 + 196884*q + ...
J_COEFF_1 = 196884  # First coefficient = MONSTER_DIM + 1


def verify_moonshine() -> bool:
    """Verify Monstrous Moonshine: first j-coefficient = Monster dim + 1"""
    return J_COEFF_1 == MONSTER_DIM + 1


# =============================================================================
# E8 CONNECTIONS
# =============================================================================

def j_E8_relations() -> Dict[str, int]:
    """j-invariant connections to E8"""
    return {
        "j_constant": J_CONSTANT,
        "j_div_3": J_CONSTANT // 3,       # = 248 = dim_E8
        "j_div_248": J_CONSTANT // 248,   # = 3 = N_gen
        "j_minus_E8": J_CONSTANT - 248,   # = 496 = dim_E8xE8
        "j_plus_E8": J_CONSTANT + 248,    # = 992
    }


# Exports
__all__ = [
    'MONSTER_DIM', 'MONSTER_FACTORS', 'MONSTER_FACTOR_EXPRESSIONS',
    'verify_monster_factorization', 'monster_factor_arithmetic_progression',
    'J_CONSTANT', 'J_CONSTANT_FACTORED', 'J_COEFF_1',
    'verify_j_constant', 'verify_moonshine', 'j_E8_relations',
]
