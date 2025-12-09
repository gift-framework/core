"""
GIFT McKay Correspondence Module
v2.0.0: E8 <-> Icosahedron <-> Golden Ratio

McKay correspondence: ADE Dynkin diagrams <-> Finite subgroups of SU(2)
E8 <-> Binary Icosahedral group (2I, order 120)
"""

from typing import Dict, Tuple

# =============================================================================
# MCKAY CORRESPONDENCE CONSTANTS
# =============================================================================

# E8 Coxeter number = 30 = icosahedron edges
COXETER_E8 = 30

# Icosahedron geometry
ICOSAHEDRON = {
    "vertices": 12,   # = dim_G2 - p2 = 14 - 2
    "edges": 30,      # = Coxeter(E8)
    "faces": 20,      # = m_s_m_d
}

# Binary polyhedral groups
BINARY_GROUPS = {
    "tetrahedral": 24,    # E6
    "octahedral": 48,     # E7
    "icosahedral": 120,   # E8
}

# E8 kissing number
E8_KISSING_NUMBER = 240  # = 2 * 120 = rank_E8 * Coxeter


def verify_mckay_coxeter() -> bool:
    """Verify Coxeter(E8) = icosahedron edges"""
    return COXETER_E8 == ICOSAHEDRON["edges"]


def verify_euler_icosahedron() -> bool:
    """Verify Euler: V - E + F = 2"""
    V, E, F = ICOSAHEDRON["vertices"], ICOSAHEDRON["edges"], ICOSAHEDRON["faces"]
    return V - E + F == 2


def verify_E8_kissing() -> bool:
    """Verify E8 kissing = 2 * binary icosahedral = rank * Coxeter"""
    return E8_KISSING_NUMBER == 2 * BINARY_GROUPS["icosahedral"]


# =============================================================================
# GOLDEN RATIO EMERGENCE
# =============================================================================

# Icosahedral angle = 72 degrees = 360/5
ICOSAHEDRAL_ANGLE = 72

# Pentagon angle = 108 degrees
PENTAGON_ANGLE = 108

# Golden ratio approximation from GIFT
PHI_APPROX = 21 / 13  # b2 / alpha_sq_B_sum


def golden_emergence_chain() -> Dict[str, str]:
    """The chain connecting E8 to phi"""
    return {
        "step1": "E8 has Coxeter number h = 30",
        "step2": "30 = 6 x 5 involves Weyl_factor = 5",
        "step3": "E8 <-> Binary Icosahedral (|2I| = 120)",
        "step4": "Icosahedron has 5-fold symmetry",
        "step5": "Pentagon diagonal/side = phi",
        "step6": "phi emerges from GIFT via 21/13 ratio",
    }


def phi_deviation(num: int, den: int) -> float:
    """Calculate percentage deviation from golden ratio"""
    phi = (1 + 5**0.5) / 2
    ratio = num / den
    return abs(ratio - phi) / phi * 100


# GIFT ratios approaching phi
PHI_RATIOS: Dict[str, Tuple[int, int, float]] = {
    "b2/alpha_sum": (21, 13, phi_deviation(21, 13)),
    "hidden/b2": (34, 21, phi_deviation(34, 21)),
    "H_star/kappa": (99, 61, phi_deviation(99, 61)),
    "b3/lucas_8": (77, 47, phi_deviation(77, 47)),
}


# =============================================================================
# ADE CLASSIFICATION
# =============================================================================

ADE_BINARY_ORDERS: Dict[str, int] = {
    "A_n": "n+1",      # Cyclic
    "D_n": "4(n-2)",   # Binary dihedral
    "E_6": 24,         # Binary tetrahedral
    "E_7": 48,         # Binary octahedral
    "E_8": 120,        # Binary icosahedral
}


# Exports
__all__ = [
    'COXETER_E8', 'ICOSAHEDRON', 'BINARY_GROUPS', 'E8_KISSING_NUMBER',
    'verify_mckay_coxeter', 'verify_euler_icosahedron', 'verify_E8_kissing',
    'ICOSAHEDRAL_ANGLE', 'PENTAGON_ANGLE', 'PHI_APPROX',
    'golden_emergence_chain', 'phi_deviation', 'PHI_RATIOS',
    'ADE_BINARY_ORDERS',
]
