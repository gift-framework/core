"""
GIFT G2 Module - G2 structures and constraints.

This module implements the G2 holonomy structure including:
- G2 3-form phi and 4-form *phi
- Holonomy computations
- Torsion classes
- GIFT constraints (det(g) = 65/32, kappa_T = 1/61)
"""

from .g2_form import G2Form, G2Form4, standard_g2_form
from .holonomy import G2Holonomy, compute_holonomy
from .torsion import G2Torsion, torsion_classes
from .constraints import G2Constraints, GIFT_CONSTRAINTS

__all__ = [
    'G2Form',
    'G2Form4',
    'standard_g2_form',
    'G2Holonomy',
    'compute_holonomy',
    'G2Torsion',
    'torsion_classes',
    'G2Constraints',
    'GIFT_CONSTRAINTS',
]
