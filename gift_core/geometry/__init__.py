"""
GIFT Geometry Module - K7 manifold construction.

This module implements the TCS (Twisted Connected Sum) construction
of compact G2 manifolds, following Kovalev and Corti-Haskins-Nordström-Pacini.
"""

from .k3_surface import KummerK3
from .acyl_cy3 import ACylCY3
from .tcs_construction import TCSManifold
from .k7_metric import K7Metric

__all__ = [
    'KummerK3',
    'ACylCY3',
    'TCSManifold',
    'K7Metric',
]
