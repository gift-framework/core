"""
GIFT Analysis Module - Sobolev spaces and Joyce certificate.

This module provides interval arithmetic and Joyce theorem verification
for the GIFT framework v3.0.
"""

from .intervals import (
    Interval,
    IntervalBound,
    TORSION_BOUND,
    JOYCE_THRESHOLD,
    LIPSCHITZ_BOUND,
    DET_G_BOUND,
    DET_G_TARGET,
    CONTRACTION_K,
)

from .joyce_certificate import (
    JoyceCertificate,
    verify_pinn_bounds,
)

__all__ = [
    # Interval arithmetic
    'Interval',
    'IntervalBound',
    'TORSION_BOUND',
    'JOYCE_THRESHOLD',
    'LIPSCHITZ_BOUND',
    'DET_G_BOUND',
    'DET_G_TARGET',
    'CONTRACTION_K',
    # Joyce certificate
    'JoyceCertificate',
    'verify_pinn_bounds',
]
