"""
GIFT Physics Module - Standard Model from G2 geometry.

This module computes physical observables from the K7 geometry:
- Yukawa couplings from harmonic form triple products
- Fermion mass spectrum
- Gauge coupling constants
"""

from .yukawa_tensor import YukawaTensor, compute_yukawa
from .mass_spectrum import MassSpectrum, compute_masses
from .coupling_constants import GaugeCouplings, GIFT_COUPLINGS

__all__ = [
    'YukawaTensor',
    'compute_yukawa',
    'MassSpectrum',
    'compute_masses',
    'GaugeCouplings',
    'GIFT_COUPLINGS',
]
