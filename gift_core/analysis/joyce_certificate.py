"""
Joyce theorem certificate verification.

This module verifies all conditions of Joyce's perturbation theorem
for the K7 manifold using PINN-computed bounds.
"""

from dataclasses import dataclass
from fractions import Fraction
from .intervals import (
    TORSION_BOUND, JOYCE_THRESHOLD, LIPSCHITZ_BOUND,
    DET_G_BOUND, DET_G_TARGET, CONTRACTION_K,
    verify_torsion_below_threshold, verify_contraction_valid,
    verify_det_g_accurate, safety_margin,
)


@dataclass
class JoyceCertificate:
    """Complete certificate for Joyce existence theorem on K7."""

    torsion_below_threshold: bool
    safety_margin: Fraction
    contraction_valid: bool
    det_g_correct: bool

    @classmethod
    def verify(cls) -> 'JoyceCertificate':
        """Verify all Joyce theorem conditions."""

        # 1. Torsion below threshold
        torsion_ok = verify_torsion_below_threshold()

        # 2. Safety margin
        margin = safety_margin()

        # 3. Contraction constant
        k_ok = verify_contraction_valid()

        # 4. Determinant
        det_ok = verify_det_g_accurate()

        return cls(
            torsion_below_threshold=torsion_ok,
            safety_margin=margin,
            contraction_valid=k_ok,
            det_g_correct=det_ok
        )

    def is_valid(self) -> bool:
        """Check if certificate is valid (all conditions met)."""
        return (
            self.torsion_below_threshold and
            self.safety_margin > 20 and
            self.contraction_valid and
            self.det_g_correct
        )

    def __str__(self) -> str:
        status = "VALID" if self.is_valid() else "INVALID"
        return f"""JoyceCertificate:
  Torsion < threshold: {self.torsion_below_threshold}
  Safety margin: {float(self.safety_margin):.1f}x
  Contraction K < 1: {self.contraction_valid}
  det(g) = 65/32: {self.det_g_correct}
  Status: {status}"""


def verify_pinn_bounds() -> bool:
    """Quick verification of PINN bounds for Joyce theorem."""
    cert = JoyceCertificate.verify()
    return cert.is_valid()


# =============================================================================
# Detailed Verification Functions
# =============================================================================

def get_torsion_info() -> dict:
    """Get detailed torsion bound information."""
    return {
        'bound_lo': float(TORSION_BOUND.lo),
        'bound_hi': float(TORSION_BOUND.hi),
        'threshold': float(JOYCE_THRESHOLD.lo),
        'margin': float(safety_margin()),
        'below_threshold': verify_torsion_below_threshold(),
    }


def get_det_g_info() -> dict:
    """Get detailed det(g) information."""
    return {
        'pinn_lo': float(DET_G_BOUND.lo),
        'pinn_hi': float(DET_G_BOUND.hi),
        'exact': float(DET_G_TARGET),
        'width': float(DET_G_BOUND.width()),
        'accurate': verify_det_g_accurate(),
    }


def get_full_certificate() -> dict:
    """Get complete certificate information as dictionary."""
    cert = JoyceCertificate.verify()
    return {
        'valid': cert.is_valid(),
        'torsion': get_torsion_info(),
        'det_g': get_det_g_info(),
        'contraction_k': float(CONTRACTION_K.hi),
        'contraction_valid': cert.contraction_valid,
    }
