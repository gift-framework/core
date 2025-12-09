"""
Interval arithmetic for verified numerical bounds.

This module provides exact rational interval arithmetic for verifying
PINN-computed bounds against Joyce's existence threshold.
"""

from fractions import Fraction
from dataclasses import dataclass
from typing import Union


@dataclass
class Interval:
    """Closed interval [lo, hi] with rational bounds."""
    lo: Fraction
    hi: Fraction

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError(f"Invalid interval: [{self.lo}, {self.hi}]")

    @classmethod
    def point(cls, x: Union[int, Fraction]) -> 'Interval':
        """Create interval containing single point."""
        return cls(Fraction(x), Fraction(x))

    @classmethod
    def from_float(cls, lo: float, hi: float, precision: int = 100000) -> 'Interval':
        """Create interval from float bounds with given precision."""
        return cls(
            Fraction(int(lo * precision), precision),
            Fraction(int(hi * precision + 1), precision)
        )

    def contains(self, x: Union[int, float, Fraction]) -> bool:
        """Check if x is in interval."""
        return self.lo <= Fraction(x) <= self.hi

    def width(self) -> Fraction:
        """Width of interval."""
        return self.hi - self.lo

    def midpoint(self) -> Fraction:
        """Midpoint of interval."""
        return (self.lo + self.hi) / 2

    def __add__(self, other: 'Interval') -> 'Interval':
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __mul__(self, other: 'Interval') -> 'Interval':
        # For positive intervals only (sufficient for GIFT)
        if self.lo >= 0 and other.lo >= 0:
            return Interval(self.lo * other.lo, self.hi * other.hi)
        raise NotImplementedError("General interval multiplication")

    def __truediv__(self, other: 'Interval') -> 'Interval':
        # For positive intervals only
        if other.lo > 0:
            return Interval(self.lo / other.hi, self.hi / other.lo)
        raise ValueError("Division by interval containing zero")

    def __repr__(self) -> str:
        return f"[{float(self.lo):.6f}, {float(self.hi):.6f}]"


# Type alias for bound checking
IntervalBound = Interval


# =============================================================================
# PINN Certified Bounds (from training)
# =============================================================================

# Torsion bound: ||T(φ₀)|| ∈ [0.00139, 0.00141]
TORSION_BOUND = Interval(
    Fraction(139, 100000),  # 0.00139
    Fraction(141, 100000)   # 0.00141
)

# Joyce threshold: ε₀ = 0.0288
JOYCE_THRESHOLD = Interval.point(Fraction(288, 10000))

# Lipschitz bound for Joyce operator
LIPSCHITZ_BOUND = Interval(
    Fraction(8, 10000),   # 0.0008
    Fraction(10, 10000)   # 0.0010
)

# det(g) from PINN (should match 65/32 = 2.03125)
DET_G_BOUND = Interval(
    Fraction(203124, 100000),  # 2.03124
    Fraction(203126, 100000)   # 2.03126
)

# Exact target for det(g)
DET_G_TARGET = Fraction(65, 32)  # 2.03125

# Contraction constant K = 0.9
CONTRACTION_K = Interval.point(Fraction(9, 10))


# =============================================================================
# Derived Bounds
# =============================================================================

def safety_margin() -> Fraction:
    """Compute safety margin: threshold / torsion_hi."""
    return JOYCE_THRESHOLD.lo / TORSION_BOUND.hi


def det_g_error() -> Fraction:
    """Relative error in det(g) computation."""
    return DET_G_BOUND.width() / DET_G_TARGET


def verify_torsion_below_threshold() -> bool:
    """Verify that PINN torsion is below Joyce threshold."""
    return TORSION_BOUND.hi < JOYCE_THRESHOLD.lo


def verify_contraction_valid() -> bool:
    """Verify contraction constant K < 1."""
    return CONTRACTION_K.hi < 1


def verify_det_g_accurate() -> bool:
    """Verify det(g) interval contains target."""
    return DET_G_BOUND.contains(DET_G_TARGET)
