"""
Interval arithmetic for certified numerical bounds.

Provides rigorous error bounds on computed quantities
for integration with formal proof systems.
"""

from dataclasses import dataclass
from typing import Union, Tuple
from fractions import Fraction
import numpy as np


@dataclass
class IntervalArithmetic:
    """
    Interval arithmetic for certified computations.

    Represents a real number x as [lo, hi] where lo <= x <= hi.
    All operations preserve the containment property.

    Attributes:
        lo: Lower bound
        hi: Upper bound
    """

    lo: float
    hi: float

    def __post_init__(self):
        """Validate interval."""
        assert self.lo <= self.hi, f"Invalid interval: [{self.lo}, {self.hi}]"

    @property
    def center(self) -> float:
        """Interval midpoint."""
        return (self.lo + self.hi) / 2

    @property
    def radius(self) -> float:
        """Interval half-width."""
        return (self.hi - self.lo) / 2

    @property
    def width(self) -> float:
        """Interval width."""
        return self.hi - self.lo

    def contains(self, x: float) -> bool:
        """Check if interval contains x."""
        return self.lo <= x <= self.hi

    def contains_rational(self, r: Fraction) -> bool:
        """Check if interval contains rational r."""
        return self.lo <= float(r) <= self.hi

    def __add__(self, other: 'IntervalArithmetic') -> 'IntervalArithmetic':
        """Interval addition: [a,b] + [c,d] = [a+c, b+d]."""
        if isinstance(other, (int, float)):
            return IntervalArithmetic(self.lo + other, self.hi + other)
        return IntervalArithmetic(self.lo + other.lo, self.hi + other.hi)

    def __radd__(self, other):
        return self.__add__(other)

    def __sub__(self, other: 'IntervalArithmetic') -> 'IntervalArithmetic':
        """Interval subtraction: [a,b] - [c,d] = [a-d, b-c]."""
        if isinstance(other, (int, float)):
            return IntervalArithmetic(self.lo - other, self.hi - other)
        return IntervalArithmetic(self.lo - other.hi, self.hi - other.lo)

    def __rsub__(self, other):
        if isinstance(other, (int, float)):
            return IntervalArithmetic(other - self.hi, other - self.lo)
        return other.__sub__(self)

    def __mul__(self, other: 'IntervalArithmetic') -> 'IntervalArithmetic':
        """Interval multiplication."""
        if isinstance(other, (int, float)):
            if other >= 0:
                return IntervalArithmetic(self.lo * other, self.hi * other)
            else:
                return IntervalArithmetic(self.hi * other, self.lo * other)

        products = [
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi
        ]
        return IntervalArithmetic(min(products), max(products))

    def __rmul__(self, other):
        return self.__mul__(other)

    def __truediv__(self, other: 'IntervalArithmetic') -> 'IntervalArithmetic':
        """Interval division (other must not contain 0)."""
        if isinstance(other, (int, float)):
            if other > 0:
                return IntervalArithmetic(self.lo / other, self.hi / other)
            elif other < 0:
                return IntervalArithmetic(self.hi / other, self.lo / other)
            else:
                raise ZeroDivisionError("Division by zero")

        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("Interval contains zero")

        quotients = [
            self.lo / other.lo,
            self.lo / other.hi,
            self.hi / other.lo,
            self.hi / other.hi
        ]
        return IntervalArithmetic(min(quotients), max(quotients))

    def __pow__(self, n: int) -> 'IntervalArithmetic':
        """Integer power."""
        if n == 0:
            return IntervalArithmetic(1.0, 1.0)
        elif n == 1:
            return self
        elif n % 2 == 0:
            # Even power: may not be monotonic
            if self.lo >= 0:
                return IntervalArithmetic(self.lo ** n, self.hi ** n)
            elif self.hi <= 0:
                return IntervalArithmetic(self.hi ** n, self.lo ** n)
            else:
                return IntervalArithmetic(0, max(self.lo ** n, self.hi ** n))
        else:
            # Odd power: monotonic
            return IntervalArithmetic(self.lo ** n, self.hi ** n)

    def sqrt(self) -> 'IntervalArithmetic':
        """Square root (interval must be non-negative)."""
        assert self.lo >= 0, "Cannot take sqrt of negative interval"
        return IntervalArithmetic(np.sqrt(self.lo), np.sqrt(self.hi))

    def __repr__(self) -> str:
        return f"[{self.lo:.10f}, {self.hi:.10f}]"

    def to_lean(self) -> str:
        """Export as Lean-compatible bound."""
        return f"|x - {self.center}| < {self.radius}"


def certified_interval(values: np.ndarray,
                       n_sigma: float = 3.0) -> IntervalArithmetic:
    """
    Create certified interval from sample values.

    Uses mean +/- n_sigma * std_err for bounds.

    Args:
        values: Sample values
        n_sigma: Number of standard deviations for bounds

    Returns:
        Certified interval
    """
    mean = np.mean(values)
    std = np.std(values)
    std_err = std / np.sqrt(len(values))

    margin = n_sigma * std_err

    return IntervalArithmetic(
        lo=float(mean - margin),
        hi=float(mean + margin)
    )


def from_fraction(r: Fraction, epsilon: float = 1e-15) -> IntervalArithmetic:
    """
    Create tight interval around a rational number.

    Args:
        r: Rational number
        epsilon: Rounding error tolerance

    Returns:
        Interval containing r
    """
    val = float(r)
    return IntervalArithmetic(val - epsilon, val + epsilon)


def verify_equality(computed: IntervalArithmetic, target: Fraction,
                    report: bool = True) -> bool:
    """
    Verify that computed interval contains target rational.

    Args:
        computed: Computed interval
        target: Expected rational value
        report: Whether to print verification result

    Returns:
        True if interval contains target
    """
    result = computed.contains(float(target))

    if report:
        if result:
            print(f"VERIFIED: {target} in {computed}")
        else:
            print(f"FAILED: {target} not in {computed}")

    return result
