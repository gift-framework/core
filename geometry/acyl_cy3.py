"""
Asymptotically Cylindrical Calabi-Yau 3-folds.

ACyl CY3s are non-compact Calabi-Yau manifolds that are asymptotic
to a cylinder K3 x S^1 x R_+ at infinity. They are the building
blocks for TCS G2 manifolds.

Reference: Corti-Haskins-Nordström-Pacini (2015)
"""

from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Callable
import numpy as np

from .k3_surface import KummerK3


@dataclass
class ACylCY3:
    """
    Asymptotically Cylindrical Calabi-Yau 3-fold.

    An ACyl CY3 X has the form:
    - Compact core: V (a Fano 3-fold or similar)
    - Asymptotic end: K3 x S^1 x [T, infty)

    The Calabi-Yau metric is Ricci-flat and approaches
    the product metric on the cylinder.

    Attributes:
        k3: The asymptotic K3 surface
        b2: Second Betti number of the ACyl
        b3: Third Betti number of the ACyl
        hyper_structure: Choice of hyperkahler rotation on K3
    """

    k3: KummerK3 = field(default_factory=KummerK3)

    # Betti numbers (vary with construction)
    b2: int = 23  # b2(X) = b2(K3) + 1 = 23 typically
    b3: int = 40  # Varies: for TCS K7, we need b3(X+) + b3(X-) to give b3(K7) = 77

    # Hyperkahler rotation angle theta
    hyper_angle: float = 0.0

    # Decay rate for asymptotic metric
    decay_rate: float = 1.0

    def __post_init__(self):
        """Initialize the ACyl structure."""
        self._validate_topology()

    def _validate_topology(self):
        """Verify topological constraints."""
        # ACyl CY3 has b1 = 0 typically
        assert self.b2 >= self.k3.betti[2], "b2(ACyl) >= b2(K3)"

    @property
    def euler(self) -> int:
        """
        Euler characteristic of ACyl CY3.

        For ACyl: chi = 2(b2 - b3 + 1) when b1 = b5 = 0
        """
        return 2 * (self.b2 - self.b3 + 1)

    def asymptotic_metric(self, r: np.ndarray, x_k3: np.ndarray) -> np.ndarray:
        """
        Metric in the asymptotic cylindrical region.

        g_cyl = g_K3 + dr^2 + dtheta^2

        where theta is the S^1 coordinate.

        Args:
            r: Radial coordinates, shape (N,)
            x_k3: K3 coordinates, shape (N, 4)

        Returns:
            Metric tensors, shape (N, 6, 6)
        """
        N = r.shape[0]
        g = np.zeros((N, 6, 6))

        # K3 metric in first 4x4 block
        g_k3 = self.k3.metric_flat(x_k3)
        g[:, :4, :4] = g_k3

        # S^1 and R directions
        g[:, 4, 4] = 1.0  # dtheta^2
        g[:, 5, 5] = 1.0  # dr^2

        return g

    def holomorphic_3form(self, x: np.ndarray) -> np.ndarray:
        """
        Holomorphic (3,0)-form Omega on the CY3.

        In the asymptotic region:
        Omega = (dr + i*dtheta) ^ Omega_K3

        where Omega_K3 is the holomorphic 2-form on K3.

        Args:
            x: Full coordinates (K3, theta, r), shape (N, 6)

        Returns:
            3-form components, shape (N, 20) for C(6,3) = 20 components
        """
        N = x.shape[0]
        # Simplified: return standard form
        omega = np.zeros((N, 20), dtype=np.complex128)

        # Leading component: dz1 ^ dz2 ^ dz3
        omega[:, 0] = 1.0

        return omega

    def kahler_form(self, x: np.ndarray) -> np.ndarray:
        """
        Kahler form omega on the CY3.

        In the asymptotic region:
        omega = omega_K3 + dr ^ dtheta

        Args:
            x: Full coordinates, shape (N, 6)

        Returns:
            2-form components, shape (N, 15)
        """
        N = x.shape[0]
        omega = np.zeros((N, 15))

        # K3 Kahler form contributions
        omega[:, 0] = 1.0  # dx0 ^ dx1
        omega[:, 5] = 1.0  # dx2 ^ dx3

        # Cylinder contribution: dr ^ dtheta
        omega[:, 14] = 1.0  # dx4 ^ dx5

        return omega

    def matching_data(self) -> Tuple[np.ndarray, np.ndarray]:
        """
        Get the matching data for TCS gluing.

        The matching data consists of:
        1. The hyperkahler structure on the asymptotic K3
        2. The S^1 twist angle

        Returns:
            (hyperkahler_triple, twist_angle)
        """
        # Hyperkahler triple (omega_I, omega_J, omega_K)
        # Under rotation by angle theta:
        # omega_2 = cos(theta)*omega_I + sin(theta)*omega_J
        triple = np.array([
            [1, 0, 0],
            [0, np.cos(self.hyper_angle), -np.sin(self.hyper_angle)],
            [0, np.sin(self.hyper_angle), np.cos(self.hyper_angle)]
        ])

        return triple, self.hyper_angle

    def sample_interior(self, n_points: int, r_max: float = 5.0) -> np.ndarray:
        """
        Sample points in the interior of the ACyl.

        Args:
            n_points: Number of points
            r_max: Maximum radial coordinate

        Returns:
            Points in interior, shape (n_points, 6)
        """
        # K3 coordinates
        x_k3 = self.k3.sample_points(n_points)

        # Cylinder coordinates
        theta = np.random.rand(n_points) * 2 * np.pi
        r = np.random.rand(n_points) * r_max

        return np.column_stack([x_k3, theta, r])

    def sample_asymptotic(self, n_points: int, r_min: float = 5.0,
                          r_max: float = 10.0) -> np.ndarray:
        """
        Sample points in the asymptotic cylindrical region.

        Args:
            n_points: Number of points
            r_min: Minimum radial coordinate
            r_max: Maximum radial coordinate

        Returns:
            Points in asymptotic region, shape (n_points, 6)
        """
        x_k3 = self.k3.sample_points(n_points)
        theta = np.random.rand(n_points) * 2 * np.pi
        r = r_min + np.random.rand(n_points) * (r_max - r_min)

        return np.column_stack([x_k3, theta, r])


def create_kovalev_acyl(which: str = 'plus') -> ACylCY3:
    """
    Create an ACyl CY3 following Kovalev's construction.

    Kovalev's original construction uses:
    - X_+ and X_- as crepant resolutions of nodal cubics
    - Both have b2 = 23, b3 = 40

    For the specific K7 with b3 = 77, we need:
    b3(K7) = b3(X+) + b3(X-) - 6 + boundary_contribution = 77

    Args:
        which: 'plus' or 'minus' for the two halves

    Returns:
        ACylCY3 with appropriate Betti numbers
    """
    k3 = KummerK3()

    if which == 'plus':
        # X+ with matching data for gluing
        return ACylCY3(k3=k3, b2=23, b3=40, hyper_angle=0.0)
    else:
        # X- with complementary matching data
        return ACylCY3(k3=k3, b2=23, b3=40, hyper_angle=np.pi / 2)
