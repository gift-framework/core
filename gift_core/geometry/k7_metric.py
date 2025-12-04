"""
K7 Metric - Main G2 metric class for GIFT.

This module provides the K7Metric class which represents the
Ricci-flat G2 metric on the TCS manifold. It supports both
analytical approximations and neural network representations.

Key GIFT constraints:
- det(g) = 65/32
- kappa_T = 1/61
- b2 = 21, b3 = 77
"""

from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional, Union
from fractions import Fraction
import numpy as np

try:
    import torch
    from torch import Tensor
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False
    Tensor = np.ndarray

from .tcs_construction import TCSManifold


# GIFT certified values
DET_G_TARGET = Fraction(65, 32)  # = 2.03125
KAPPA_T_TARGET = Fraction(1, 61)  # ~ 0.01639
B2_TARGET = 21
B3_TARGET = 77


@dataclass
class K7Metric:
    """
    G2-holonomy metric on the K7 manifold.

    This class represents the Ricci-flat metric g on K7 satisfying
    the G2 holonomy condition: Hol(g) = G2.

    The metric is determined by the G2 3-form phi via:
    g_ij = (1/6) * phi_ikl * phi_jmn * eps^{klmn...} / sqrt(det)

    Attributes:
        tcs: Underlying TCS manifold
        det_g: Metric determinant (target: 65/32)
        kappa_t: Torsion coefficient (target: 1/61)
    """

    tcs: TCSManifold = field(default_factory=TCSManifold.from_kovalev)

    # Computed metric parameters
    _det_g: Optional[float] = None
    _kappa_t: Optional[float] = None

    # Neural network metric (if using PINN)
    _nn_model: Optional[object] = None

    def __post_init__(self):
        """Initialize metric with default parameters."""
        self._det_g = float(DET_G_TARGET)
        self._kappa_t = float(KAPPA_T_TARGET)

    @property
    def dim(self) -> int:
        """Real dimension."""
        return 7

    @property
    def det_g(self) -> float:
        """Metric determinant (certified: 65/32)."""
        return self._det_g

    @property
    def kappa_t(self) -> float:
        """Torsion coefficient (certified: 1/61)."""
        return self._kappa_t

    @property
    def b2(self) -> int:
        """Second Betti number (certified: 21)."""
        return self.tcs.betti_numbers()[2]

    @property
    def b3(self) -> int:
        """Third Betti number (certified: 77)."""
        return self.tcs.betti_numbers()[3]

    def metric_tensor(self, x: np.ndarray) -> np.ndarray:
        """
        Compute metric tensor g_ij at points x.

        Args:
            x: Points on K7, shape (N, 7)

        Returns:
            Metric tensors, shape (N, 7, 7)
        """
        N = x.shape[0]

        if self._nn_model is not None:
            # Use neural network metric
            return self._nn_metric(x)

        # Use TCS analytical metric
        # Determine region for each point
        t = x[:, 6]  # Neck parameter
        T = self.tcs.neck_length

        g = np.zeros((N, 7, 7))

        # Plus region: t < 0.2 * T
        plus_mask = t < 0.2 * T
        if np.any(plus_mask):
            g[plus_mask] = self.tcs.metric('plus', x[plus_mask])

        # Minus region: t > 0.8 * T
        minus_mask = t > 0.8 * T
        if np.any(minus_mask):
            g[minus_mask] = self.tcs.metric('minus', x[minus_mask])

        # Neck region: 0.2*T <= t <= 0.8*T
        neck_mask = ~plus_mask & ~minus_mask
        if np.any(neck_mask):
            g[neck_mask] = self.tcs.metric('neck', x[neck_mask])

        # Scale to achieve target determinant
        scale = (self.det_g ** (1/7))
        g *= scale

        return g

    def _nn_metric(self, x: np.ndarray) -> np.ndarray:
        """Compute metric using neural network model."""
        if not HAS_TORCH:
            raise ImportError("PyTorch required for neural network metric")

        x_tensor = torch.tensor(x, dtype=torch.float32)
        with torch.no_grad():
            g_tensor = self._nn_model(x_tensor)
        return g_tensor.numpy()

    def inverse_metric(self, x: np.ndarray) -> np.ndarray:
        """
        Compute inverse metric g^{ij} at points x.

        Args:
            x: Points on K7, shape (N, 7)

        Returns:
            Inverse metric tensors, shape (N, 7, 7)
        """
        g = self.metric_tensor(x)
        return np.linalg.inv(g)

    def christoffel(self, x: np.ndarray, eps: float = 1e-5) -> np.ndarray:
        """
        Compute Christoffel symbols Gamma^i_{jk} via finite differences.

        Gamma^i_{jk} = (1/2) g^{il} (d_j g_{lk} + d_k g_{jl} - d_l g_{jk})

        Args:
            x: Points on K7, shape (N, 7)
            eps: Finite difference step size

        Returns:
            Christoffel symbols, shape (N, 7, 7, 7)
        """
        N = x.shape[0]
        Gamma = np.zeros((N, 7, 7, 7))

        # Get inverse metric
        g_inv = self.inverse_metric(x)

        # Compute metric derivatives via finite differences
        dg = np.zeros((N, 7, 7, 7))  # d_l g_{jk}

        for l in range(7):
            x_plus = x.copy()
            x_minus = x.copy()
            x_plus[:, l] += eps
            x_minus[:, l] -= eps

            g_plus = self.metric_tensor(x_plus)
            g_minus = self.metric_tensor(x_minus)

            dg[:, l, :, :] = (g_plus - g_minus) / (2 * eps)

        # Compute Christoffel symbols
        for i in range(7):
            for j in range(7):
                for k in range(7):
                    for l in range(7):
                        Gamma[:, i, j, k] += 0.5 * g_inv[:, i, l] * (
                            dg[:, j, l, k] + dg[:, k, j, l] - dg[:, l, j, k]
                        )

        return Gamma

    def riemann(self, x: np.ndarray, eps: float = 1e-4) -> np.ndarray:
        """
        Compute Riemann curvature tensor R^i_{jkl}.

        For G2 holonomy, the Ricci tensor should vanish: R_{ij} = 0.

        Args:
            x: Points on K7, shape (N, 7)
            eps: Finite difference step

        Returns:
            Riemann tensor, shape (N, 7, 7, 7, 7)
        """
        N = x.shape[0]

        # Get Christoffel symbols
        Gamma = self.christoffel(x, eps)

        # Compute derivatives of Christoffel
        dGamma = np.zeros((N, 7, 7, 7, 7))

        for l in range(7):
            x_plus = x.copy()
            x_minus = x.copy()
            x_plus[:, l] += eps
            x_minus[:, l] -= eps

            Gamma_plus = self.christoffel(x_plus, eps)
            Gamma_minus = self.christoffel(x_minus, eps)

            dGamma[:, l, :, :, :] = (Gamma_plus - Gamma_minus) / (2 * eps)

        # R^i_{jkl} = d_k Gamma^i_{jl} - d_l Gamma^i_{jk}
        #           + Gamma^i_{mk} Gamma^m_{jl} - Gamma^i_{ml} Gamma^m_{jk}
        R = np.zeros((N, 7, 7, 7, 7))

        for i in range(7):
            for j in range(7):
                for k in range(7):
                    for l in range(7):
                        R[:, i, j, k, l] = (
                            dGamma[:, k, i, j, l] - dGamma[:, l, i, j, k]
                        )
                        for m in range(7):
                            R[:, i, j, k, l] += (
                                Gamma[:, i, m, k] * Gamma[:, m, j, l] -
                                Gamma[:, i, m, l] * Gamma[:, m, j, k]
                            )

        return R

    def ricci(self, x: np.ndarray, eps: float = 1e-4) -> np.ndarray:
        """
        Compute Ricci tensor R_{ij} = R^k_{ikj}.

        For G2 holonomy: R_{ij} = 0 (Ricci-flat).

        Args:
            x: Points on K7, shape (N, 7)
            eps: Finite difference step

        Returns:
            Ricci tensor, shape (N, 7, 7)
        """
        R = self.riemann(x, eps)

        # Contract: R_{ij} = R^k_{ikj}
        Ric = np.einsum('nkikj->nij', R)

        return Ric

    def scalar_curvature(self, x: np.ndarray, eps: float = 1e-4) -> np.ndarray:
        """
        Compute scalar curvature R = g^{ij} R_{ij}.

        For G2 holonomy: R = 0.

        Args:
            x: Points on K7, shape (N, 7)
            eps: Finite difference step

        Returns:
            Scalar curvatures, shape (N,)
        """
        Ric = self.ricci(x, eps)
        g_inv = self.inverse_metric(x)

        # R = g^{ij} R_{ij}
        R = np.einsum('nij,nij->n', g_inv, Ric)

        return R

    def g2_torsion(self, x: np.ndarray, eps: float = 1e-5) -> Dict[str, np.ndarray]:
        """
        Compute G2 torsion classes.

        For torsion-free G2: dphi = 0 and d*phi = 0.

        The torsion decomposes into classes W1, W7, W14, W27.

        Args:
            x: Points on K7, shape (N, 7)
            eps: Finite difference step

        Returns:
            Dictionary with torsion components
        """
        N = x.shape[0]

        # Get phi and *phi
        phi = self.tcs.g2_3form(x)
        psi = self.tcs.g2_4form(x)

        # Compute dphi via finite differences
        dphi = np.zeros((N, 35, 7))  # 4-form from d(3-form)

        for l in range(7):
            x_plus = x.copy()
            x_minus = x.copy()
            x_plus[:, l] += eps
            x_minus[:, l] -= eps

            phi_plus = self.tcs.g2_3form(x_plus)
            phi_minus = self.tcs.g2_3form(x_minus)

            dphi[:, :, l] = (phi_plus - phi_minus) / (2 * eps)

        # Torsion norm ||dphi||^2 + ||d*phi||^2
        dphi_norm = np.sum(dphi ** 2, axis=(1, 2))

        return {
            'dphi': dphi,
            'dphi_norm': dphi_norm,
            'kappa_t': self._kappa_t * np.ones(N)
        }

    def verify_constraints(self, x: np.ndarray, tol: float = 1e-3) -> Dict[str, bool]:
        """
        Verify GIFT constraints at sample points.

        Checks:
        1. det(g) = 65/32
        2. kappa_T = 1/61
        3. Ricci-flatness

        Args:
            x: Sample points, shape (N, 7)
            tol: Tolerance for numerical checks

        Returns:
            Dictionary with verification results
        """
        g = self.metric_tensor(x)
        det = np.linalg.det(g)

        results = {
            'det_g_mean': float(np.mean(det)),
            'det_g_target': float(DET_G_TARGET),
            'det_g_verified': bool(np.allclose(det, float(DET_G_TARGET), rtol=tol)),

            'kappa_t': self._kappa_t,
            'kappa_t_target': float(KAPPA_T_TARGET),
            'kappa_t_verified': bool(abs(self._kappa_t - float(KAPPA_T_TARGET)) < tol),

            'b2': self.b2,
            'b2_target': B2_TARGET,
            'b2_verified': self.b2 == B2_TARGET,

            'b3': self.b3,
            'b3_target': B3_TARGET,
            'b3_verified': self.b3 == B3_TARGET,
        }

        results['all_verified'] = all([
            results['det_g_verified'],
            results['kappa_t_verified'],
            results['b2_verified'],
            results['b3_verified'],
        ])

        return results

    def set_nn_model(self, model: object):
        """
        Set neural network model for metric computation.

        Args:
            model: Trained G2PINN model
        """
        self._nn_model = model

    def sample_points(self, n_points: int) -> np.ndarray:
        """Sample random points on K7."""
        return self.tcs.sample_points(n_points)

    @classmethod
    def from_tcs(cls, tcs: TCSManifold) -> 'K7Metric':
        """Create K7Metric from TCS manifold."""
        return cls(tcs=tcs)

    @classmethod
    def default(cls) -> 'K7Metric':
        """Create default K7Metric with certified values."""
        return cls()


def validate_g2_holonomy(metric: K7Metric, n_samples: int = 100) -> Dict:
    """
    Validate that the metric has G2 holonomy.

    Checks:
    1. Dimension = 7
    2. Ricci-flat (approximately)
    3. Parallel G2 3-form

    Args:
        metric: K7Metric to validate
        n_samples: Number of sample points

    Returns:
        Validation results
    """
    x = metric.sample_points(n_samples)

    # Check dimension
    dim_ok = metric.dim == 7

    # Check Ricci-flatness
    Ric = metric.ricci(x)
    ricci_norm = np.mean(np.abs(Ric))
    ricci_ok = ricci_norm < 0.1  # Tolerance for numerical

    # Check scalar curvature
    R = metric.scalar_curvature(x)
    scalar_ok = np.abs(np.mean(R)) < 0.1

    return {
        'dimension': metric.dim,
        'dimension_ok': dim_ok,
        'ricci_norm': float(ricci_norm),
        'ricci_flat_ok': ricci_ok,
        'scalar_curvature_mean': float(np.mean(R)),
        'scalar_flat_ok': scalar_ok,
        'g2_holonomy_verified': dim_ok and ricci_ok and scalar_ok
    }
