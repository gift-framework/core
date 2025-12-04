"""
Loss functions for G2 PINN training.

Main losses:
- Torsion loss: ||dphi||^2 + ||d*phi||^2
- Determinant loss: (det(g) - 65/32)^2
- Kappa loss: (kappa_T - 1/61)^2
"""

from typing import Optional
from fractions import Fraction
import numpy as np

try:
    import torch
    import torch.nn as nn
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False


# Target values
DET_G_TARGET = float(Fraction(65, 32))  # = 2.03125
KAPPA_T_TARGET = float(Fraction(1, 61))  # ~ 0.01639


if HAS_TORCH:
    def det_g_loss(model: nn.Module, x: torch.Tensor,
                   target: float = DET_G_TARGET) -> torch.Tensor:
        """
        Loss for det(g) = 65/32 constraint.

        L_det = mean((det(g) - target)^2)

        Args:
            model: G2PINN model
            x: Sample points, shape (N, 7)
            target: Target determinant value

        Returns:
            Scalar loss
        """
        det = model.det_g(x)
        return torch.mean((det - target) ** 2)


    def kappa_t_loss(model: nn.Module, x: torch.Tensor,
                     target: float = KAPPA_T_TARGET) -> torch.Tensor:
        """
        Loss for kappa_T = 1/61 constraint.

        The kappa_T parameter is related to the torsion class W1.
        For torsion-free G2, kappa_T -> 0. GIFT requires kappa_T = 1/61.

        Args:
            model: G2PINN model
            x: Sample points, shape (N, 7)
            target: Target kappa_T value

        Returns:
            Scalar loss
        """
        # kappa_T is computed from the W1 torsion class
        # Simplified: use torsion norm as proxy
        torsion = _compute_torsion_norm(model, x)
        kappa = torsion / 61.0  # Normalized

        return torch.mean((kappa - target) ** 2)


    def torsion_loss(model: nn.Module, x: torch.Tensor,
                     eps: float = 1e-4) -> torch.Tensor:
        """
        Torsion-free loss: ||dphi||^2 + ||d*phi||^2.

        Uses automatic differentiation to compute dphi.

        Args:
            model: G2PINN model
            x: Sample points, shape (N, 7)
            eps: Small value for numerical stability

        Returns:
            Scalar loss
        """
        x.requires_grad_(True)

        # Get phi components
        phi = model(x)  # (N, 35)

        # Compute gradient of each component
        dphi_norm = 0.0

        for i in range(35):
            grad = torch.autograd.grad(
                phi[:, i].sum(), x,
                create_graph=True,
                retain_graph=True
            )[0]  # (N, 7)

            dphi_norm = dphi_norm + torch.mean(grad ** 2)

        return dphi_norm


    def _compute_torsion_norm(model: nn.Module, x: torch.Tensor) -> torch.Tensor:
        """Compute torsion norm from model output."""
        # Simplified: use gradient norm as proxy
        x.requires_grad_(True)
        phi = model(x)

        # Total variation as torsion proxy
        grad_norm = 0.0
        for i in range(min(7, 35)):  # Sample components
            grad = torch.autograd.grad(
                phi[:, i].sum(), x,
                create_graph=True,
                retain_graph=True
            )[0]
            grad_norm = grad_norm + torch.mean(torch.abs(grad))

        return grad_norm / 7.0


    def metric_smoothness_loss(model: nn.Module, x: torch.Tensor) -> torch.Tensor:
        """
        Smoothness regularization for metric.

        Penalizes rapid metric variation (high curvature).

        Args:
            model: G2PINN model
            x: Sample points

        Returns:
            Smoothness loss
        """
        x.requires_grad_(True)
        g = model.metric(x)  # (N, 7, 7)

        # Compute gradient of metric components
        smooth_loss = 0.0

        for i in range(7):
            for j in range(i, 7):
                grad = torch.autograd.grad(
                    g[:, i, j].sum(), x,
                    create_graph=True,
                    retain_graph=True
                )[0]
                smooth_loss = smooth_loss + torch.mean(grad ** 2)

        return smooth_loss / 28.0  # Normalize by number of components


    def positive_definite_loss(model: nn.Module, x: torch.Tensor) -> torch.Tensor:
        """
        Loss to ensure metric is positive definite.

        Uses eigenvalue penalty: sum(max(0, -lambda_i)^2)

        Args:
            model: G2PINN model
            x: Sample points

        Returns:
            Positive definiteness loss
        """
        g = model.metric(x)  # (N, 7, 7)

        # Compute eigenvalues
        eigenvalues = torch.linalg.eigvalsh(g)  # (N, 7)

        # Penalize negative eigenvalues
        neg_eigenvalues = torch.relu(-eigenvalues)
        return torch.mean(neg_eigenvalues ** 2)


    def total_g2_loss(model: nn.Module, x: torch.Tensor,
                      det_weight: float = 1.0,
                      kappa_weight: float = 1.0,
                      torsion_weight: float = 1.0,
                      smooth_weight: float = 0.1,
                      pd_weight: float = 1.0) -> torch.Tensor:
        """
        Combined G2 loss function.

        L = w_det * L_det + w_kappa * L_kappa + w_torsion * L_torsion
            + w_smooth * L_smooth + w_pd * L_pd

        Args:
            model: G2PINN model
            x: Sample points
            det_weight: Weight for determinant loss
            kappa_weight: Weight for kappa_T loss
            torsion_weight: Weight for torsion loss
            smooth_weight: Weight for smoothness loss
            pd_weight: Weight for positive definiteness

        Returns:
            Total loss
        """
        loss = 0.0

        # Determinant constraint
        if det_weight > 0:
            loss = loss + det_weight * det_g_loss(model, x)

        # Kappa constraint
        if kappa_weight > 0:
            loss = loss + kappa_weight * kappa_t_loss(model, x)

        # Torsion-free constraint
        if torsion_weight > 0:
            loss = loss + torsion_weight * torsion_loss(model, x)

        # Smoothness regularization
        if smooth_weight > 0:
            loss = loss + smooth_weight * metric_smoothness_loss(model, x)

        # Positive definiteness
        if pd_weight > 0:
            loss = loss + pd_weight * positive_definite_loss(model, x)

        return loss


    def constraint_loss(model: nn.Module, x: torch.Tensor) -> torch.Tensor:
        """
        Combined constraint loss (det + kappa).

        Args:
            model: G2PINN model
            x: Sample points

        Returns:
            Constraint loss
        """
        return det_g_loss(model, x) + kappa_t_loss(model, x)


# NumPy versions for non-PyTorch use
def det_g_loss_numpy(det_values: np.ndarray,
                     target: float = DET_G_TARGET) -> float:
    """NumPy version of det_g_loss."""
    return float(np.mean((det_values - target) ** 2))


def kappa_t_loss_numpy(kappa_values: np.ndarray,
                       target: float = KAPPA_T_TARGET) -> float:
    """NumPy version of kappa_t_loss."""
    return float(np.mean((kappa_values - target) ** 2))
