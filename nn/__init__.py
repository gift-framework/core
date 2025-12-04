"""
GIFT Neural Network Module - PINN for G2 metrics.

This module implements Physics-Informed Neural Networks (PINN)
for learning the G2 metric on K7 that satisfies:
- Torsion-free condition: dphi = 0, d*phi = 0
- GIFT constraints: det(g) = 65/32, kappa_T = 1/61
"""

from .fourier_features import FourierFeatures, positional_encoding
from .g2_pinn import G2PINN, create_g2_pinn
from .training import G2Trainer, TrainConfig, TrainResult
from .loss_functions import (
    torsion_loss,
    constraint_loss,
    det_g_loss,
    kappa_t_loss,
    total_g2_loss
)

__all__ = [
    'FourierFeatures',
    'positional_encoding',
    'G2PINN',
    'create_g2_pinn',
    'G2Trainer',
    'TrainConfig',
    'TrainResult',
    'torsion_loss',
    'constraint_loss',
    'det_g_loss',
    'kappa_t_loss',
    'total_g2_loss',
]
