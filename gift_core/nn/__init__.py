"""
GIFT Neural Network Module - PINN for G2 metrics.

This module implements Physics-Informed Neural Networks (PINN)
for learning the G2 metric on K7 that satisfies:
- Torsion-free condition: dphi = 0, d*phi = 0
- GIFT constraints: det(g) = 65/32, kappa_T = 1/61

V3.1.4: GIFT-Native PINN with built-in G2 structure
- Fano plane epsilon_ijk (exact)
- G2 adjoint representation (14 DOF)
- Analytical extraction capabilities
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

# V3.1.4: GIFT-Native PINN
try:
    from .gift_native_pinn import (
        # Constants
        B2, B3, DIM_G2, DET_G_TARGET, DET_G_TARGET_FLOAT,
        H_STAR, TORSION_THRESHOLD, PINN_TARGET_TORSION,
        FANO_LINES, EPSILON,
        # Functions
        build_epsilon_tensor, phi0_standard,
        g2_generators, adjoint_to_3form_variation,
        # Classes
        GIFTNativePINN, GIFTNativeLoss,
        GIFTTrainConfig, GIFTTrainResult,
        # Training
        sample_k7_points, train_gift_native_pinn,
        # Extraction
        extract_fourier_coefficients, rationalize_coefficients,
        export_analytical_form,
        # Factory
        create_gift_native_pinn,
    )
    HAS_GIFT_NATIVE = True
except ImportError:
    HAS_GIFT_NATIVE = False

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
    # V3.1.4: GIFT-Native PINN
    'HAS_GIFT_NATIVE',
    'GIFTNativePINN',
    'GIFTNativeLoss',
    'GIFTTrainConfig',
    'GIFTTrainResult',
    'create_gift_native_pinn',
    'train_gift_native_pinn',
    'sample_k7_points',
    'extract_fourier_coefficients',
    'rationalize_coefficients',
    'export_analytical_form',
    'phi0_standard',
    'FANO_LINES',
    'EPSILON',
]
