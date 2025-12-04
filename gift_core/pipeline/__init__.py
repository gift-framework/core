"""
GIFT Pipeline Module - End-to-end computation.

This module provides the complete pipeline from
K7 geometry to physical predictions:

1. Construct TCS manifold
2. Train G2 PINN
3. Extract harmonic forms
4. Compute Yukawa couplings
5. Generate certificates
"""

from .config import PipelineConfig, default_config
from .full_pipeline import GIFTPipeline, PipelineResult, run_pipeline

__all__ = [
    'PipelineConfig',
    'default_config',
    'GIFTPipeline',
    'PipelineResult',
    'run_pipeline',
]
