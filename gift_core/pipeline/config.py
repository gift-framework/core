"""
Pipeline configuration.

Centralizes all configuration parameters for the GIFT pipeline.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional


@dataclass
class GeometryConfig:
    """Configuration for geometry construction."""

    # TCS parameters
    neck_length: float = 10.0
    twist_angle: float = 1.5708  # pi/2

    # Grid resolution
    resolution: int = 16

    # Sampling
    n_samples: int = 10000


@dataclass
class TrainingConfig:
    """Configuration for PINN training."""

    # Network architecture
    hidden_dims: List[int] = field(default_factory=lambda: [256, 256, 256, 256])
    num_frequencies: int = 64

    # Training parameters
    n_epochs: int = 1000
    batch_size: int = 256
    learning_rate: float = 1e-3

    # Loss weights
    det_weight: float = 1.0
    kappa_weight: float = 1.0
    torsion_weight: float = 1.0

    # Device
    device: str = 'cpu'

    # Curriculum phases
    use_curriculum: bool = True


@dataclass
class HarmonicConfig:
    """Configuration for harmonic form extraction."""

    # Grid resolution
    resolution: int = 16

    # Eigenvalue computation
    n_eigenvalues: int = 100
    zero_threshold: float = 1e-4

    # Target Betti numbers
    b2_target: int = 21
    b3_target: int = 77


@dataclass
class PhysicsConfig:
    """Configuration for physics computation."""

    # Yukawa computation
    n_integration_points: int = 10000

    # Mass spectrum
    n_generations: int = 3

    # Validation tolerances
    mass_ratio_tolerance: float = 0.1
    coupling_tolerance: float = 0.01


@dataclass
class VerificationConfig:
    """Configuration for verification and certificates."""

    # Certificate generation
    n_samples: int = 10000
    confidence_level: float = 0.99  # 3-sigma

    # Export
    export_lean: bool = True
    export_coq: bool = True
    output_dir: str = './certificates'


@dataclass
class PipelineConfig:
    """
    Complete pipeline configuration.

    Aggregates all sub-configurations.
    """

    geometry: GeometryConfig = field(default_factory=GeometryConfig)
    training: TrainingConfig = field(default_factory=TrainingConfig)
    harmonic: HarmonicConfig = field(default_factory=HarmonicConfig)
    physics: PhysicsConfig = field(default_factory=PhysicsConfig)
    verification: VerificationConfig = field(default_factory=VerificationConfig)

    # Pipeline options
    skip_training: bool = False
    load_checkpoint: Optional[str] = None
    save_checkpoint: Optional[str] = None

    # Verbosity
    verbose: bool = True
    log_interval: int = 50


def default_config() -> PipelineConfig:
    """
    Create default pipeline configuration.

    Returns:
        PipelineConfig with default values
    """
    return PipelineConfig()


def fast_config() -> PipelineConfig:
    """
    Create fast configuration for testing.

    Reduced resolution and epochs for quick validation.
    """
    config = PipelineConfig()

    config.geometry.resolution = 8
    config.geometry.n_samples = 1000

    config.training.n_epochs = 100
    config.training.hidden_dims = [64, 64]

    config.harmonic.resolution = 8
    config.harmonic.n_eigenvalues = 20

    config.physics.n_integration_points = 1000

    config.verification.n_samples = 1000

    return config


def production_config() -> PipelineConfig:
    """
    Create production configuration.

    High resolution and thorough training for final results.
    """
    config = PipelineConfig()

    config.geometry.resolution = 32
    config.geometry.n_samples = 100000

    config.training.n_epochs = 10000
    config.training.hidden_dims = [512, 512, 512, 512]
    config.training.num_frequencies = 128

    config.harmonic.resolution = 32
    config.harmonic.n_eigenvalues = 200

    config.physics.n_integration_points = 100000

    config.verification.n_samples = 100000

    return config
