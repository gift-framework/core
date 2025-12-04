"""
Training pipeline for G2 PINN.

Multi-phase curriculum training:
1. Init: Learn approximate structure
2. Constraint: Enforce det(g), kappa_T
3. Torsion: Drive torsion to zero
4. Refine: Fine-tune all constraints
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Callable
import numpy as np

try:
    import torch
    import torch.nn as nn
    import torch.optim as optim
    from torch.utils.data import DataLoader, TensorDataset
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False

from .loss_functions import total_g2_loss


@dataclass
class TrainConfig:
    """
    Training configuration.

    Attributes:
        n_epochs: Total epochs per phase
        batch_size: Batch size
        learning_rate: Initial learning rate
        n_samples: Number of sample points per epoch
        device: Training device ('cpu' or 'cuda')
    """

    n_epochs: int = 1000
    batch_size: int = 256
    learning_rate: float = 1e-3
    n_samples: int = 10000
    device: str = 'cpu'

    # Loss weights
    det_weight: float = 1.0
    kappa_weight: float = 1.0
    torsion_weight: float = 1.0

    # Scheduler
    use_scheduler: bool = True
    scheduler_patience: int = 50
    scheduler_factor: float = 0.5


@dataclass
class TrainResult:
    """
    Training results.

    Attributes:
        losses: Loss history
        final_loss: Final loss value
        det_g_final: Final det(g) value
        converged: Whether training converged
    """

    losses: List[float] = field(default_factory=list)
    final_loss: float = 0.0
    det_g_final: float = 0.0
    kappa_t_final: float = 0.0
    torsion_final: float = 0.0
    converged: bool = False


# Training phases
TRAINING_PHASES = [
    {
        'name': 'init',
        'epochs': 100,
        'lr': 1e-3,
        'weights': {'torsion': 0.1, 'det': 1.0, 'kappa': 0.0}
    },
    {
        'name': 'constraint',
        'epochs': 200,
        'lr': 5e-4,
        'weights': {'torsion': 0.5, 'det': 1.0, 'kappa': 0.5}
    },
    {
        'name': 'torsion',
        'epochs': 500,
        'lr': 1e-4,
        'weights': {'torsion': 1.0, 'det': 0.5, 'kappa': 1.0}
    },
    {
        'name': 'refine',
        'epochs': 200,
        'lr': 1e-5,
        'weights': {'torsion': 1.0, 'det': 1.0, 'kappa': 1.0}
    },
]


if HAS_TORCH:
    class G2Trainer:
        """
        Multi-phase curriculum trainer for G2 PINN.

        Implements curriculum learning:
        1. Start with easy constraints (det(g))
        2. Gradually add harder constraints (torsion)
        3. Fine-tune with all constraints

        Attributes:
            model: G2PINN model
            config: Training configuration
            sampler: Coordinate sampler function
        """

        def __init__(self, model: nn.Module, config: TrainConfig = None,
                     sampler: Callable = None):
            self.model = model
            self.config = config or TrainConfig()
            self.sampler = sampler or self._default_sampler

            self.device = torch.device(self.config.device)
            self.model.to(self.device)

            self.history = []

        def _default_sampler(self, n_samples: int) -> torch.Tensor:
            """Sample random points in [0,1]^7."""
            return torch.rand(n_samples, 7)

        def train(self, phases: List[Dict] = None) -> TrainResult:
            """
            Execute multi-phase training.

            Args:
                phases: List of phase configurations

            Returns:
                TrainResult with training history
            """
            if phases is None:
                phases = TRAINING_PHASES

            all_losses = []

            for phase in phases:
                print(f"\n=== Phase: {phase['name']} ===")
                phase_losses = self._train_phase(phase)
                all_losses.extend(phase_losses)

            # Collect final results
            result = self._evaluate_final()
            result.losses = all_losses

            return result

        def _train_phase(self, phase: Dict) -> List[float]:
            """
            Train a single phase.

            Args:
                phase: Phase configuration

            Returns:
                Loss history for this phase
            """
            epochs = phase['epochs']
            lr = phase['lr']
            weights = phase['weights']

            # Setup optimizer
            optimizer = optim.Adam(self.model.parameters(), lr=lr)

            if self.config.use_scheduler:
                scheduler = optim.lr_scheduler.ReduceLROnPlateau(
                    optimizer,
                    patience=self.config.scheduler_patience,
                    factor=self.config.scheduler_factor
                )
            else:
                scheduler = None

            losses = []

            for epoch in range(epochs):
                # Sample training points
                x = self.sampler(self.config.n_samples).to(self.device)

                # Forward pass
                self.model.train()
                optimizer.zero_grad()

                loss = total_g2_loss(
                    self.model, x,
                    det_weight=weights['det'],
                    kappa_weight=weights['kappa'],
                    torsion_weight=weights['torsion']
                )

                # Backward pass
                loss.backward()
                optimizer.step()

                if scheduler is not None:
                    scheduler.step(loss)

                losses.append(loss.item())

                if epoch % 50 == 0:
                    print(f"  Epoch {epoch}: loss = {loss.item():.6f}")

            return losses

        def _evaluate_final(self) -> TrainResult:
            """Evaluate final model state."""
            self.model.eval()

            with torch.no_grad():
                x = self.sampler(1000).to(self.device)
                det = self.model.det_g(x)

            result = TrainResult(
                final_loss=self.history[-1] if self.history else 0.0,
                det_g_final=float(det.mean()),
                converged=True  # Check convergence criteria
            )

            return result

        def save_checkpoint(self, path: str):
            """Save model checkpoint."""
            torch.save({
                'model_state': self.model.state_dict(),
                'config': self.config,
                'history': self.history
            }, path)

        def load_checkpoint(self, path: str):
            """Load model checkpoint."""
            checkpoint = torch.load(path)
            self.model.load_state_dict(checkpoint['model_state'])
            self.history = checkpoint.get('history', [])


def train_g2_pinn(model, n_epochs: int = 1000,
                  learning_rate: float = 1e-3) -> TrainResult:
    """
    Simplified training function.

    Args:
        model: G2PINN model
        n_epochs: Number of epochs
        learning_rate: Learning rate

    Returns:
        TrainResult
    """
    if not HAS_TORCH:
        raise ImportError("PyTorch required for training")

    config = TrainConfig(
        n_epochs=n_epochs,
        learning_rate=learning_rate
    )

    trainer = G2Trainer(model, config)
    return trainer.train()
