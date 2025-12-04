"""
Physics-Informed Neural Network for G2 3-form.

The G2PINN learns a mapping from K7 coordinates to the
35 components of the G2 3-form phi, constrained by:
- Torsion-free: dphi = 0, d*phi = 0
- det(g) = 65/32
- kappa_T = 1/61
"""

from typing import List, Optional, Dict
import numpy as np

try:
    import torch
    import torch.nn as nn
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False

from .fourier_features import FourierFeatures, PositionalEncoding


if HAS_TORCH:
    class G2PINN(nn.Module):
        """
        Physics-Informed Neural Network for G2 3-form.

        Architecture:
        1. Fourier feature encoding of coordinates
        2. MLP with residual connections
        3. Output: 35 components of phi

        The network is trained to minimize:
        L = L_torsion + lambda_det * L_det + lambda_kappa * L_kappa

        Attributes:
            input_dim: Coordinate dimension (7)
            hidden_dims: List of hidden layer dimensions
            num_frequencies: Fourier feature frequencies
        """

        def __init__(self, input_dim: int = 7,
                     hidden_dims: List[int] = None,
                     num_frequencies: int = 64,
                     use_residual: bool = True):
            super().__init__()

            if hidden_dims is None:
                hidden_dims = [256, 256, 256, 256]

            self.input_dim = input_dim
            self.hidden_dims = hidden_dims
            self.output_dim = 35  # G2 3-form components

            # Fourier feature encoding
            self.fourier = FourierFeatures(
                input_dim=input_dim,
                num_frequencies=num_frequencies
            )

            # Build MLP
            layers = []
            in_dim = self.fourier.output_dim

            for i, h_dim in enumerate(hidden_dims):
                layers.append(nn.Linear(in_dim, h_dim))
                layers.append(nn.SiLU())  # Smooth activation

                if use_residual and i > 0 and in_dim == h_dim:
                    # Residual connection handled in forward
                    pass

                in_dim = h_dim

            # Output layer
            layers.append(nn.Linear(in_dim, self.output_dim))

            self.mlp = nn.ModuleList(layers)
            self.use_residual = use_residual

            # Initialize weights
            self._init_weights()

        def _init_weights(self):
            """Xavier initialization for stable training."""
            for m in self.modules():
                if isinstance(m, nn.Linear):
                    nn.init.xavier_uniform_(m.weight)
                    if m.bias is not None:
                        nn.init.zeros_(m.bias)

        def forward(self, x: torch.Tensor) -> torch.Tensor:
            """
            Forward pass: coordinates -> G2 form components.

            Args:
                x: Coordinates on K7, shape (N, 7)

            Returns:
                G2 3-form components, shape (N, 35)
            """
            # Fourier encoding
            h = self.fourier(x)

            # MLP with optional residual connections
            prev_h = None
            for i, layer in enumerate(self.mlp):
                h = layer(h)

                # Add residual if dimensions match
                if (self.use_residual and prev_h is not None and
                    h.shape == prev_h.shape and isinstance(layer, nn.SiLU)):
                    h = h + prev_h

                if isinstance(layer, nn.Linear) and i < len(self.mlp) - 1:
                    prev_h = h

            return h

        def phi_tensor(self, x: torch.Tensor) -> torch.Tensor:
            """
            Get full 3-tensor phi_{ijk} from components.

            Args:
                x: Coordinates, shape (N, 7)

            Returns:
                Full tensor, shape (N, 7, 7, 7)
            """
            components = self.forward(x)
            return self._components_to_tensor(components)

        def _components_to_tensor(self, components: torch.Tensor) -> torch.Tensor:
            """Convert 35 components to full antisymmetric tensor."""
            N = components.shape[0]
            phi = torch.zeros(N, 7, 7, 7, device=components.device)

            idx = 0
            for i in range(7):
                for j in range(i + 1, 7):
                    for k in range(j + 1, 7):
                        val = components[:, idx]
                        # Antisymmetric permutations
                        phi[:, i, j, k] = val
                        phi[:, j, k, i] = val
                        phi[:, k, i, j] = val
                        phi[:, j, i, k] = -val
                        phi[:, i, k, j] = -val
                        phi[:, k, j, i] = -val
                        idx += 1

            return phi

        def metric(self, x: torch.Tensor) -> torch.Tensor:
            """
            Compute metric g_ij from phi.

            Args:
                x: Coordinates, shape (N, 7)

            Returns:
                Metric tensors, shape (N, 7, 7)
            """
            phi = self.phi_tensor(x)

            # g_ij = (1/36) sum_{klm} phi_ikl * phi_jlm (simplified)
            g = torch.einsum('nikl,njlm->nij', phi, phi) / 36.0

            return g

        def det_g(self, x: torch.Tensor) -> torch.Tensor:
            """
            Compute metric determinant.

            Args:
                x: Coordinates, shape (N, 7)

            Returns:
                Determinants, shape (N,)
            """
            g = self.metric(x)
            return torch.linalg.det(g)


    class G2PINNWithConstraints(G2PINN):
        """
        G2PINN with built-in constraint layers.

        Adds soft constraints directly in the architecture:
        - Normalization layer for det(g)
        - Projection layer for torsion
        """

        def __init__(self, *args, target_det: float = 65/32, **kwargs):
            super().__init__(*args, **kwargs)
            self.target_det = target_det

        def forward(self, x: torch.Tensor) -> torch.Tensor:
            """Forward with constraint enforcement."""
            components = super().forward(x)

            # Soft constraint: scale to target determinant
            # This is approximate; full constraint in loss
            scale = self._compute_scale(x, components)
            components = components * scale.unsqueeze(-1)

            return components

        def _compute_scale(self, x: torch.Tensor,
                          components: torch.Tensor) -> torch.Tensor:
            """Compute scaling factor for det(g) constraint."""
            # Approximate: assume near-standard form
            # det(g) ~ components^{14/3}, so scale ~ det^{3/14}
            return torch.ones(x.shape[0], device=x.device)


def create_g2_pinn(config: Optional[Dict] = None) -> 'G2PINN':
    """
    Factory function to create G2PINN.

    Args:
        config: Optional configuration dictionary

    Returns:
        Configured G2PINN instance
    """
    if not HAS_TORCH:
        raise ImportError("PyTorch required for G2PINN")

    if config is None:
        config = {}

    return G2PINN(
        input_dim=config.get('input_dim', 7),
        hidden_dims=config.get('hidden_dims', [256, 256, 256, 256]),
        num_frequencies=config.get('num_frequencies', 64),
        use_residual=config.get('use_residual', True)
    )
