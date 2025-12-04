"""
Fourier feature encoding for neural networks.

Random Fourier features help neural networks learn high-frequency
functions by mapping inputs to a higher-dimensional space:

gamma(x) = [cos(2*pi*B*x), sin(2*pi*B*x)]

Reference: Tancik et al. (2020) "Fourier Features Let Networks Learn
High Frequency Functions in Low Dimensional Domains"
"""

from typing import Optional
import numpy as np

try:
    import torch
    import torch.nn as nn
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False


if HAS_TORCH:
    class FourierFeatures(nn.Module):
        """
        Random Fourier feature mapping.

        Maps input x in R^d to gamma(x) in R^{2*num_frequencies}:
        gamma(x) = [cos(2*pi*B*x), sin(2*pi*B*x)]

        where B is a random matrix of shape (num_frequencies, d).

        Attributes:
            input_dim: Input dimension (7 for K7)
            num_frequencies: Number of Fourier frequencies
            scale: Standard deviation for random B matrix
        """

        def __init__(self, input_dim: int = 7, num_frequencies: int = 64,
                     scale: float = 1.0):
            super().__init__()

            self.input_dim = input_dim
            self.num_frequencies = num_frequencies
            self.output_dim = 2 * num_frequencies

            # Random frequency matrix (fixed during training)
            B = torch.randn(num_frequencies, input_dim) * scale
            self.register_buffer('B', B)

        def forward(self, x: torch.Tensor) -> torch.Tensor:
            """
            Apply Fourier feature mapping.

            Args:
                x: Input coordinates, shape (N, input_dim)

            Returns:
                Encoded features, shape (N, 2*num_frequencies)
            """
            # x @ B^T: (N, num_frequencies)
            projected = 2 * np.pi * torch.matmul(x, self.B.T)

            # Concatenate cos and sin
            return torch.cat([torch.cos(projected), torch.sin(projected)], dim=-1)


    class PositionalEncoding(nn.Module):
        """
        Deterministic positional encoding (NeRF-style).

        gamma(x) = [x, sin(2^0 * pi * x), cos(2^0 * pi * x),
                       sin(2^1 * pi * x), cos(2^1 * pi * x), ...]

        Attributes:
            input_dim: Input dimension
            num_frequencies: Number of frequency octaves
            include_input: Whether to include original input
        """

        def __init__(self, input_dim: int = 7, num_frequencies: int = 6,
                     include_input: bool = True):
            super().__init__()

            self.input_dim = input_dim
            self.num_frequencies = num_frequencies
            self.include_input = include_input

            # Output dimension
            self.output_dim = input_dim * (1 + 2 * num_frequencies) if include_input \
                else input_dim * 2 * num_frequencies

            # Frequency scales: 2^0, 2^1, ..., 2^{L-1}
            freq_bands = 2.0 ** torch.arange(num_frequencies)
            self.register_buffer('freq_bands', freq_bands)

        def forward(self, x: torch.Tensor) -> torch.Tensor:
            """
            Apply positional encoding.

            Args:
                x: Input coordinates, shape (N, input_dim)

            Returns:
                Encoded features, shape (N, output_dim)
            """
            outputs = [x] if self.include_input else []

            for freq in self.freq_bands:
                outputs.append(torch.sin(np.pi * freq * x))
                outputs.append(torch.cos(np.pi * freq * x))

            return torch.cat(outputs, dim=-1)


def positional_encoding(x: np.ndarray, num_frequencies: int = 6) -> np.ndarray:
    """
    NumPy implementation of positional encoding.

    Args:
        x: Input coordinates, shape (N, d)
        num_frequencies: Number of frequency octaves

    Returns:
        Encoded features
    """
    outputs = [x]

    for i in range(num_frequencies):
        freq = 2.0 ** i
        outputs.append(np.sin(np.pi * freq * x))
        outputs.append(np.cos(np.pi * freq * x))

    return np.concatenate(outputs, axis=-1)


def gaussian_fourier_features(x: np.ndarray, B: np.ndarray) -> np.ndarray:
    """
    NumPy implementation of Gaussian Fourier features.

    Args:
        x: Input coordinates, shape (N, d)
        B: Random frequency matrix, shape (m, d)

    Returns:
        Encoded features, shape (N, 2*m)
    """
    projected = 2 * np.pi * x @ B.T
    return np.concatenate([np.cos(projected), np.sin(projected)], axis=-1)
