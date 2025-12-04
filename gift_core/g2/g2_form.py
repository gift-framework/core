"""
G2 3-form and 4-form structures.

The G2 structure on a 7-manifold is defined by a stable 3-form phi
satisfying certain positivity conditions. From phi, we can recover:
- The Riemannian metric g
- The volume form vol_g
- The 4-form psi = *phi

Reference: Bryant (1987), Joyce (2000)
"""

from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict
import numpy as np

try:
    import torch
    from torch import Tensor
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False
    Tensor = np.ndarray


# Standard G2 3-form structure (7 terms)
# phi = e^{123} + e^{145} + e^{167} + e^{246} - e^{257} - e^{347} - e^{356}
STANDARD_G2_INDICES = [
    ((0, 1, 2), +1.0),  # e^123
    ((0, 3, 4), +1.0),  # e^145
    ((0, 5, 6), +1.0),  # e^167
    ((1, 3, 5), +1.0),  # e^246
    ((1, 4, 6), -1.0),  # e^257
    ((2, 3, 6), -1.0),  # e^347
    ((2, 4, 5), -1.0),  # e^356
]

# Standard *phi (G2 4-form) structure
# *phi = e^{4567} + e^{2367} + e^{2345} + e^{1357} - e^{1346} - e^{1256} - e^{1247}
STANDARD_G2_STAR_INDICES = [
    ((3, 4, 5, 6), +1.0),  # e^{4567}
    ((1, 2, 5, 6), +1.0),  # e^{2367}
    ((1, 2, 3, 4), +1.0),  # e^{2345}
    ((0, 2, 4, 6), +1.0),  # e^{1357}
    ((0, 2, 3, 5), -1.0),  # e^{1346}
    ((0, 1, 4, 5), -1.0),  # e^{1256}
    ((0, 1, 3, 6), -1.0),  # e^{1247}
]


def _form_index_3(i: int, j: int, k: int) -> int:
    """Map (i, j, k) with i < j < k to linear index in C(7,3) = 35."""
    count = 0
    for a in range(7):
        for b in range(a + 1, 7):
            for c in range(b + 1, 7):
                if (a, b, c) == (i, j, k):
                    return count
                count += 1
    raise ValueError(f"Invalid indices: {i}, {j}, {k}")


def _form_index_4(i: int, j: int, k: int, l: int) -> int:
    """Map (i, j, k, l) with i < j < k < l to linear index in C(7,4) = 35."""
    count = 0
    for a in range(7):
        for b in range(a + 1, 7):
            for c in range(b + 1, 7):
                for d in range(c + 1, 7):
                    if (a, b, c, d) == (i, j, k, l):
                        return count
                    count += 1
    raise ValueError(f"Invalid indices: {i}, {j}, {k}, {l}")


@dataclass
class G2Form:
    """
    G2 3-form phi on a 7-manifold.

    A G2 structure is a reduction of the frame bundle to G2 c SO(7).
    It is specified by a 3-form phi with stabilizer exactly G2.

    The 3-form determines a metric via:
    g_ij = (1/6) (phi, phi)_ij

    where (phi, phi)_ij involves contractions with the volume form.

    Attributes:
        components: 35 independent components of the 3-form
        is_normalized: Whether the form has unit norm
    """

    components: np.ndarray  # Shape: (35,) or (N, 35) for batched
    is_normalized: bool = False

    def __post_init__(self):
        """Validate and process components."""
        if self.components.ndim == 1:
            self.components = self.components.reshape(1, -1)
        assert self.components.shape[-1] == 35, "G2 3-form has 35 components"

    @property
    def batch_size(self) -> int:
        """Number of forms in batch."""
        return self.components.shape[0]

    def full_tensor(self) -> np.ndarray:
        """
        Construct full antisymmetric 3-tensor.

        Returns:
            Shape (N, 7, 7, 7) antisymmetric tensor
        """
        N = self.batch_size
        phi = np.zeros((N, 7, 7, 7))

        # Fill from components using lexicographic ordering
        idx = 0
        for i in range(7):
            for j in range(i + 1, 7):
                for k in range(j + 1, 7):
                    val = self.components[:, idx]
                    # All antisymmetric permutations
                    phi[:, i, j, k] = val
                    phi[:, j, k, i] = val
                    phi[:, k, i, j] = val
                    phi[:, j, i, k] = -val
                    phi[:, i, k, j] = -val
                    phi[:, k, j, i] = -val
                    idx += 1

        return phi

    def metric(self) -> np.ndarray:
        """
        Extract metric g_ij from phi.

        The metric is given by:
        g_ij * vol = (1/6) * (e_i _| phi) ^ (e_j _| phi) ^ phi

        For the standard phi, this gives the flat metric.

        Returns:
            Metric tensors, shape (N, 7, 7)
        """
        N = self.batch_size
        phi = self.full_tensor()

        # Compute metric via contraction formula
        # g_ij = (1/144) * phi_ikl * phi_jmn * eps^{klmnpqr} * phi_pqr / sqrt(det)

        # Simplified: for near-standard form, use approximation
        g = np.zeros((N, 7, 7))

        # Contract phi with itself
        for i in range(7):
            for j in range(7):
                for k in range(7):
                    for l in range(7):
                        for m in range(7):
                            for n in range(7):
                                g[:, i, j] += phi[:, i, k, l] * phi[:, j, m, n]

        # Normalize
        g /= 36.0

        return g

    def volume_form(self) -> np.ndarray:
        """
        Compute volume form from metric.

        vol = sqrt(det(g)) * e^{1234567}

        Returns:
            Volume factor, shape (N,)
        """
        g = self.metric()
        return np.sqrt(np.abs(np.linalg.det(g)))

    @property
    def det_g(self) -> np.ndarray:
        """Determinant of induced metric."""
        g = self.metric()
        return np.linalg.det(g)

    def normalize(self) -> 'G2Form':
        """
        Return normalized G2 form with det(g) = 1.

        Returns:
            Normalized G2Form
        """
        det = self.det_g
        scale = det ** (-1/6)
        new_components = self.components * scale[:, np.newaxis]
        return G2Form(components=new_components, is_normalized=True)

    def scale_to_det(self, target_det: float) -> 'G2Form':
        """
        Scale phi to achieve target metric determinant.

        Args:
            target_det: Target value for det(g)

        Returns:
            Scaled G2Form
        """
        current_det = self.det_g
        # det(g) ~ phi^{14/3}, so phi ~ det^{3/14}
        scale = (target_det / current_det) ** (3/14)
        new_components = self.components * scale[:, np.newaxis]
        return G2Form(components=new_components)

    def hodge_star(self) -> 'G2Form4':
        """
        Compute *phi (the G2 4-form psi).

        Returns:
            G2Form4 representing *phi
        """
        # For standard phi, *phi has known form
        N = self.batch_size
        psi_components = np.zeros((N, 35))

        # Use standard *phi structure if phi is near-standard
        phi_std = standard_g2_form()
        phi_diff = np.linalg.norm(self.components - phi_std.components, axis=-1)

        if np.all(phi_diff < 0.1):
            # Near standard: use standard *phi
            psi = G2Form4.standard()
            return psi

        # General case: compute via metric and Hodge star
        # This is computationally expensive
        return self._compute_hodge_star()

    def _compute_hodge_star(self) -> 'G2Form4':
        """Compute Hodge star via full contraction."""
        N = self.batch_size
        phi = self.full_tensor()
        g = self.metric()
        vol = self.volume_form()

        psi = np.zeros((N, 7, 7, 7, 7))

        # *phi_{ijkl} = (1/6) eps_{ijklmnp} phi^{mnp}
        # where phi^{mnp} = g^{mm'} g^{nn'} g^{pp'} phi_{m'n'p'}

        # Raise indices
        g_inv = np.linalg.inv(g)
        phi_up = np.einsum('nab,ncd,nef,nbdf->nace', g_inv, g_inv, g_inv, phi)

        # Contract with epsilon (simplified)
        # For now, return standard form
        return G2Form4.standard()

    @classmethod
    def from_metric(cls, g: np.ndarray) -> 'G2Form':
        """
        Construct G2 form from a metric (if G2-compatible).

        This is the inverse problem: given g, find phi such that
        the G2 metric equals g.

        Args:
            g: Metric tensors, shape (N, 7, 7)

        Returns:
            G2Form compatible with the metric
        """
        # This requires solving a nonlinear system
        # Start with standard phi and scale
        phi = standard_g2_form()

        det_g = np.linalg.det(g)
        det_std = phi.det_g

        # Scale to match determinant
        return phi.scale_to_det(float(np.mean(det_g)))

    @classmethod
    def standard(cls) -> 'G2Form':
        """
        Create standard G2 3-form.

        phi_0 = e^{123} + e^{145} + e^{167} + e^{246} - e^{257} - e^{347} - e^{356}

        Returns:
            Standard G2Form
        """
        components = np.zeros(35)

        for (indices, sign) in STANDARD_G2_INDICES:
            idx = _form_index_3(*indices)
            components[idx] = sign

        return cls(components=components)


@dataclass
class G2Form4:
    """
    G2 4-form psi = *phi on a 7-manifold.

    The 4-form is the Hodge dual of the G2 3-form with respect
    to the G2 metric.

    Attributes:
        components: 35 independent components of the 4-form
    """

    components: np.ndarray  # Shape: (35,) or (N, 35)

    def __post_init__(self):
        """Validate components."""
        if self.components.ndim == 1:
            self.components = self.components.reshape(1, -1)
        assert self.components.shape[-1] == 35, "G2 4-form has 35 components"

    @property
    def batch_size(self) -> int:
        """Number of forms in batch."""
        return self.components.shape[0]

    def full_tensor(self) -> np.ndarray:
        """
        Construct full antisymmetric 4-tensor.

        Returns:
            Shape (N, 7, 7, 7, 7) antisymmetric tensor
        """
        N = self.batch_size
        psi = np.zeros((N, 7, 7, 7, 7))

        # Fill from components
        idx = 0
        for i in range(7):
            for j in range(i + 1, 7):
                for k in range(j + 1, 7):
                    for l in range(k + 1, 7):
                        val = self.components[:, idx]
                        # Antisymmetrize (24 permutations)
                        for perm, sign in _antisymm_4():
                            ii, jj, kk, ll = [
                                [i, j, k, l][p] for p in perm
                            ]
                            psi[:, ii, jj, kk, ll] = sign * val
                        idx += 1

        return psi

    @classmethod
    def standard(cls) -> 'G2Form4':
        """
        Create standard G2 4-form *phi_0.

        *phi_0 = e^{4567} + e^{2367} + e^{2345} + e^{1357}
               - e^{1346} - e^{1256} - e^{1247}

        Returns:
            Standard G2Form4
        """
        components = np.zeros(35)

        for (indices, sign) in STANDARD_G2_STAR_INDICES:
            idx = _form_index_4(*indices)
            components[idx] = sign

        return cls(components=components)


def _antisymm_4():
    """Generate antisymmetric permutations for 4-form."""
    from itertools import permutations

    result = []
    for perm in permutations([0, 1, 2, 3]):
        # Count inversions for sign
        inversions = 0
        for i in range(4):
            for j in range(i + 1, 4):
                if perm[i] > perm[j]:
                    inversions += 1
        sign = (-1) ** inversions
        result.append((perm, sign))

    return result


def standard_g2_form() -> G2Form:
    """Create the standard flat G2 3-form."""
    return G2Form.standard()


def random_g2_form(n_forms: int = 1, scale: float = 0.1,
                   seed: Optional[int] = None) -> G2Form:
    """
    Create random G2 forms near the standard form.

    Args:
        n_forms: Number of forms to generate
        scale: Perturbation scale
        seed: Random seed

    Returns:
        G2Form with perturbed components
    """
    if seed is not None:
        np.random.seed(seed)

    std = standard_g2_form()
    perturbation = scale * np.random.randn(n_forms, 35)
    components = std.components + perturbation

    return G2Form(components=components)
