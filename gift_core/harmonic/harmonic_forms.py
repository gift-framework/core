"""
Harmonic form extraction from G2 metric.

Harmonic forms are solutions to Delta omega = 0.
They represent de Rham cohomology classes.

For G2 manifolds:
- H^2: parameterizes metric deformations
- H^3: contains the G2 3-form phi
"""

from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict
import numpy as np
from scipy.sparse.linalg import eigsh

from .hodge_laplacian import HodgeLaplacian


@dataclass
class HarmonicBasis:
    """
    Orthonormal basis of harmonic p-forms.

    Attributes:
        degree: Form degree
        forms: Array of harmonic forms, shape (n_forms, n_points, form_dim)
        eigenvalues: Small eigenvalues (should be ~0)
    """

    degree: int
    forms: np.ndarray
    eigenvalues: np.ndarray

    @property
    def n_forms(self) -> int:
        """Number of harmonic forms (= b_p)."""
        return self.forms.shape[0]

    def __len__(self) -> int:
        return self.n_forms

    def inner_product(self, i: int, j: int) -> float:
        """
        L^2 inner product of forms i and j.

        <omega_i, omega_j> = integral omega_i ^ *omega_j
        """
        # Approximate as sum over grid
        return float(np.sum(self.forms[i] * self.forms[j]))

    def is_orthonormal(self, tol: float = 1e-6) -> bool:
        """Check if basis is orthonormal."""
        n = self.n_forms
        for i in range(n):
            for j in range(n):
                ip = self.inner_product(i, j)
                expected = 1.0 if i == j else 0.0
                if abs(ip - expected) > tol:
                    return False
        return True


@dataclass
class HarmonicExtractor:
    """
    Extract harmonic forms from a G2 metric.

    Uses the Hodge Laplacian to find forms with near-zero eigenvalue.

    Attributes:
        metric: Metric tensor function
        resolution: Grid resolution
        zero_threshold: Threshold for harmonic eigenvalues
    """

    metric: callable
    resolution: int = 16
    zero_threshold: float = 1e-4

    _laplacian: Optional[HodgeLaplacian] = None

    def __post_init__(self):
        """Initialize Laplacian."""
        self._laplacian = HodgeLaplacian(
            metric=self.metric,
            resolution=self.resolution
        )

    def extract_basis(self, degree: int,
                      num_forms: Optional[int] = None) -> HarmonicBasis:
        """
        Extract orthonormal harmonic p-forms.

        Solve Delta omega = lambda omega, keep lambda ~ 0.

        Args:
            degree: Form degree
            num_forms: Expected number of harmonic forms (for validation)

        Returns:
            HarmonicBasis with extracted forms
        """
        # Get Laplacian matrix
        Delta = self._laplacian.laplacian_matrix(degree)

        # Compute smallest eigenvalues/vectors
        k = num_forms * 2 if num_forms else 50
        k = min(k, Delta.shape[0] - 2)

        eigenvalues, eigenvectors = eigsh(
            Delta, k=k, which='SM', sigma=0
        )

        # Sort by eigenvalue
        order = np.argsort(np.abs(eigenvalues))
        eigenvalues = eigenvalues[order]
        eigenvectors = eigenvectors[:, order]

        # Filter near-zero eigenvalues
        harmonic_mask = np.abs(eigenvalues) < self.zero_threshold
        harmonic_eigenvalues = eigenvalues[harmonic_mask]
        harmonic_vectors = eigenvectors[:, harmonic_mask]

        # Reshape to (n_forms, n_points, form_dim)
        n_harmonic = harmonic_vectors.shape[1]
        form_dim = self._laplacian.form_dimension(degree)
        n_points = self._laplacian.n_points

        forms = harmonic_vectors.T.reshape(n_harmonic, n_points, form_dim)

        # Orthonormalize (Gram-Schmidt)
        forms = self._gram_schmidt(forms)

        return HarmonicBasis(
            degree=degree,
            forms=forms,
            eigenvalues=harmonic_eigenvalues
        )

    def _gram_schmidt(self, forms: np.ndarray) -> np.ndarray:
        """
        Gram-Schmidt orthonormalization.

        Args:
            forms: Shape (n_forms, n_points, form_dim)

        Returns:
            Orthonormalized forms
        """
        n = forms.shape[0]
        result = np.zeros_like(forms)

        for i in range(n):
            v = forms[i].copy()

            # Subtract projections
            for j in range(i):
                proj = np.sum(v * result[j]) / np.sum(result[j] ** 2)
                v -= proj * result[j]

            # Normalize
            norm = np.sqrt(np.sum(v ** 2))
            if norm > 1e-10:
                result[i] = v / norm

        return result

    def betti_numbers(self) -> Dict[int, int]:
        """
        Compute all Betti numbers.

        b_p = dim(H^p) = number of harmonic p-forms

        Returns:
            Dictionary {p: b_p}
        """
        betti = {}

        for p in range(8):  # 0 to 7 for 7-manifold
            basis = self.extract_basis(p)
            betti[p] = basis.n_forms

        return betti

    def validate_gift_betti(self) -> Tuple[bool, Dict]:
        """
        Validate GIFT Betti numbers: b2=21, b3=77.

        Returns:
            (is_valid, computed_betti)
        """
        # Only compute b2 and b3
        basis_2 = self.extract_basis(2, num_forms=21)
        basis_3 = self.extract_basis(3, num_forms=77)

        computed = {
            2: basis_2.n_forms,
            3: basis_3.n_forms
        }

        expected = {2: 21, 3: 77}

        is_valid = (computed[2] == expected[2] and computed[3] == expected[3])

        return is_valid, computed


def extract_harmonic_2forms(metric: callable, resolution: int = 16) -> HarmonicBasis:
    """
    Extract harmonic 2-forms (for metric deformations).

    Args:
        metric: Metric function
        resolution: Grid resolution

    Returns:
        HarmonicBasis of 2-forms
    """
    extractor = HarmonicExtractor(metric=metric, resolution=resolution)
    return extractor.extract_basis(2, num_forms=21)


def extract_harmonic_3forms(metric: callable, resolution: int = 16) -> HarmonicBasis:
    """
    Extract harmonic 3-forms (including phi).

    Args:
        metric: Metric function
        resolution: Grid resolution

    Returns:
        HarmonicBasis of 3-forms
    """
    extractor = HarmonicExtractor(metric=metric, resolution=resolution)
    return extractor.extract_basis(3, num_forms=77)


def wedge_product(omega1: np.ndarray, omega2: np.ndarray) -> np.ndarray:
    """
    Compute wedge product of forms.

    (omega1 ^ omega2)_{i1...ip j1...jq} =
        sum over permutations * omega1_{i...} * omega2_{j...}

    Args:
        omega1: p-form, shape (n_points, p_dim)
        omega2: q-form, shape (n_points, q_dim)

    Returns:
        (p+q)-form
    """
    # Simplified: tensor product (full antisymmetrization needed)
    return np.einsum('np,nq->npq', omega1, omega2)
