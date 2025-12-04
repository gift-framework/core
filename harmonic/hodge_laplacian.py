"""
Hodge Laplacian on differential forms.

The Hodge Laplacian Delta = d*d + dd* acts on differential forms.
Harmonic forms (ker Delta) represent cohomology classes.

On a G2 manifold, the Laplacian respects the G2-decomposition
of the form spaces.
"""

from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict
import numpy as np
from scipy import sparse
from scipy.sparse.linalg import eigsh


@dataclass
class HodgeLaplacian:
    """
    Hodge Laplacian operator on a Riemannian manifold.

    Delta = d*d + dd* where:
    - d is exterior derivative
    - d* = (-1)^{n(p+1)+1} * d * is the codifferential

    For a metric g, we discretize Delta using finite elements
    or finite differences.

    Attributes:
        metric: Metric tensor function (coords -> g_ij)
        dim: Manifold dimension (7 for G2)
        resolution: Discretization resolution
    """

    metric: callable  # (N, 7) -> (N, 7, 7)
    dim: int = 7
    resolution: int = 16

    # Discretization data
    _grid: Optional[np.ndarray] = None
    _laplacian_matrices: Dict[int, sparse.csr_matrix] = field(default_factory=dict)

    def __post_init__(self):
        """Initialize grid if not provided."""
        if self._grid is None:
            self._setup_grid()

    def _setup_grid(self):
        """Create discretization grid on [0,1]^7."""
        n = self.resolution
        coords = np.linspace(0, 1, n)
        grids = np.meshgrid(*[coords] * self.dim, indexing='ij')
        self._grid = np.stack([g.flatten() for g in grids], axis=-1)

    @property
    def n_points(self) -> int:
        """Number of grid points."""
        return self._grid.shape[0]

    def form_dimension(self, degree: int) -> int:
        """
        Dimension of p-forms space at each point.

        dim(Lambda^p R^7) = C(7, p)
        """
        from math import comb
        return comb(self.dim, degree)

    def laplacian_matrix(self, degree: int) -> sparse.csr_matrix:
        """
        Construct Laplacian matrix for p-forms.

        Delta_p: Omega^p -> Omega^p

        Discretized as:
        Delta_{ij} = -sum_k (g^{kk} * (D_k)_ij^2)

        where D_k are finite difference operators.

        Args:
            degree: Form degree p

        Returns:
            Sparse Laplacian matrix
        """
        if degree in self._laplacian_matrices:
            return self._laplacian_matrices[degree]

        n = self.resolution
        N = n ** self.dim  # Total grid points
        form_dim = self.form_dimension(degree)

        # Total matrix size: N * form_dim
        total_dim = N * form_dim

        # Build sparse Laplacian
        rows, cols, data = [], [], []

        # Metric at grid points
        g = self.metric(self._grid)  # (N, 7, 7)
        g_inv = np.linalg.inv(g)  # (N, 7, 7)

        # Grid spacing
        h = 1.0 / (n - 1)

        # For each grid point, add finite difference stencil
        for idx in range(N):
            # Multi-index
            multi_idx = np.unravel_index(idx, (n,) * self.dim)

            for p in range(form_dim):
                row = idx * form_dim + p

                # Diagonal: -2 * sum(g^{kk}) / h^2
                diag = 0.0
                for k in range(self.dim):
                    diag -= 2 * g_inv[idx, k, k] / h**2

                rows.append(row)
                cols.append(row)
                data.append(diag)

                # Off-diagonal: neighbors in each direction
                for k in range(self.dim):
                    for delta in [-1, 1]:
                        new_idx = list(multi_idx)
                        new_idx[k] += delta

                        # Boundary: Neumann (zero flux)
                        if 0 <= new_idx[k] < n:
                            neighbor = np.ravel_multi_index(
                                new_idx, (n,) * self.dim
                            )
                            col = neighbor * form_dim + p
                            val = g_inv[idx, k, k] / h**2

                            rows.append(row)
                            cols.append(col)
                            data.append(val)

        Delta = sparse.csr_matrix(
            (data, (rows, cols)),
            shape=(total_dim, total_dim)
        )

        self._laplacian_matrices[degree] = Delta
        return Delta

    def eigenvalues(self, degree: int, k: int = 10) -> np.ndarray:
        """
        Compute smallest k eigenvalues of Delta_p.

        Args:
            degree: Form degree
            k: Number of eigenvalues

        Returns:
            Sorted eigenvalues
        """
        Delta = self.laplacian_matrix(degree)

        # Use shift-invert mode for smallest eigenvalues
        eigenvalues, _ = eigsh(
            Delta, k=min(k, Delta.shape[0] - 2),
            which='SM', sigma=0
        )

        return np.sort(np.abs(eigenvalues))

    def harmonic_dimension(self, degree: int,
                           zero_threshold: float = 1e-6) -> int:
        """
        Count near-zero eigenvalues (harmonic forms).

        dim(H^p) = #{lambda_i : lambda_i < threshold}

        Args:
            degree: Form degree
            zero_threshold: Threshold for "zero" eigenvalue

        Returns:
            Number of harmonic forms
        """
        eigenvalues = self.eigenvalues(degree, k=50)
        return int(np.sum(eigenvalues < zero_threshold))


def laplacian_eigenvalues(metric: callable, degree: int,
                          resolution: int = 16, k: int = 20) -> np.ndarray:
    """
    Compute Laplacian eigenvalues for p-forms.

    Args:
        metric: Metric tensor function
        degree: Form degree
        resolution: Grid resolution
        k: Number of eigenvalues

    Returns:
        Smallest k eigenvalues
    """
    laplacian = HodgeLaplacian(metric=metric, resolution=resolution)
    return laplacian.eigenvalues(degree, k)


def analytic_eigenvalues_flat_torus(degree: int, n_modes: int = 10) -> np.ndarray:
    """
    Analytic eigenvalues on flat T^7.

    For the flat torus T^7 = R^7/Z^7:
    lambda_k = 4*pi^2 * |k|^2

    where k in Z^7.

    Args:
        degree: Form degree
        n_modes: Number of modes per direction

    Returns:
        Eigenvalues sorted
    """
    from math import comb

    # Generate lattice modes
    eigenvalues = []

    for norm_sq in range(n_modes**2):
        # Count lattice points with |k|^2 = norm_sq
        # Multiplicity is related to representation theory
        if norm_sq == 0:
            # Zero mode: dim(H^p(T^7)) = C(7, p)
            multiplicity = comb(7, degree)
        else:
            # Rough estimate
            multiplicity = 1

        eigenvalues.extend([4 * np.pi**2 * norm_sq] * multiplicity)

    return np.array(sorted(eigenvalues)[:100])
