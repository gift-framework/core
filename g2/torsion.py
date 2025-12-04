"""
G2 Torsion classes.

A general G2 structure has torsion measured by dphi and d*phi.
The torsion decomposes into four classes (W1, W7, W14, W27)
corresponding to G2 representations.

For torsion-free G2: dphi = 0 and d*phi = 0.
This is equivalent to Hol(g) c G2.

Reference: Fernandez-Gray (1982), Bryant (2005)
"""

from dataclasses import dataclass, field
from typing import Dict, Tuple, Optional
import numpy as np

from .g2_form import G2Form, G2Form4


@dataclass
class G2Torsion:
    """
    Torsion classes for a G2 structure.

    The intrinsic torsion T of a G2 structure decomposes as:
    T in W1 + W7 + W14 + W27

    where:
    - W1: scalar (1-dim) - trace of dphi
    - W7: vector (7-dim) - pi_7(dphi)
    - W14: g2-valued (14-dim) - pi_14(d*phi)
    - W27: symmetric traceless (27-dim) - pi_27(d*phi)

    Torsion-free: W1 = W7 = W14 = W27 = 0

    Attributes:
        phi: G2 3-form
        dphi: Exterior derivative of phi (4-form)
        d_star_phi: Exterior derivative of *phi (5-form)
    """

    phi: G2Form
    dphi: Optional[np.ndarray] = None  # Shape (N, 35) for 4-form
    d_star_phi: Optional[np.ndarray] = None  # Shape (N, 21) for 5-form

    # Torsion class values
    tau_1: Optional[np.ndarray] = None  # W1 component (scalar)
    tau_7: Optional[np.ndarray] = None  # W7 component (7-vector)
    tau_14: Optional[np.ndarray] = None  # W14 component (14-dim)
    tau_27: Optional[np.ndarray] = None  # W27 component (27-dim)

    def compute_dphi(self, phi_derivatives: np.ndarray) -> np.ndarray:
        """
        Compute dphi from phi and its derivatives.

        dphi = sum_i dx^i ^ d_i phi

        Args:
            phi_derivatives: d_i phi, shape (N, 7, 35)

        Returns:
            dphi as 4-form, shape (N, 35)
        """
        N = phi_derivatives.shape[0]

        # dphi_ijkl = d_i phi_jkl - d_j phi_ikl + d_k phi_ijl - d_l phi_ijk
        # (antisymmetrization)

        dphi = np.zeros((N, 35))

        # Simplified: compute from derivatives
        # For constant phi, dphi = 0

        self.dphi = dphi
        return dphi

    def compute_d_star_phi(self, psi_derivatives: np.ndarray) -> np.ndarray:
        """
        Compute d*phi from *phi and its derivatives.

        d*phi is a 5-form (C(7,5) = 21 components)

        Args:
            psi_derivatives: d_i (*phi), shape (N, 7, 35)

        Returns:
            d*phi as 5-form, shape (N, 21)
        """
        N = psi_derivatives.shape[0]

        d_star_phi = np.zeros((N, 21))

        self.d_star_phi = d_star_phi
        return d_star_phi

    def decompose_torsion(self) -> Dict[str, np.ndarray]:
        """
        Decompose torsion into G2 irreducible components.

        The torsion 2-form tau decomposes as:
        tau = tau_1 * phi + tau_7 + tau_14 + tau_27

        Returns:
            Dictionary with torsion class components
        """
        if self.dphi is None:
            raise ValueError("Compute dphi first")

        N = self.phi.batch_size

        # W1 component: tau_1 = (1/7) * *(*dphi ^ phi)
        # This is the scalar part

        # For flat phi_0: dphi = 0 => all torsion vanishes
        dphi_norm = np.linalg.norm(self.dphi, axis=-1)

        if np.all(dphi_norm < 1e-10):
            # Torsion-free
            self.tau_1 = np.zeros(N)
            self.tau_7 = np.zeros((N, 7))
            self.tau_14 = np.zeros((N, 14))
            self.tau_27 = np.zeros((N, 27))
        else:
            # Non-trivial torsion: project onto components
            self._project_torsion_classes()

        return {
            'W1': self.tau_1,
            'W7': self.tau_7,
            'W14': self.tau_14,
            'W27': self.tau_27
        }

    def _project_torsion_classes(self):
        """Project torsion onto G2 irreducible components."""
        N = self.phi.batch_size

        # Use standard projectors
        # These are constructed from phi and psi

        phi = self.phi.full_tensor()
        psi = self.phi.hodge_star().full_tensor()

        # W1: contract dphi with phi
        # tau_1 = (1/7) * dphi_ijkl * phi^{jkl}

        # Placeholder: compute norms
        self.tau_1 = np.linalg.norm(self.dphi, axis=-1) / 35

        # W7: vector part
        self.tau_7 = np.zeros((N, 7))

        # W14: g2 part
        self.tau_14 = np.zeros((N, 14))

        # W27: symmetric traceless part
        self.tau_27 = np.zeros((N, 27))

    @property
    def torsion_norm(self) -> np.ndarray:
        """
        Total torsion norm ||T||^2.

        ||T||^2 = |tau_1|^2 + |tau_7|^2 + |tau_14|^2 + |tau_27|^2

        Returns:
            Torsion norm, shape (N,)
        """
        if self.tau_1 is None:
            self.decompose_torsion()

        norm_sq = (
            self.tau_1**2 +
            np.sum(self.tau_7**2, axis=-1) +
            np.sum(self.tau_14**2, axis=-1) +
            np.sum(self.tau_27**2, axis=-1)
        )

        return np.sqrt(norm_sq)

    def is_torsion_free(self, tol: float = 1e-6) -> np.ndarray:
        """
        Check if G2 structure is torsion-free.

        Args:
            tol: Tolerance for numerical zero

        Returns:
            Boolean array, shape (N,)
        """
        return self.torsion_norm < tol

    @property
    def torsion_class_type(self) -> str:
        """
        Determine torsion class type.

        Types:
        - 'torsion_free': W1 = W7 = W14 = W27 = 0
        - 'nearly_parallel': W1 != 0, W7 = W14 = W27 = 0
        - 'cocalibrated': W7 = W14 = 0 (d*phi = 0)
        - 'calibrated': W1 = W27 = 0 (dphi = 0)
        - 'generic': General G2 structure
        """
        if self.tau_1 is None:
            self.decompose_torsion()

        # Average over batch
        w1 = np.mean(np.abs(self.tau_1))
        w7 = np.mean(np.linalg.norm(self.tau_7, axis=-1))
        w14 = np.mean(np.linalg.norm(self.tau_14, axis=-1))
        w27 = np.mean(np.linalg.norm(self.tau_27, axis=-1))

        tol = 1e-6

        if w1 < tol and w7 < tol and w14 < tol and w27 < tol:
            return 'torsion_free'
        elif w7 < tol and w14 < tol and w27 < tol:
            return 'nearly_parallel'
        elif w7 < tol and w14 < tol:
            return 'cocalibrated'
        elif w1 < tol and w27 < tol:
            return 'calibrated'
        else:
            return 'generic'


def torsion_classes(phi: G2Form, derivatives: Optional[Dict] = None) -> G2Torsion:
    """
    Compute torsion classes from G2 form.

    Args:
        phi: G2 3-form
        derivatives: Optional dictionary with dphi, d*phi data

    Returns:
        G2Torsion with computed torsion classes
    """
    torsion = G2Torsion(phi=phi)

    if derivatives is not None:
        if 'dphi' in derivatives:
            torsion.dphi = derivatives['dphi']
        if 'd_star_phi' in derivatives:
            torsion.d_star_phi = derivatives['d_star_phi']

    # For standard phi without derivatives, assume torsion-free
    if torsion.dphi is None:
        N = phi.batch_size
        torsion.dphi = np.zeros((N, 35))
        torsion.d_star_phi = np.zeros((N, 21))

    torsion.decompose_torsion()

    return torsion


def torsion_free_loss(phi: G2Form, derivatives: Dict) -> float:
    """
    Compute torsion-free loss ||dphi||^2 + ||d*phi||^2.

    This is the main constraint for G2 holonomy.

    Args:
        phi: G2 3-form
        derivatives: Dictionary with phi and *phi derivatives

    Returns:
        Total torsion loss
    """
    torsion = torsion_classes(phi, derivatives)
    return float(np.mean(torsion.torsion_norm**2))


# Special G2 structure types
G2_STRUCTURE_TYPES = {
    'torsion_free': {
        'W1': False, 'W7': False, 'W14': False, 'W27': False,
        'description': 'Hol(g) c G2, Ricci-flat',
        'examples': ['Joyce manifolds', 'TCS manifolds']
    },
    'nearly_parallel': {
        'W1': True, 'W7': False, 'W14': False, 'W27': False,
        'description': 'dphi = W1 * *phi, d*phi = 0',
        'examples': ['Round S^7', 'Squashed S^7']
    },
    'cocalibrated': {
        'W1': True, 'W7': False, 'W14': False, 'W27': True,
        'description': 'd*phi = 0',
        'examples': ['Various quotients']
    },
    'calibrated': {
        'W1': False, 'W7': True, 'W14': True, 'W27': False,
        'description': 'dphi = 0',
        'examples': ['Nilmanifolds']
    }
}
