"""
Yukawa tensor computation from harmonic forms.

The Yukawa couplings in M-theory compactifications are given by
triple products of harmonic forms:

Y_ijk = integral_{K7} omega_i ^ omega_j ^ omega_k

where omega_i are harmonic forms.

Reference: Acharya-Witten (2001), Atiyah-Witten (2002)
"""

from dataclasses import dataclass, field
from typing import Optional, Tuple, List
import numpy as np


@dataclass
class YukawaTensor:
    """
    Yukawa coupling tensor from G2 compactification.

    The Yukawa couplings arise from the superpotential:
    W = integral phi ^ Omega

    and determine fermion mass matrices.

    Attributes:
        basis_2: Harmonic 2-forms (b2 = 21 forms)
        basis_3: Harmonic 3-forms (b3 = 77 forms)
        tensor: The computed Y_ijk tensor
    """

    basis_2: np.ndarray  # Shape (21, n_points, 21) - 21 forms
    basis_3: np.ndarray  # Shape (77, n_points, 35) - 77 forms
    grid: np.ndarray     # Integration grid points
    volume_element: np.ndarray  # sqrt(det(g)) at each point

    _tensor: Optional[np.ndarray] = None  # Y_ijk

    @property
    def n2(self) -> int:
        """Number of 2-forms."""
        return self.basis_2.shape[0]

    @property
    def n3(self) -> int:
        """Number of 3-forms."""
        return self.basis_3.shape[0]

    @property
    def tensor(self) -> np.ndarray:
        """Yukawa tensor Y_ijk."""
        if self._tensor is None:
            self._compute_tensor()
        return self._tensor

    def _compute_tensor(self):
        """
        Compute Yukawa tensor via integration.

        Y_ijk = integral omega2_i ^ omega3_j ^ omega3_k
              = sum_x omega2_i(x) ^ omega3_j(x) ^ omega3_k(x) * vol(x)

        The wedge product omega2 ^ omega3 ^ omega3 is a 7-form,
        which we integrate over K7.
        """
        n2, n3 = self.n2, self.n3
        self._tensor = np.zeros((n2, n3, n3))

        for i in range(n2):
            omega_i = self.basis_2[i]  # (n_points, 21)

            for j in range(n3):
                omega_j = self.basis_3[j]  # (n_points, 35)

                for k in range(j, n3):  # Symmetry in j, k
                    omega_k = self.basis_3[k]

                    # Compute wedge product and integrate
                    integral = self._integrate_wedge(omega_i, omega_j, omega_k)

                    self._tensor[i, j, k] = integral
                    self._tensor[i, k, j] = integral  # Symmetry

    def _integrate_wedge(self, omega2: np.ndarray, omega3_1: np.ndarray,
                         omega3_2: np.ndarray) -> float:
        """
        Integrate wedge product omega2 ^ omega3 ^ omega3.

        This is a 2+3+3=8-form, but on a 7-manifold.
        The relevant coupling is actually from a different combination.

        For G2 Yukawas:
        Y = integral phi ^ (form) where phi is the G2 form.
        """
        # Simplified: use L2 inner product as proxy
        # Full computation requires explicit 7-form integration

        # Approximate wedge as product
        product = omega2 * omega3_1[:, :21] * omega3_2[:, :21]
        integral = np.sum(product * self.volume_element[:, np.newaxis])

        return float(integral) / len(self.grid)

    def mass_eigenvalues(self) -> np.ndarray:
        """
        Extract fermion mass ratios from Yukawa tensor.

        The mass matrix M_ij ~ Y_ijk * v_k where v is a VEV.
        Eigenvalues give mass ratios.

        Returns:
            Mass eigenvalues (sorted)
        """
        Y = self.tensor

        # Contract with unit vector (simplified VEV direction)
        v = np.ones(self.n3) / np.sqrt(self.n3)
        M = np.einsum('ijk,k->ij', Y, v)

        # Singular values give mass scale
        _, s, _ = np.linalg.svd(M)

        return np.sort(s)[::-1]

    def flavor_structure(self) -> np.ndarray:
        """
        Analyze flavor structure from Yukawa.

        Returns mixing angles and CP phase.
        """
        masses = self.mass_eigenvalues()

        # Three generations
        if len(masses) >= 3:
            m1, m2, m3 = masses[:3]

            # Mass ratios
            r12 = m2 / m1 if m1 > 0 else 0
            r23 = m3 / m2 if m2 > 0 else 0

            return {
                'masses': masses[:3],
                'm2_m1': r12,
                'm3_m2': r23,
                'hierarchy': 'normal' if m3 > m2 > m1 else 'inverted'
            }

        return {'masses': masses}

    def ckm_like_matrix(self) -> np.ndarray:
        """
        Extract CKM-like mixing matrix.

        The mixing matrix V relates mass and flavor eigenstates:
        d_mass = V * d_flavor

        Returns:
            3x3 unitary mixing matrix
        """
        # Contract Yukawa to get mass matrices
        Y = self.tensor

        # Up-type and down-type mass matrices (simplified)
        v_u = np.zeros(self.n3)
        v_d = np.zeros(self.n3)
        v_u[0] = 1.0  # VEV directions
        v_d[1] = 1.0

        M_u = np.einsum('ijk,k->ij', Y, v_u)[:3, :3]
        M_d = np.einsum('ijk,k->ij', Y, v_d)[:3, :3]

        # Diagonalize
        _, V_u = np.linalg.eigh(M_u @ M_u.T)
        _, V_d = np.linalg.eigh(M_d @ M_d.T)

        # CKM = V_u^dag * V_d
        V_ckm = V_u.T @ V_d

        return V_ckm


def compute_yukawa(basis_2: np.ndarray, basis_3: np.ndarray,
                   grid: np.ndarray, metric: np.ndarray) -> YukawaTensor:
    """
    Factory function to compute Yukawa tensor.

    Args:
        basis_2: Harmonic 2-forms
        basis_3: Harmonic 3-forms
        grid: Integration points
        metric: Metric tensor at grid points

    Returns:
        YukawaTensor with computed couplings
    """
    # Compute volume element
    det_g = np.linalg.det(metric)
    volume_element = np.sqrt(np.abs(det_g))

    yukawa = YukawaTensor(
        basis_2=basis_2,
        basis_3=basis_3,
        grid=grid,
        volume_element=volume_element
    )

    return yukawa


def yukawa_from_g2_form(phi: np.ndarray, grid: np.ndarray) -> np.ndarray:
    """
    Compute Yukawa from G2 3-form directly.

    Y = integral phi ^ phi ^ phi (normalized)

    Args:
        phi: G2 3-form components at grid points
        grid: Integration points

    Returns:
        Yukawa coupling value
    """
    # Triple product phi ^ phi ^ phi
    # This is a 9-form, so zero on 7-manifold
    # The relevant quantity is phi ^ *phi

    return np.zeros(1)
