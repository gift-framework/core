"""
Fermion mass spectrum from G2 compactification.

The mass spectrum is determined by:
1. Yukawa couplings (from harmonic forms)
2. VEV structure (from moduli stabilization)
3. Topological factors

GIFT predictions:
- m_tau/m_e = 3477
- m_s/m_d = 20
- m_mu/m_e ~ 27 (J3(O) dimension)
"""

from dataclasses import dataclass
from typing import Dict, List, Optional
from fractions import Fraction
import numpy as np


# GIFT mass predictions
GIFT_MASS_RATIOS = {
    'm_tau_m_e': 3477,      # tau/electron
    'm_s_m_d': 20,          # strange/down
    'm_mu_m_e_base': 27,    # mu/electron base (dim J3O)
}


@dataclass
class MassSpectrum:
    """
    Fermion mass spectrum from G2 geometry.

    Attributes:
        yukawa: Yukawa tensor
        vevs: Vacuum expectation values
        masses: Computed mass eigenvalues
    """

    yukawa_tensor: np.ndarray  # Y_ijk
    vev_direction: np.ndarray  # v_k
    n_generations: int = 3

    _masses: Optional[Dict] = None

    def compute_masses(self) -> Dict[str, np.ndarray]:
        """
        Compute fermion masses from Yukawa.

        M_ij = Y_ijk * v_k

        Returns:
            Dictionary of mass matrices by sector
        """
        Y = self.yukawa_tensor
        v = self.vev_direction

        # Mass matrix
        M = np.einsum('ijk,k->ij', Y, v)

        # Diagonalize
        eigenvalues = np.linalg.svd(M, compute_uv=False)

        # Group by generation
        n = self.n_generations
        self._masses = {
            'charged_leptons': eigenvalues[:n],
            'down_quarks': eigenvalues[n:2*n] if len(eigenvalues) > n else eigenvalues[:n],
            'up_quarks': eigenvalues[2*n:3*n] if len(eigenvalues) > 2*n else eigenvalues[:n],
        }

        return self._masses

    @property
    def mass_ratios(self) -> Dict[str, float]:
        """
        Compute mass ratios.

        Returns:
            Dictionary of mass ratios
        """
        if self._masses is None:
            self.compute_masses()

        ratios = {}

        # Charged lepton ratios
        leptons = self._masses['charged_leptons']
        if len(leptons) >= 3:
            m_e, m_mu, m_tau = sorted(leptons)[:3]
            if m_e > 0:
                ratios['m_mu_m_e'] = m_mu / m_e
                ratios['m_tau_m_e'] = m_tau / m_e
            if m_mu > 0:
                ratios['m_tau_m_mu'] = m_tau / m_mu

        # Quark ratios
        down = self._masses['down_quarks']
        if len(down) >= 2:
            m_d, m_s = sorted(down)[:2]
            if m_d > 0:
                ratios['m_s_m_d'] = m_s / m_d

        return ratios

    def validate_gift_predictions(self, tol: float = 0.1) -> Dict[str, bool]:
        """
        Validate computed masses against GIFT predictions.

        Args:
            tol: Relative tolerance

        Returns:
            Validation results
        """
        ratios = self.mass_ratios

        results = {}

        if 'm_tau_m_e' in ratios:
            expected = GIFT_MASS_RATIOS['m_tau_m_e']
            actual = ratios['m_tau_m_e']
            results['m_tau_m_e'] = {
                'computed': actual,
                'expected': expected,
                'valid': abs(actual - expected) / expected < tol
            }

        if 'm_s_m_d' in ratios:
            expected = GIFT_MASS_RATIOS['m_s_m_d']
            actual = ratios['m_s_m_d']
            results['m_s_m_d'] = {
                'computed': actual,
                'expected': expected,
                'valid': abs(actual - expected) / expected < tol
            }

        return results


def compute_masses(yukawa: 'YukawaTensor') -> MassSpectrum:
    """
    Factory function to compute mass spectrum.

    Args:
        yukawa: YukawaTensor object

    Returns:
        MassSpectrum with computed masses
    """
    # Default VEV direction (electroweak scale)
    n = yukawa.n3
    vev = np.zeros(n)
    vev[0] = 1.0  # Single VEV direction

    spectrum = MassSpectrum(
        yukawa_tensor=yukawa.tensor,
        vev_direction=vev
    )

    return spectrum


def gift_mass_formulas() -> Dict:
    """
    GIFT mass formulas from topology.

    Returns:
        Dictionary with mass ratio formulas
    """
    return {
        'm_tau_m_e': {
            'value': 3477,
            'formula': 'dim(K7) + 10*dim(E8) + 10*H* = 7 + 2480 + 990',
            'components': {
                'dim_K7': 7,
                '10_dim_E8': 10 * 248,
                '10_H_star': 10 * 99
            }
        },
        'm_s_m_d': {
            'value': 20,
            'formula': 'p2^2 * Weyl = 4 * 5',
            'components': {
                'p2_sq': 4,
                'weyl': 5
            }
        },
        'm_mu_m_e_base': {
            'value': 27,
            'formula': 'dim(J3(O))',
            'note': 'Base value; full ratio includes corrections'
        },
        'q_koide': {
            'value': Fraction(2, 3),
            'formula': 'dim(G2) / b2 = 14/21 = 2/3',
            'note': 'Koide parameter for charged leptons'
        }
    }


def koide_parameter(m1: float, m2: float, m3: float) -> float:
    """
    Compute Koide parameter Q for three masses.

    Q = (m1 + m2 + m3) / (sqrt(m1) + sqrt(m2) + sqrt(m3))^2

    For charged leptons, Q ~ 2/3.

    Args:
        m1, m2, m3: Three masses

    Returns:
        Koide parameter
    """
    numerator = m1 + m2 + m3
    denominator = (np.sqrt(m1) + np.sqrt(m2) + np.sqrt(m3)) ** 2

    if denominator == 0:
        return 0.0

    return numerator / denominator
