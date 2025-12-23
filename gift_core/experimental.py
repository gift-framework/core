"""
Experimental data from PDG 2024 and NuFIT 5.3.

Contains measured values with uncertainties for comparison
with GIFT topological predictions.
"""
from dataclasses import dataclass
from typing import Tuple
from fractions import Fraction

__all__ = [
    'Measurement', 'Comparison', 'GIFT_COMPARISONS', 'summary_table',
    # Gauge bosons and electroweak
    'M_Z_EXP', 'M_W_EXP', 'M_H_EXP', 'SIN2_THETA_W_EXP',
    # Leptons
    'M_ELECTRON', 'M_MUON', 'M_TAU', 'M_TAU_M_E_EXP', 'Q_KOIDE_EXP',
    # Quarks
    'M_UP', 'M_DOWN', 'M_STRANGE', 'M_S_M_D_EXP', 'M_CHARM', 'M_BOTTOM', 'M_TOP',
    # Neutrinos
    'DELTA_CP_EXP',
    # CKM
    'V_UD', 'V_US', 'V_UB', 'V_CD', 'V_CS', 'V_CB', 'V_TD', 'V_TS', 'V_TB', 'J_CP_CKM',
    # Couplings
    'ALPHA_EM', 'ALPHA_S_MZ', 'G_FERMI',
]

# =============================================================================
# PDG 2024 VALUES
# Source: https://pdg.lbl.gov/
# =============================================================================


@dataclass(frozen=True)
class Measurement:
    """An experimental measurement with uncertainty."""
    value: float
    error_plus: float
    error_minus: float = 0.0  # Asymmetric errors; 0 means symmetric
    unit: str = ""
    source: str = "PDG 2024"

    @property
    def error(self) -> float:
        """Symmetric error (average if asymmetric)."""
        if self.error_minus == 0:
            return self.error_plus
        return (self.error_plus + abs(self.error_minus)) / 2

    @property
    def relative_error(self) -> float:
        """Relative uncertainty."""
        return self.error / abs(self.value) if self.value != 0 else float('inf')

    def range(self) -> Tuple[float, float]:
        """1-sigma range."""
        lower = self.value - (abs(self.error_minus) if self.error_minus else self.error_plus)
        upper = self.value + self.error_plus
        return (lower, upper)

    def contains(self, prediction: float, sigma: float = 1.0) -> bool:
        """Check if prediction is within sigma of measurement."""
        lower, upper = self.range()
        margin = self.error * (sigma - 1)
        return (lower - margin) <= prediction <= (upper + margin)


# -----------------------------------------------------------------------------
# ELECTROWEAK SECTOR
# -----------------------------------------------------------------------------

# Weinberg angle (MS-bar at M_Z)
SIN2_THETA_W_EXP = Measurement(
    value=0.23122,
    error_plus=0.00003,
    source="PDG 2024"
)

# Z boson mass
M_Z_EXP = Measurement(
    value=91.1876,
    error_plus=0.0021,
    unit="GeV",
    source="PDG 2024"
)

# W boson mass
M_W_EXP = Measurement(
    value=80.3692,
    error_plus=0.0133,
    unit="GeV",
    source="PDG 2024 (CDF 2022 average)"
)

# Higgs mass
M_H_EXP = Measurement(
    value=125.20,
    error_plus=0.11,
    unit="GeV",
    source="PDG 2024"
)

# -----------------------------------------------------------------------------
# LEPTON MASSES
# -----------------------------------------------------------------------------

M_ELECTRON = Measurement(
    value=0.51099895,
    error_plus=0.00000015,
    unit="MeV",
    source="PDG 2024"
)

M_MUON = Measurement(
    value=105.6583755,
    error_plus=0.0000023,
    unit="MeV",
    source="PDG 2024"
)

M_TAU = Measurement(
    value=1776.86,
    error_plus=0.12,
    unit="MeV",
    source="PDG 2024"
)

# Tau/electron mass ratio (for GIFT comparison)
M_TAU_M_E_EXP = Measurement(
    value=M_TAU.value / M_ELECTRON.value,  # ≈ 3477.23
    error_plus=0.24,  # Error propagated
    source="PDG 2024 derived"
)

# Koide parameter Q = (m_e + m_mu + m_tau) / (sqrt(m_e) + sqrt(m_mu) + sqrt(m_tau))^2
# Experimental value
Q_KOIDE_EXP = Measurement(
    value=0.666661,
    error_plus=0.000007,
    source="PDG 2024 derived"
)

# -----------------------------------------------------------------------------
# QUARK MASSES (MS-bar at 2 GeV)
# -----------------------------------------------------------------------------

M_UP = Measurement(
    value=2.16,
    error_plus=0.07,
    error_minus=-0.26,
    unit="MeV",
    source="PDG 2024"
)

M_DOWN = Measurement(
    value=4.70,
    error_plus=0.07,
    error_minus=-0.07,
    unit="MeV",
    source="PDG 2024"
)

M_STRANGE = Measurement(
    value=93.5,
    error_plus=0.8,
    error_minus=-0.8,
    unit="MeV",
    source="PDG 2024"
)

# Strange/down ratio (for GIFT comparison)
M_S_M_D_EXP = Measurement(
    value=M_STRANGE.value / M_DOWN.value,  # ≈ 19.89
    error_plus=0.4,
    source="PDG 2024 derived"
)

M_CHARM = Measurement(
    value=1.273,
    error_plus=0.004,
    unit="GeV",
    source="PDG 2024 (MS-bar at m_c)"
)

M_BOTTOM = Measurement(
    value=4.183,
    error_plus=0.007,
    unit="GeV",
    source="PDG 2024 (MS-bar at m_b)"
)

M_TOP = Measurement(
    value=172.57,
    error_plus=0.29,
    unit="GeV",
    source="PDG 2024"
)

# -----------------------------------------------------------------------------
# NUFIT 5.3 (2024) - NEUTRINO OSCILLATION PARAMETERS
# Source: http://www.nu-fit.org/
# Normal Ordering (NO) central values
# -----------------------------------------------------------------------------

# Mixing angles
THETA_12 = Measurement(
    value=33.41,
    error_plus=0.75,
    error_minus=-0.72,
    unit="degrees",
    source="NuFIT 5.3 (NO)"
)

THETA_23 = Measurement(
    value=42.2,
    error_plus=1.1,
    error_minus=-0.9,
    unit="degrees",
    source="NuFIT 5.3 (NO)"
)

THETA_13 = Measurement(
    value=8.58,
    error_plus=0.11,
    error_minus=-0.11,
    unit="degrees",
    source="NuFIT 5.3 (NO)"
)

# CP violation phase
DELTA_CP_EXP = Measurement(
    value=197.0,
    error_plus=42.0,
    error_minus=-25.0,
    unit="degrees",
    source="NuFIT 5.3 (NO)"
)

# Mass squared differences
DELTA_M21_SQ = Measurement(
    value=7.41e-5,
    error_plus=0.21e-5,
    error_minus=-0.20e-5,
    unit="eV^2",
    source="NuFIT 5.3"
)

DELTA_M31_SQ = Measurement(
    value=2.507e-3,
    error_plus=0.026e-3,
    error_minus=-0.027e-3,
    unit="eV^2",
    source="NuFIT 5.3 (NO)"
)

# -----------------------------------------------------------------------------
# CKM MATRIX ELEMENTS
# -----------------------------------------------------------------------------

V_UD = Measurement(value=0.97370, error_plus=0.00014, source="PDG 2024")
V_US = Measurement(value=0.2245, error_plus=0.0008, source="PDG 2024")
V_UB = Measurement(value=0.00382, error_plus=0.00020, source="PDG 2024")
V_CD = Measurement(value=0.221, error_plus=0.004, source="PDG 2024")
V_CS = Measurement(value=0.987, error_plus=0.011, source="PDG 2024")
V_CB = Measurement(value=0.0410, error_plus=0.0014, source="PDG 2024")
V_TD = Measurement(value=0.0080, error_plus=0.0003, source="PDG 2024")
V_TS = Measurement(value=0.0388, error_plus=0.0011, source="PDG 2024")
V_TB = Measurement(value=1.013, error_plus=0.030, source="PDG 2024")

# Jarlskog invariant (CP violation)
J_CP_CKM = Measurement(
    value=3.08e-5,
    error_plus=0.15e-5,
    source="PDG 2024"
)

# -----------------------------------------------------------------------------
# COUPLING CONSTANTS
# -----------------------------------------------------------------------------

# Fine structure constant
ALPHA_EM = Measurement(
    value=1 / 137.035999177,
    error_plus=2.1e-12,
    source="PDG 2024"
)

# Strong coupling at M_Z
ALPHA_S_MZ = Measurement(
    value=0.1180,
    error_plus=0.0009,
    source="PDG 2024"
)

# Fermi constant
G_FERMI = Measurement(
    value=1.1663788e-5,
    error_plus=0.0000006e-5,
    unit="GeV^-2",
    source="PDG 2024"
)


# =============================================================================
# GIFT PREDICTIONS VS EXPERIMENT COMPARISON
# =============================================================================

@dataclass
class Comparison:
    """Compare GIFT prediction with experimental value."""
    name: str
    symbol: str
    prediction: float
    measurement: Measurement
    gift_formula: str

    @property
    def deviation(self) -> float:
        """(pred - exp) / sigma."""
        return (self.prediction - self.measurement.value) / self.measurement.error

    @property
    def percent_diff(self) -> float:
        """Percent difference from experiment."""
        return 100 * (self.prediction - self.measurement.value) / self.measurement.value

    @property
    def agrees(self) -> bool:
        """Within 3 sigma?"""
        return abs(self.deviation) < 3.0


# Pre-built comparisons with GIFT predictions
GIFT_COMPARISONS = [
    Comparison(
        name="Weinberg angle",
        symbol="sin²θ_W",
        prediction=float(Fraction(3, 13)),  # 0.230769...
        measurement=SIN2_THETA_W_EXP,
        gift_formula="b₂/(b₃ + dim(G₂)) = 21/91 = 3/13"
    ),
    Comparison(
        name="CP violation phase",
        symbol="δ_CP",
        prediction=197.0,
        measurement=DELTA_CP_EXP,
        gift_formula="7×dim(G₂) + H* = 7×14 + 99 = 197°"
    ),
    Comparison(
        name="Tau/electron mass ratio",
        symbol="m_τ/m_e",
        prediction=3477.0,
        measurement=M_TAU_M_E_EXP,
        gift_formula="7 + 10×248 + 10×99 = 3477"
    ),
    Comparison(
        name="Strange/down mass ratio",
        symbol="m_s/m_d",
        prediction=20.0,
        measurement=M_S_M_D_EXP,
        gift_formula="4×5 = 20"
    ),
    Comparison(
        name="Koide parameter",
        symbol="Q_Koide",
        prediction=float(Fraction(2, 3)),  # 0.666666...
        measurement=Q_KOIDE_EXP,
        gift_formula="dim(G₂)/b₂ = 14/21 = 2/3"
    ),
]


def summary_table() -> str:
    """Generate comparison summary table."""
    lines = [
        "GIFT Predictions vs Experiment",
        "=" * 70,
        f"{'Observable':<25} {'GIFT':<12} {'Exp':<12} {'σ dev':<8} {'Status'}",
        "-" * 70,
    ]
    for c in GIFT_COMPARISONS:
        status = "✓" if c.agrees else "✗"
        lines.append(
            f"{c.name:<25} {c.prediction:<12.6f} "
            f"{c.measurement.value:<12.6f} {c.deviation:>+7.2f}σ  {status}"
        )
    lines.append("=" * 70)
    return "\n".join(lines)
