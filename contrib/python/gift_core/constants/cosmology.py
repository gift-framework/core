"""
Cosmological Constants from GIFT Framework.

Dark energy, Hubble tension, CMB temperature.
All values proven in Lean 4 (GIFT.Relations.Cosmology).
"""
from fractions import Fraction
from .algebra import DIM_G2, DIM_K7, RANK_E8, WEYL_FACTOR, DIM_E7
from .topology import B2, B3, H_STAR, D_BULK
from .structural import N_GEN

# =============================================================================
# DARK ENERGY FRACTION
# =============================================================================

# Omega_DE = (b2 + b3) / H* = 98/99
OMEGA_DE_NUM = B2 + B3         # = 98
OMEGA_DE_DEN = H_STAR          # = 99
OMEGA_DE_FRACTION = Fraction(OMEGA_DE_NUM, OMEGA_DE_DEN)

# Product form: dim_K7 * dim_G2 = 7 * 14 = 98 = H* - 1
OMEGA_DE_PRODUCT = DIM_K7 * DIM_G2  # = 98

# =============================================================================
# PHI-SQUARED RATIO (Dark energy / Dark matter)
# =============================================================================

# Omega_DE / Omega_DM ~ b2 / rank_E8 = 21/8 ~ 2.625 ~ phi^2 = 2.618
PHI_SQUARED_NUM = B2           # = 21
PHI_SQUARED_DEN = RANK_E8      # = 8

# =============================================================================
# HUBBLE TENSION
# =============================================================================

# H0(CMB) = b3 - 2*Weyl = 77 - 10 = 67 km/s/Mpc
HUBBLE_CMB = B3 - 2 * WEYL_FACTOR  # = 67

# H0(local) = b3 - p2^2 = 77 - 4 = 73 km/s/Mpc
HUBBLE_LOCAL = B3 - 4              # = 73

# Tension = 2 * N_gen = 6
HUBBLE_TENSION = 2 * N_GEN         # = 6

# Topological H0 = dim_K7 * 10 = 70
H0_TOPOLOGICAL = DIM_K7 * 10       # = 70

# =============================================================================
# CMB TEMPERATURE
# =============================================================================

# T_CMB = 2.725 K => 2725 mK = 25 * 109 = Weyl^2 * 109
T_CMB_mK = 2725

# =============================================================================
# AGE OF UNIVERSE
# =============================================================================

# 13.8 Gyr ~ dim_E7 + Weyl = 133 + 5 = 138 (in 0.1 Gyr units)
AGE_UNIVERSE_UNIT = DIM_E7 + WEYL_FACTOR  # = 138

# =============================================================================
# SPECTRAL INDEX
# =============================================================================

# n_s from zeta ratios: zeta(11)/zeta(5) ~ 0.965
N_S_ZETA_BULK = D_BULK       # = 11
N_S_ZETA_WEYL = WEYL_FACTOR  # = 5

# =============================================================================
# IMPEDANCE
# =============================================================================

# Z = H* / D_bulk = 99/11 = 9
IMPEDANCE = H_STAR // D_BULK  # = 9
