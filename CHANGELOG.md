# Changelog

All notable changes to GIFT Core will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.4.0] - 2025-12-05

### Added

- **Irrational Sector Relations** (4 new certified relations):
  - `alpha^-1 complete = 267489/1952` - Exact rational for fine structure constant inverse
  - `theta_13 degrees = 60/7` - Reactor mixing angle rational part
  - `phi bounds: (1.618, 1.619)` - Golden ratio certified interval
  - `m_mu/m_e bounds: (206, 208)` - Muon/electron mass ratio bounds from 27^phi

- **Lean 4 modules**:
  - `Lean/GIFT/Relations/IrrationalSector.lean` - theta_13, theta_23, alpha^-1 complete
  - `Lean/GIFT/Relations/GoldenRatio.lean` - phi equation, sqrt(5) bounds, 27^phi

- **Coq modules**:
  - `COQ/Relations/IrrationalSector.v` - Matching proofs
  - `COQ/Relations/GoldenRatio.v` - Matching proofs

- **Python constants** (in `gift_core.constants`):
  - `THETA_13_DIVISOR`, `THETA_13_DEGREES_NUM`, `THETA_13_DEGREES_DEN`
  - `THETA_13_DEGREES_SIMPLIFIED` - Fraction(60, 7)
  - `ALPHA_INV_TORSION_NUM`, `ALPHA_INV_TORSION_DEN`
  - `ALPHA_INV_COMPLETE_NUM`, `ALPHA_INV_COMPLETE_DEN`, `ALPHA_INV_COMPLETE`
  - `PHI_LOWER_BOUND`, `PHI_UPPER_BOUND`
  - `SQRT5_LOWER_BOUND`, `SQRT5_UPPER_BOUND`
  - `M_MU_M_E_LOWER`, `M_MU_M_E_UPPER`, `M_MU_M_E_BASE_CUBE`

### Changed

- Updated `GaugeSector.lean` and `GaugeSector.v` with alpha^-1 complete relation (#36)
- Updated `Certificate.lean` with `all_39_relations_certified` master theorem
- Updated `AllProven.v` with `all_39_relations_certified` master theorem
- Total certified relations: 35 -> 39

### Key Insight

The fine structure constant inverse `alpha^-1 = 267489/1952 ~ 137.033` is proven to be
an *exact rational*, not an approximation. This arises from:
- 128 = (dim(E8) + rank(E8))/2 (algebraic component)
- 9 = H*/D_bulk (bulk component)
- 65/1952 = det(g) * kappa_T (torsion correction)

## [1.3.0] - 2025-12-04

### Added

- **Yukawa Duality Relations** (10 new certified relations):
  - Structure A (topological): alpha^2 = {2, 3, 7}, sum=12, prod+1=43
  - Structure B (dynamical): alpha^2 = {2, 5, 6}, sum=13, prod+1=61
  - Duality gap: 61 - 43 = 18 = p2 * N_gen^2
  - Jordan connection: 61 - 34 = 27 = dim(J3(O))

- **Lean 4**: `Relations/YukawaDuality.lean`
- **Coq**: `Relations/YukawaDuality.v`

### Changed

- Total certified relations: 25 -> 35

## [1.2.0] - 2025-12-03

### Added

- **K7 Metric Pipeline**: Full G2 holonomy metric computation
  - `gift_core.geometry`: TCS manifold construction
  - `gift_core.g2`: G2 3-form and torsion constraints
  - `gift_core.harmonic`: Hodge Laplacian and Betti validation
  - `gift_core.physics`: Yukawa tensor extraction
  - `gift_core.verification`: Interval arithmetic certificates
  - `gift_core.pipeline`: End-to-end orchestration

### Changed

- Optional numpy dependency for K7 modules

## [1.1.0] - 2025-12-02

### Added

- **Topological Extension** (12 new certified relations):
  - Gauge sector: alpha_s structure, alpha^-1 base
  - Neutrino sector: gamma_GIFT, theta angles
  - Lepton sector: m_mu/m_e base, lambda_H^2
  - Cosmology: n_s indices, Omega_DE

### Changed

- Total certified relations: 13 -> 25

## [1.0.0] - 2025-12-01

### Added

- Initial release with 13 original certified relations
- Lean 4 formal proofs
- Coq formal proofs
- Python package `giftpy`
- Monte Carlo robustness testing
- Experimental comparison module
