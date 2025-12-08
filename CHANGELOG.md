# Changelog

All notable changes to GIFT Core will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.7.0] - 2025-12-08

### Added

- **Extended Decomposition Relations** (4 new certified relations):
  - `tau_num base13 = [1,7,7,1]` - Hierarchy parameter numerator in base 13
  - `n_observables = 39` - Observable count from N_gen * ALPHA_SUM_B
  - `E6_dual = 78` - E6 dimension as 2 * n_observables (visible + hidden)
  - `H0_topological = 70` - Hubble constant from dim(K7) * 10

- **Lean 4 modules**:
  - Extended `Lean/GIFT/Relations/BaseDecomposition.lean` with relations 51-54

- **Coq modules**:
  - Extended `COQ/Relations/BaseDecomposition.v` with relations 51-54

- **Python constants** (in `gift_core.constants`):
  - `TAU_NUM_VALUE`, `TAU_DEN_VALUE`, `TAU_NUM_BASE13`
  - `to_base_13()` - Helper function for base conversion
  - `N_OBSERVABLES`, `E6_DUAL_OBSERVABLES`, `H0_TOPOLOGICAL`

### Changed

- Updated `Certificate.lean` with `all_54_relations_certified` master theorem
- Updated `AllProven.v` with `all_54_relations_certified` master theorem
- Total certified relations: 50 -> 54

### Key Insight

The hierarchy parameter tau = 3472/891 has a palindromic structure in base 13:
tau_num = 3472 = 1*13^3 + 7*13^2 + 7*13 + 1 = [1, 7, 7, 1]_13

The central digits (7, 7) encode dim(K7) = 7, while the outer digits (1, 1)
provide the symmetric boundary. This connects the mass hierarchy parameter
directly to the K7 manifold dimension.

The E6 dimension 78 = 2 * 39 = 2 * (3 * 13) encodes visible/hidden duality,
where 39 = N_gen * ALPHA_SUM_B represents the number of GIFT observables.

## [1.6.0] - 2025-12-07

### Added

- **Base Decomposition Relations** (6 new certified relations):
  - `kappa_T^-1 = dim(F4) + N_gen^2 = 61` - Torsion inverse from F4 and generations
  - `b2 = ALPHA_SUM_B + rank(E8) = 21` - Second Betti number decomposition
  - `b3 = ALPHA_SUM_B * Weyl + 12 = 77` - Third Betti number decomposition
  - `H* = ALPHA_SUM_B * dim(K7) + rank(E8) = 99` - Effective DOF decomposition
  - `quotient_sum = 1 + 5 + 7 = 13` - Gauge-holonomy-manifold sum
  - `omega_DE_num = dim(K7) * dim(G2) = 98` - Dark energy numerator product

- **Lean 4 modules**:
  - `Lean/GIFT/Relations/BaseDecomposition.lean` - All 6 decomposition relations

- **Coq modules**:
  - `COQ/Relations/BaseDecomposition.v` - Matching proofs

- **Python constants** (in `gift_core.constants`):
  - `KAPPA_T_INV_FROM_F4`, `B2_BASE_DECOMPOSITION`
  - `B3_INTERMEDIATE`, `B3_BASE_DECOMPOSITION`
  - `H_STAR_INTERMEDIATE`, `H_STAR_BASE_DECOMPOSITION`
  - `QUOTIENT_SUM`, `OMEGA_DE_PRODUCT`

### Changed

- Updated `Certificate.lean` with `all_50_relations_certified` master theorem
- Updated `AllProven.v` with `all_50_relations_certified` master theorem
- Total certified relations: 44 -> 50

### Key Insight

The Structure B sum (2 + 5 + 6 = 13 = ALPHA_SUM_B = rank(E8) + Weyl) provides a
consistent base for decomposing all primary GIFT topological constants:
- b2 = 13 + 8 (base + rank)
- b3 = 13 * 5 + 12 (base * Weyl + gauge_dim)
- H* = 13 * 7 + 8 (base * manifold_dim + rank)

The quotient sum 1 + 5 + 7 = 13 reflects gauge (U(1)), holonomy (Weyl), and
manifold (K7) contributions to the decomposition base.

## [1.5.0] - 2025-12-07

### Added

- **Exceptional Groups Relations** (5 new certified relations):
  - `alpha_s^2 = 1/72` - Strong coupling squared is exactly rational
  - `dim(F4) = 52` - F4 dimension from Structure B: p2^2 * sum(alpha^2_B)
  - `delta_penta = 25` - Pentagonal structure from F4/Jordan gap: dim(F4) - dim(J3O) = Weyl^2
  - `J3(O)_0 = 26` - Traceless Jordan algebra: dim(E6) - dim(F4) = dim(J3O) - 1
  - `|W(E8)| = 696729600` - E8 Weyl group topological factorization

- **Lean 4 modules**:
  - `Lean/GIFT/Relations/ExceptionalGroups.lean` - F4, E6, E8 connections
  - New constants in `Lean/GIFT/Algebra.lean`: dim_F4, dim_E6, weyl_E8_order, dim_J3O_traceless

- **Coq modules**:
  - `COQ/Relations/ExceptionalGroups.v` - Matching proofs

- **Python constants** (in `gift_core.constants`):
  - `DIM_F4`, `DIM_E6`, `DIM_J3O_TRACELESS`, `WEYL_E8_ORDER`
  - `ALPHA_SQ_B_SUM`, `ALPHA_S_SQUARED`, `ALPHA_S_SQUARED_NUM`, `ALPHA_S_SQUARED_DEN`
  - `DIM_F4_FROM_STRUCTURE_B`, `DELTA_PENTA`, `JORDAN_TRACELESS`
  - `WEYL_E8_FORMULA`, `EXCEPTIONAL_CHAIN`

### Changed

- Updated `Certificate.lean` with `all_44_relations_certified` master theorem
- Updated `AllProven.v` with `all_44_relations_certified` master theorem
- Total certified relations: 39 -> 44

### Key Insight

The Weyl group of E8 has order |W(E8)| = 696,729,600 = 2^14 * 3^5 * 5^2 * 7.
Remarkably, this factorizes as:
- 2^14 = p2^dim(G2) (Pontryagin class to power of G2 dimension)
- 3^5 = N_gen^Weyl (generations to power of Weyl factor)
- 5^2 = Weyl^p2 (Weyl factor squared)
- 7 = dim(K7) (dimension of internal manifold)

This encodes the complete K7 topological structure in a single group-theoretic invariant.

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
