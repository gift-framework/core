# Changelog

All notable changes to GIFT Core will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [3.3.24] - 2026-02-23

### Summary

**Ambrose-Singer holonomy diagnostics, axiom classification (87/87), Hodge star hierarchy.** New `AmbroseSinger.lean` module formalizing the gap between torsion-free G₂ structures and G₂ holonomy: so(7) = g₂ + g₂⊥ decomposition, holonomy rank gap (21 → 14), AS constraints per point (147 = 7 × 21). All 87 axioms across 17 files tagged with category labels (A-F). Hodge star file hierarchy documented. Zero new axioms, full build passes (2652 jobs).

### Added

- **Foundations/AmbroseSinger.lean** (~250 lines, 0 axioms) — Holonomy diagnostics:
  - `so7_g2_decomposition`: 21 = 14 + 7 (so(7) = g₂ ⊕ g₂⊥)
  - `dim_g2_complement_eq_dim_K7`: dim(g₂⊥) = dim(K₇) = 7
  - `b2_holonomy_manifold_sum`: b₂ = dim(g₂) + dim(K₇)
  - `holonomy_rank_gap`: current − target = 21 − 14 = 7
  - `as_constraints_decomposition`: 147 = dim(K₇) × b₂ constraints per point
  - `ambrose_singer_certificate`: Master certificate (10 conjuncts, all proven)

- **Axiom category tags** on all 87 axioms across 17 Lean files:
  - Category A (Definitions): ~5 axioms
  - Category B (Standard results): ~15 axioms
  - Category C (Geometric structure): ~25 axioms
  - Category D (Literature axioms): ~8 axioms
  - Category E (GIFT claims): ~12 axioms
  - Category F (Numerically verified): ~22 axioms

### Changed

- **Certificate/Foundations.lean** — Added 7 abbrevs for AmbroseSinger + 2 new conjuncts in `def statement`
- **Foundations.lean** — Added import and export block for AmbroseSinger (20+ symbols)
- **CLAUDE.md** — Added Hodge star file hierarchy, Ambrose-Singer module docs, axiom classification system, updated version
- **docs/USAGE.md** — Added v3.3.24 section (this release)
- **17 Lean files** — Axiom category tags added to docstrings (HarmonicForms, HodgeTheory, Zeta/*, Spectral/*, RefinedSpectralBounds, SelbergBridge)

---

## [3.3.23] - 2026-02-22

### Summary

**Certificate modularization: monolithic → domain-organized.** Restructures the 2281-line monolithic `Certificate.lean` (55 theorems, 233 abbrevs, 9 stacked master theorems) into four focused files organized by mathematical domain. Removes 16 versioned certificates and 9 stacked master theorems. The new structure uses `def statement : Prop` / `theorem certified : statement` pattern for composability. One master certificate combines all three pillars: `Foundations.statement ∧ Predictions.statement ∧ Spectral.statement`. Backward-compatible `Certificate.lean` wrapper preserves legacy aliases. Zero proof changes, full build passes (2651 jobs).

### Added

- **Certificate/Foundations.lean** (~440 lines) — E₈ root system, G₂ cross product, octonion bridge, K₇ Betti numbers, exterior algebra, Joyce existence, Sobolev embedding, conformal rigidity, Poincare duality, G₂ metric properties, TCS piecewise structure:
  - 80+ abbrevs creating dependency graph edges
  - `def statement : Prop` with 19 conjuncts
  - `theorem certified : statement` proven via `refine` + `native_decide`

- **Certificate/Predictions.lean** (~460 lines) — All 33+ published dimensionless predictions (R1-R20), V5.0 observables (~50 rational fractions), Fano selection principle, tau bounds, hierarchy, SO(16) decomposition, Landauer dark energy:
  - 30+ abbrevs for Relations submodules
  - `def statement : Prop` with 48 conjuncts
  - 7 additional theorems: `observables_certified`, `the_42_universality`, `fano_selection_certified`, `tau_bounds_certified`, `hierarchy_certified`, `SO16_certified`, `landauer_certified`

- **Certificate/Spectral.lean** (~380 lines) — Mass gap ratio 14/99, TCS manifold structure, TCS spectral bounds, selection principle, refined bounds, literature axioms, spectral scaling, Connes bridge:
  - 60+ abbrevs for Spectral submodules
  - `def statement : Prop` with 27 conjuncts
  - `theorem certified : statement` proven via `repeat (first | constructor | native_decide | rfl | norm_num)`

- **Certificate/Core.lean** (~40 lines) — Single master certificate:
  - `theorem gift_master_certificate : Foundations.statement ∧ Predictions.statement ∧ Spectral.statement`

### Changed

- **Certificate.lean** — Replaced 2281-line monolithic file with ~35-line backward-compat wrapper
- **GIFT.lean** — Updated import from `GIFT.Certificate` to `GIFT.Certificate.Core`
- **CLAUDE.md** — Updated project structure, certificate workflow documentation
- **docs/USAGE.md** — Added v3.3.23 certificate modularization section

### Removed

- 9 stacked master theorems (`all_13_relations_certified` → `all_75_relations_certified`)
- 16 versioned certificates (`gift_v2_*`, `gift_v3_*`, `gift_v32_*`, etc.)
- ~1400 lines of redundant code

---

## [3.3.22] - 2026-02-22

### Summary

**Poincare duality doubles the GIFT spectrum.** Consolidates spectral-topological arithmetic identities. Key discovery: H* = 1 + 2 * dim_K7^2. Adds ~40 new theorems covering the full Betti sequence, holonomy embedding chain G2 < SO(7) < GL(7), G2 torsion decomposition, SU(3) branching rule, and the Betti-torsion bridge. Zero axioms.

### Added

- **Foundations/PoincareDuality.lean** — 41 theorems, 4 defs, master certificate (12 conjuncts)

---

## [3.3.21] - 2026-02-22

### Summary

**Spectral scaling on the TCS neck.** Formalizes the rational skeleton of Neumann eigenvalue scaling on the TCS neck interval [0,L]. Adds ~35 new theorems including eigenvalue sum identities, sub-gap mode counting (3 = N_gen), the Pell equation 99² − 50 × 14² = 1. Zero axioms.

### Added

- **Foundations/SpectralScaling.lean** — 35 theorems, master certificate (12 conjuncts)

---

## [3.3.20] - 2026-02-22

### Summary

**G₂ metric formalization: three new Lean modules.** ~90 new theorems across three modules covering metric properties, TCS piecewise structure, and conformal rigidity. Zero axioms.

### Added

- **Relations/G2MetricProperties.lean** — 25 theorems (non-flatness, spectral degeneracy, SPD₇, det(g) triple derivation, κ_T decomposition)
- **Foundations/TCSPiecewiseMetric.lean** — 30 theorems (building block asymmetry, Fano automorphism, Kovalev involution)
- **Foundations/ConformalRigidity.lean** — 37 theorems (G₂ irrep decomposition, conformal rigidity, moduli gap)

---

## Earlier Releases (condensed)

### v3.3.19 (2026-02-13) — Spectral axiom cleanup
Removed 8 ad-hoc Category E axioms claiming specific spectral gap values. Spectral gap now treated as open research question.

### v3.3.18 (2026-02-10) — Connes Bridge + Adaptive Cutoff
Two new modules: `Spectral/ConnesBridge.lean` (Weil positivity ↔ GIFT, 19-conjunct certificate) and `MollifiedSum/AdaptiveGIFT.lean` (θ(T) = 10/7 − (14/3)/log(T), 12-conjunct certificate).

### v3.3.17 (2026-02-08) — Physical Spectral Gap + Selberg Bridge
Axiom-free `PhysicalSpectralGap.lean` (ev₁ = 13/99 from Berger classification) and `SelbergBridge.lean` (trace formula connecting MollifiedSum to Spectral). Two blueprint chapters.

### v3.3.16 (2026-02-08) — Mollified Dirichlet Polynomial
Constructive (zero axioms) `MollifiedSum/` module: cosine-squared kernel, S_w(T) as Finset.sum, adaptive cutoff. Blueprint chapter with full Lean ↔ LaTeX linking.

### v3.3.15 (2026-01-29) — Axiom Classification System
All spectral module axioms classified (A-F) with academic citations. New `PiBounds.lean` for π > 3, π < 4, π < √10.

### v3.3.14 (2026-01-28) — TCS Selection Principle + Refined Spectral Bounds
`SelectionPrinciple.lean` (κ = π²/14, building blocks, Mayer-Vietoris) and `RefinedSpectralBounds.lean` (H7 cross-section gap). 31 new relations.

### v3.3.13 (2026-01-26) — Literature Axioms
`LiteratureAxioms.lean` integrating Langlais 2024 (spectral density) and CGN 2024 (no small eigenvalues). 23 new relations.

### v3.3.12 (2026-01-26) — TCS Spectral Bounds Model Theorem
`NeckGeometry.lean` (TCS structure, H1-H6) and `TCSBounds.lean` (λ₁ ~ 1/L²). Lean toolchain updated to v4.27.0.

### v3.3.11 (2026-01-24) — Monster Dimension via Coxeter Numbers
`MonsterCoxeter.lean`: 196883 = (b₃−h(G₂))×(b₃−h(E₇))×(b₃−h(E₈)) = 71×59×47. j-invariant ratio observations. 18 new relations.

### v3.3.10 (2026-01-24) — GIFT-Zeta Correspondences + Monster-Zeta Moonshine
`Zeta/` module (γ₁~14, γ₂~21, γ₂₀~77, γ₁₀₇~248), `Supersingular.lean` (15 primes), `MonsterZeta.lean`. 35+ new relations.

### v3.3.9 (2026-01-24) — Complete Spectral Theory Module
Full 4-phase formalization: `SpectralTheory`, `G2Manifold`, `UniversalLaw`, `CheegerInequality`, `YangMills`. 25+ new relations.

### v3.3.8 (2026-01-19) — Yang-Mills Mass Gap Module
`MassGapRatio.lean`: 14/99 algebraic, PINN verification (0.57% deviation), physical prediction Δ ≈ 28.28 MeV. 11 new relations.

### v3.3.7 (2026-01-16) — Tier 1 Complete (all numerical axioms proven)
Final rpow proofs: 27^1.618 > 206, 27^1.6185 < 209. Numerical bounds: 0 axioms remaining.

### v3.3.5-v3.3.6 (2026-01-15) — Numerical Bounds via Taylor Series
Taylor series proofs for log(φ), log(5), log(10), φ⁻⁵⁴, cohomological suppression. Axiom count: 7 → 0.

### v3.3.4 (2026-01-15) — Axiom-Free Hodge Star
`HodgeStarCompute.lean`: explicit Levi-Civita signs, ψ = ⋆φ **PROVEN**. Geometry module: zero axioms.

### v3.3.3 (2026-01-14) — DG-Ready Geometry Module
`Geometry/` with exterior algebra, differential forms (d²=0), Hodge star (⋆⋆=+1), TorsionFree predicate.

### v3.3.2 (2026-01-14) — G2 Forms Bridge + Analytical Foundations
Cross product ↔ G2 forms connection. Sobolev embedding, elliptic bootstrap, Joyce PINN verification (20x margin).

### v3.3.1 (2026-01-14) — G2 Forms Infrastructure
`G2Forms/` module: GradedDiffForms, exterior derivative, Hodge star, TorsionFree predicate. Zero axioms.

### v3.3.0 (2026-01-14) — chi(K7) Terminology Fix
χ(K7) = 0 (not 42). Value 42 = 2×b₂ renamed to `two_b2` (structural invariant).

---

### v3.2.15 (2026-01-13) — Octonion Bridge
OctonionBridge.lean connecting R8 (E8Lattice) and R7 (G2CrossProduct) via O = R + Im(O).

### v3.2.14 (2026-01-13) — Fano Selection Principle
FanoSelectionPrinciple, OverDetermination (28 expressions), SectorClassification, m_W/m_Z = 37/42 (0.06% deviation).

### v3.2.13 (2026-01-11) — Blueprint Consolidation
50+ observables, 0.24% mean deviation. Dependency graph streamlined (−14 nodes).

### v3.2.12 (2026-01-11) — Extended Observables
22+ physical observables: PMNS, CKM, quark masses, cosmology. The 42 universality (m_b/m_t and Ω_DM/Ω_b).

### v3.2.11 (2026-01-10) — PINN Validation
Joyce PINN: 220000× safety margin. 7/7 numerical axioms verified via mpmath (100 digits).

### v3.2.10 (2026-01-10) — Tau Derivation + Power Bounds
τ = dim(E₈×E₈) × b₂ / (dim(J₃(O)) × H*). Formal bounds: 230 < τ⁴ < 231, 898 < τ⁵ < 899.

### v3.2.0 (2026-01-06) — TCS Building Blocks
Both Betti numbers derived from M₁ (Quintic) + M₂ (CI): b₂ = 11+10 = 21, b₃ = 40+37 = 77. Structural identities (PSL(2,7) = 168).

---

### v3.1.x (2025-12-15 to 2025-12-30) — Mathematical Foundations
- **3.1.12**: E8_basis_generates proven (axiom → theorem)
- **3.1.11**: Blueprint dependency graph completion, E8 basis explicit definition
- **3.1.10**: E8 lattice closure axioms → theorems (45 → 42 axioms)
- **3.1.9**: Numerical bounds axiom resolution (all properly documented)
- **3.1.8**: Axiom reduction (52 → 44, connecting RootSystems + G2CrossProduct)
- **3.1.7**: Blueprint dependency graph consolidation (~100 uses tags)
- **3.1.6**: Constant deduplication (def → abbrev to canonical sources)
- **3.1.5**: Dimensional hierarchy module (M_EW/M_Pl from topology)
- **3.1.4**: Analytical G₂ metric discovery (g = (65/32)^{1/7} × I₇)
- **3.1.3**: Lagrange identity for 7D cross product proven
- **3.1.2**: Lagrange identity infrastructure (psi, epsilon contraction)
- **3.1.1**: 9 helper axioms → theorems, Weyl reflection proven
- **3.1.0**: Consolidation (RootSystems, E8Lattice, G2CrossProduct, RationalConstants, GraphTheory, GoldenRatio, Algebraic chain, Core module). 175+ relations.

---

## [3.0.0] - 2025-12-09

Joyce existence theorem, Sobolev spaces, differential forms, interval arithmetic, Python analysis module.

## [2.0.0] - 2025-12-09

Sequence embeddings (Fibonacci, Lucas), Prime Atlas (100% < 200), Monster group, McKay correspondence. 75 → 165+ relations.

## [1.0.0] - 2025-12-01

Initial release: 13 certified relations, Lean 4 + Coq proofs, Python package `giftpy`.
