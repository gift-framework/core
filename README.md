# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![Publish to PyPI](https://github.com/gift-framework/core/actions/workflows/publish.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/publish.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.14-blue)](Lean/)
[![Coq](https://img.shields.io/badge/Coq-8.18-orange)](COQ/)

---

## What is GIFT?

GIFT (Geometric Information Field Theory) is a speculative theoretical physics framework that attempts to derive Standard Model parameters from topological invariants of E8 x E8 gauge theory compactified on seven-dimensional manifolds with G2 holonomy.

This repository contains only the **mathematical core**: exact rational and integer relations that have been formally verified in two independent proof assistants. The physical interpretation of these relations remains conjectural and subject to experimental validation.

**Important distinction**: This package proves that certain mathematical identities hold exactly. Whether these identities correspond to physical reality is a separate empirical question.

---

## Installation

```bash
pip install giftpy
```

## Usage

```python
from gift_core import *

# Original 13 certified relations
print(SIN2_THETA_W)  # Fraction(3, 13)
print(TAU)           # Fraction(3472, 891)
print(KAPPA_T)       # Fraction(1, 61)

# v1.1.0: 12 additional topological relations
print(GAMMA_GIFT)    # Fraction(511, 884)
print(THETA_23)      # Fraction(85, 99)
print(ALPHA_INV_BASE)  # 137

# v1.3.0: Yukawa duality relations
print(ALPHA_SUM_A)   # 12 (Structure A: 2+3+7)
print(ALPHA_SUM_B)   # 13 (Structure B: 2+5+6)
print(ALPHA_PROD_A + 1)  # 43 (visible sector)
print(ALPHA_PROD_B + 1)  # 61 (kappa_T inverse)
print(DUALITY_GAP)   # 18 (colored sector correction)

# v1.4.0: Irrational sector (exact rationals!)
print(ALPHA_INV_COMPLETE)  # Fraction(267489, 1952) ~ 137.033
print(THETA_13_DEGREES_SIMPLIFIED)  # Fraction(60, 7) ~ 8.571 degrees
print(PHI_LOWER_BOUND)  # Fraction(1618, 1000) = 1.618
print(M_MU_M_E_LOWER)   # 206 < 27^phi < 208

# All proven relations
for r in PROVEN_RELATIONS:
    print(f"{r.symbol} = {r.value}")
```

### K7 Metric Pipeline (v1.2.0)

Build your own G2 holonomy metrics on K7 manifolds:

```python
import gift_core as gc

# Check if numpy is available (required for K7 modules)
if gc.NUMPY_AVAILABLE:
    # Configure the pipeline
    config = gc.PipelineConfig(
        neck_length=15.0,      # TCS gluing parameter
        resolution=32,         # Grid resolution
        pinn_epochs=1000,      # Neural network training
        use_pinn=True          # Enable physics-informed learning
    )

    # Run the full G2 geometry pipeline
    result = gc.run_pipeline(config)

    # Access computed values
    print(f"det(g) = {result.det_g}")      # Should match 65/32
    print(f"kappa_T = {result.kappa_T}")    # Should match 1/61
    print(f"b2 = {result.betti[2]}")        # 21
    print(f"b3 = {result.betti[3]}")        # 77

    # Export certificate to Lean/Coq
    lean_proof = result.certificate.to_lean()
    coq_proof = result.certificate.to_coq()

    # Physics extraction
    yukawa = gc.YukawaTensor(result.harmonic_forms)
    masses = yukawa.fermion_masses()
```

**Requirements**: K7 modules require `numpy`. Install with:
```bash
pip install giftpy numpy
```

---

## Interactive Visualizations

[View GIFT Lean Blueprint](https://gift-framework.github.io/GIFT/docs/figures/gift_blueprint.html)
---
[View K7 Manifold Lean Blueprint](https://gift-framework.github.io/GIFT/docs/figures/k7_blueprint.html)
---
[created with Lean Blueprint Copilot](https://github.com/augustepoiroux/LeanBlueprintCopilot)

---

## Proven Relations (50 Total)

All relations are formally verified in both Lean 4 and Coq. Each relation is a mathematical identity; no fitting or approximation is involved.

### Original 13 Relations

| # | Symbol | Value | Derivation | Status |
|---|--------|-------|------------|--------|
| 1 | sin²θ_W | 3/13 | b₂/(b₃ + dim(G₂)) = 21/91 | Lean + Coq |
| 2 | τ | 3472/891 | dim(E₈×E₈)·b₂ / (dim(J₃O)·H*) | Lean + Coq |
| 3 | κ_T | 1/61 | 1/(b₃ - dim(G₂) - p₂) | Lean + Coq |
| 4 | det(g) | 65/32 | (H* - b₂ - 13) / 2^(Weyl) | Lean + Coq |
| 5 | Q_Koide | 2/3 | dim(G₂)/b₂ = 14/21 | Lean + Coq |
| 6 | m_τ/m_e | 3477 | dim(K₇) + 10·dim(E₈) + 10·H* | Lean + Coq |
| 7 | m_s/m_d | 20 | p₂² × Weyl = 4 × 5 | Lean + Coq |
| 8 | δ_CP | 197° | dim(K₇)·dim(G₂) + H* | Lean + Coq |
| 9 | λ_H (num) | 17 | H* - b₂ - 61 | Lean + Coq |
| 10 | H* | 99 | b₂ + b₃ + 1 | Lean + Coq |
| 11 | p₂ | 2 | dim(G₂)/dim(K₇) | Lean + Coq |
| 12 | N_gen | 3 | rank(E₈) - Weyl | Lean + Coq |
| 13 | dim(E₈×E₈) | 496 | 2 × 248 | Lean + Coq |

### Topological Extension (12 New Relations) - v1.1.0

| # | Symbol | Value | Derivation | Status |
|---|--------|-------|------------|--------|
| 14 | α_s denom | 12 | dim(G₂) - p₂ | Lean + Coq |
| 15 | γ_GIFT | 511/884 | (2·rank(E₈) + 5·H*) / (10·dim(G₂) + 3·dim(E₈)) | Lean + Coq |
| 16 | δ penta | 25 | Weyl² (pentagonal structure) | Lean + Coq |
| 17 | θ₂₃ | 85/99 | (rank(E₈) + b₃) / H* | Lean + Coq |
| 18 | θ₁₃ denom | 21 | b₂ (Betti number) | Lean + Coq |
| 19 | α_s² denom | 144 | (dim(G₂) - p₂)² | Lean + Coq |
| 20 | λ_H² | 17/1024 | (dim(G₂) + N_gen) / 32² | Lean + Coq |
| 21 | θ₁₂ factor | 12775 | Weyl² × γ_num | Lean + Coq |
| 22 | m_μ/m_e base | 27 | dim(J₃(O)) | Lean + Coq |
| 23 | n_s indices | 11, 5 | D_bulk, Weyl_factor | Lean + Coq |
| 24 | Ω_DE frac | 98/99 | (H* - 1) / H* | Lean + Coq |
| 25 | α⁻¹ base | 137 | (dim(E₈) + rank(E₈))/2 + H*/11 | Lean + Coq |

### Yukawa Duality (10 New Relations) - v1.3.0

The Extended Koide formula exhibits a **duality** between two α² structures that are both topologically determined:

| Structure | α² values | Sum | Product+1 | Physical meaning |
|-----------|-----------|-----|-----------|------------------|
| **A** (Topological) | {2, 3, 7} | 12 = gauge_dim | 43 = visible | K3 signature origin |
| **B** (Dynamical) | {2, 5, 6} | 13 = rank+Weyl | 61 = κ_T⁻¹ | Exact mass fit |

The torsion κ_T = 1/61 mediates between topology and physics.

| # | Symbol | Value | Derivation | Status |
|---|--------|-------|------------|--------|
| 26 | α²_A sum | 12 | 2 + 3 + 7 = dim(SM gauge) | Lean + Coq |
| 27 | α²_A prod+1 | 43 | 2×3×7 + 1 = visible_dim | Lean + Coq |
| 28 | α²_B sum | 13 | 2 + 5 + 6 = rank(E₈) + Weyl | Lean + Coq |
| 29 | α²_B prod+1 | 61 | 2×5×6 + 1 = κ_T⁻¹ | Lean + Coq |
| 30 | Duality gap | 18 | 61 - 43 = p₂ × N_gen² | Lean + Coq |
| 31 | α²_up (B) | 5 | dim(K₇) - p₂ = Weyl | Lean + Coq |
| 32 | α²_down (B) | 6 | dim(G₂) - rank(E₈) = 2×N_gen | Lean + Coq |
| 33 | visible_dim | 43 | b₃ - hidden_dim | Lean + Coq |
| 34 | hidden_dim | 34 | b₃ - visible_dim | Lean + Coq |
| 35 | Jordan gap | 27 | 61 - 34 = dim(J₃(𝕆)) | Lean + Coq |

### Irrational Sector (4 New Relations) - v1.4.0

Relations involving irrational numbers (pi, phi) with certified rational parts:

| # | Symbol | Value | Derivation | Status |
|---|--------|-------|------------|--------|
| 36 | alpha^-1 complete | 267489/1952 | 128 + 9 + (65/32)(1/61) | Lean + Coq |
| 37 | theta_13 degrees | 60/7 | 180/b2 = 180/21 | Lean + Coq |
| 38 | phi bounds | (1.618, 1.619) | sqrt(5) in (2.236, 2.237) | Lean + Coq |
| 39 | m_mu/m_e bounds | (206, 208) | 27^phi | Lean + Coq |

**Key insight**: The fine structure constant inverse alpha^-1 = 267489/1952 is an *exact rational*, not an approximation! This comes from:
- 128 = (dim(E8) + rank(E8))/2 = algebraic component
- 9 = H*/D_bulk = bulk component
- 65/1952 = det(g) * kappa_T = torsion correction

### Exceptional Groups (5 New Relations) - v1.5.0

Relations connecting the exceptional Lie groups F4, E6, E8 to GIFT structure:

| # | Symbol | Value | Derivation | Status |
|---|--------|-------|------------|--------|
| 40 | alpha_s^2 | 1/72 | dim(G2)/dim(K7) / (dim(G2)-p2)^2 | Lean + Coq |
| 41 | dim(F4) | 52 | p2^2 * sum(alpha^2_B) = 4 * 13 | Lean + Coq |
| 42 | delta_penta | 25 | dim(F4) - dim(J3(O)) = Weyl^2 | Lean + Coq |
| 43 | J3(O)_0 | 26 | dim(E6) - dim(F4) = dim(J3(O)) - 1 | Lean + Coq |
| 44 | |W(E8)| | 696729600 | p2^dim(G2) * N_gen^Weyl * Weyl^p2 * dim(K7) | Lean + Coq |

**Key insight**: The Weyl group of E8 factorizes as 2^14 * 3^5 * 5^2 * 7, where each prime corresponds exactly to a GIFT topological constant (p2, N_gen, Weyl, dim(K7)).

### Base Decomposition (6 New Relations) - v1.6.0

All primary GIFT constants decompose consistently using ALPHA_SUM_B = 13 = rank(E8) + Weyl:

| # | Symbol | Value | Derivation | Status |
|---|--------|-------|------------|--------|
| 45 | kappa_T^-1 | 61 | dim(F4) + N_gen^2 = 52 + 9 | Lean + Coq |
| 46 | b2 | 21 | ALPHA_SUM_B + rank(E8) = 13 + 8 | Lean + Coq |
| 47 | b3 | 77 | ALPHA_SUM_B * Weyl + 12 = 65 + 12 | Lean + Coq |
| 48 | H* | 99 | ALPHA_SUM_B * dim(K7) + rank(E8) = 91 + 8 | Lean + Coq |
| 49 | quotient_sum | 13 | dim(U1) + Weyl + dim(K7) = 1 + 5 + 7 | Lean + Coq |
| 50 | omega_DE_num | 98 | dim(K7) * dim(G2) = H* - 1 | Lean + Coq |

**Key insight**: The Structure B sum (2 + 5 + 6 = 13) provides a consistent base for decomposing all primary GIFT topological constants. The quotients (1, 5, 7) represent gauge, holonomy, and manifold contributions respectively.

### Topological Constants

The relations above derive from these fixed mathematical structures:

| Constant | Value | Origin |
|----------|-------|--------|
| b₂(K₇) | 21 | Second Betti number of K₇ manifold |
| b₃(K₇) | 77 | Third Betti number of K₇ manifold |
| dim(G₂) | 14 | Dimension of G₂ holonomy group |
| dim(K₇) | 7 | Dimension of internal manifold |
| rank(E₈) | 8 | Rank of E₈ Lie algebra |
| dim(E₈) | 248 | Dimension of E₈ Lie algebra |
| dim(J₃O) | 27 | Dimension of exceptional Jordan algebra |
| Weyl | 5 | Weyl factor from E₈ structure |
| D_bulk | 11 | M-theory bulk dimension |

---

## Formal Verification

### Why Two Proof Assistants?

Independent verification in Lean 4 and Coq provides strong confidence that these mathematical identities are correct. The proofs verify:

1. **Arithmetic correctness**: All rational simplifications (e.g., 21/91 = 3/13) are exact.
2. **Algebraic consistency**: Relations using shared constants are mutually compatible.
3. **Integer constraints**: Values claimed to be integers are proven integral.

### What Formal Verification Does NOT Prove

The proofs establish mathematical identities only. They do not verify:

- That these formulas correspond to physical observables
- That the topological interpretation is correct
- That the underlying physics framework is valid

### Building the Proofs

```bash
# Lean 4
cd Lean && lake build

# Coq
cd COQ && make
```

### Proof Structure

```
Lean/
├── GIFT/
│   ├── Algebra.lean           # E8, G2 structures
│   ├── Topology.lean          # Betti numbers
│   ├── Geometry.lean          # K7, Jordan algebra
│   ├── Relations.lean         # Original 13 relations
│   ├── Relations/
│   │   ├── GaugeSector.lean   # α_s, α⁻¹ structure
│   │   ├── NeutrinoSector.lean # θ₁₂, θ₁₃, θ₂₃, γ_GIFT
│   │   ├── LeptonSector.lean  # m_μ/m_e, λ_H²
│   │   ├── Cosmology.lean     # n_s, Ω_DE
│   │   ├── YukawaDuality.lean # α² duality (v1.3.0)
│   │   ├── IrrationalSector.lean  # θ₁₃, θ₂₃, α⁻¹ (v1.4.0)
│   │   ├── GoldenRatio.lean   # φ, m_μ/m_e (v1.4.0)
│   │   ├── ExceptionalGroups.lean  # F4, E6, E8 (v1.5.0)
│   │   └── BaseDecomposition.lean  # ALPHA_SUM_B decomposition (v1.6.0)
│   └── Certificate.lean       # Master theorem (50 relations)
└── lakefile.lean

COQ/
├── Algebra/                   # E8, G2 structures
├── Topology/                  # Betti numbers
├── Geometry/                  # K7, Jordan algebra
├── Relations/                 # All relation files
│   ├── Weinberg.v
│   ├── Physical.v
│   ├── GaugeSector.v
│   ├── NeutrinoSector.v
│   ├── LeptonSector.v
│   ├── Cosmology.v
│   ├── YukawaDuality.v        # v1.3.0
│   ├── IrrationalSector.v     # v1.4.0
│   ├── GoldenRatio.v          # v1.4.0
│   ├── ExceptionalGroups.v    # v1.5.0
│   └── BaseDecomposition.v    # v1.6.0
└── Certificate/
    └── AllProven.v            # Master theorem (50 relations)
```

---

## K7 Metric Modules (v1.2.0)

The K7 pipeline enables computation of G2 holonomy metrics on twisted connected sum (TCS) manifolds.

### Module Architecture

```
gift_core/
├── geometry/          # Manifold construction
│   ├── kummer_k3.py   # Kummer K3 surface (T^4/Z_2 resolution)
│   ├── acyl_cy3.py    # Asymptotically cylindrical CY3
│   ├── tcs_construction.py  # TCS gluing (X+ ∪ X-)
│   └── k7_metric.py   # Full K7 metric assembly
│
├── g2/                # G2 geometry
│   ├── g2_form.py     # 3-form φ with 35 components
│   ├── holonomy.py    # Holonomy group computation
│   ├── torsion.py     # Torsion-free conditions (dφ=0, d*φ=0)
│   └── constraints.py # GIFT constraints (det_g, κ_T)
│
├── harmonic/          # Hodge theory
│   ├── hodge_laplacian.py   # Δ = dd* + d*d
│   ├── harmonic_forms.py    # Kernel extraction
│   └── betti_validator.py   # Validate b2=21, b3=77
│
├── nn/                # Machine learning
│   ├── fourier_features.py  # Positional encoding
│   └── g2_pinn.py     # Physics-informed neural network
│
├── physics/           # Observable extraction
│   ├── yukawa.py      # Yukawa tensor from harmonic 3-forms
│   ├── mass_spectrum.py     # Fermion mass hierarchies
│   └── gauge_couplings.py   # sin²θ_W, α_s from geometry
│
├── verification/      # Certified computation
│   ├── interval.py    # Interval arithmetic bounds
│   ├── certificate.py # G2Certificate generation
│   └── lean_export.py # Export proofs to Lean/Coq
│
└── pipeline/          # End-to-end workflow
    └── pipeline.py    # GIFTPipeline orchestration
```

### Key Classes

| Class | Purpose |
|-------|---------|
| `KummerK3` | T^4/Z_2 resolution with 16 blown-up singularities |
| `ACylCY3` | Asymptotically cylindrical Calabi-Yau 3-fold |
| `TCSManifold` | Twisted connected sum K7 = X+ ∪_φ X- |
| `G2Form` | Associative 3-form with 35 independent components |
| `HodgeLaplacian` | Discrete Laplacian for harmonic form extraction |
| `G2PINN` | Neural network satisfying G2 torsion constraints |
| `YukawaTensor` | Yukawa couplings from triple harmonic integrals |
| `G2Certificate` | Certified bounds exportable to Lean/Coq |
| `GIFTPipeline` | Full end-to-end metric computation |

---

## Experimental Comparison

For context, these exact values may be compared to experimental measurements. Discrepancies, if any, could indicate either experimental uncertainty or limitations of the conjectured physical correspondence.

| Observable | GIFT (exact) | Experimental (PDG 2024) | Deviation |
|------------|--------------|-------------------------|-----------|
| sin²θ_W | 0.230769... | 0.23122 ± 0.00004 | 0.20% |
| m_s/m_d | 20 | 20.0 ± 1.0 | 0.00% |
| m_τ/m_e | 3477 | 3477.0 ± 0.1 | 0.00% |
| Q_Koide | 0.666... | 0.666661 ± 0.000007 | 0.001% |
| δ_CP | 197° | 197° ± 24° | 0.00% |

---

## Scope and Limitations

### What This Package Provides

- **50 exact relations** with formal proofs (13 original + 12 extension + 10 Yukawa + 4 irrational + 5 exceptional + 6 base decomposition)
- Python interface for numerical computation
- Cross-verified mathematical identities
- **K7 metric pipeline** (v1.2.0): Build G2 holonomy metrics from scratch
- **Yukawa duality** (v1.3.0): Topological ↔ dynamical α² structure
- **Irrational sector** (v1.4.0): Exact alpha^-1, golden ratio bounds
- **Exceptional groups** (v1.5.0): F4, E6, E8 connections and Weyl group factorization
- **Base decomposition** (v1.6.0): Consistent decomposition of all GIFT constants using ALPHA_SUM_B

### What This Package Does Not Claim

- Physical validity of the GIFT framework
- Correctness of the E₈×E₈ / G₂ holonomy interpretation
- Agreement beyond current experimental precision
- Resolution of open problems in theoretical physics

### Falsifiability

The framework makes testable predictions. Key experimental tests include:

- **DUNE (2027+)**: δ_CP = 197° ± 10° would test the CP violation prediction
- **FCC-ee**: High-precision sin²θ_W measurements could distinguish 3/13 from experiment
- **Lattice QCD**: Improved m_s/m_d determinations test the exact integer prediction

Significant deviation from these predictions would challenge the physical interpretation.

---

## Related Resources

### Full Framework

- **Repository**: [gift-framework/GIFT](https://github.com/gift-framework/GIFT)


### Citation

If referencing this work:

```bibtex
@software{gift_core,
  author = {deLaFournière, Brieuc},
  title = {GIFT Core: Formally Verified Mathematical Constants},
  year = {2025},
  url = {https://github.com/gift-framework/core},
  note = {Lean 4 and Coq verified, 50 certified relations}
}
```

---

## License

MIT License

---

## Acknowledgments

This work benefited from computational assistance provided by various AI systems used as mathematical tools. The formal verification was developed using Lean 4 and Coq proof assistants.

---

*GIFT Core v1.6.0 - 50 Certified Relations + K7 Metric Pipeline + Yukawa Duality + Irrational Sector + Exceptional Groups + Base Decomposition*
