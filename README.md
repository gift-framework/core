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

## Proven Relations (25 Total)

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
│   │   └── Cosmology.lean     # n_s, Ω_DE
│   └── Certificate.lean       # Master theorem (25 relations)
└── lakefile.lean

COQ/
├── Algebra/                   # E8, G2 structures
├── Topology/                  # Betti numbers
├── Geometry/                  # K7, Jordan algebra
├── Relations/                 # All relation files
│   ├── Weinberg.v
│   ├── Physical.v
│   ├── GaugeSector.v          # NEW
│   ├── NeutrinoSector.v       # NEW
│   ├── LeptonSector.v         # NEW
│   └── Cosmology.v            # NEW
└── Certificate/
    └── AllProven.v            # Master theorem (25 relations)
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

- **25 exact relations** with formal proofs (13 original + 12 extension)
- Python interface for numerical computation
- Cross-verified mathematical identities
- **K7 metric pipeline** (v1.2.0): Build G2 holonomy metrics from scratch

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
  note = {Lean 4 and Coq verified, 25 certified relations}
}
```

---

## License

MIT License

---

## Acknowledgments

This work benefited from computational assistance provided by various AI systems used as mathematical tools. The formal verification was developed using Lean 4 and Coq proof assistants.

---

*GIFT Core v1.2.0 - 25 Certified Relations + K7 Metric Pipeline*
