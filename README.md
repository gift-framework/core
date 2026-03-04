# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)

Formally verified mathematical relations from the GIFT framework. 455+ certified relations, 87 axioms classified (A-F), all theorems proven in **Lean 4** (146 files, 2656 build jobs).

## Structure

```
Lean/GIFT/
├── Core.lean                # Constants (dim_E8, b2, b3, H*, ...)
├── Certificate/             # Modular certificate system [v3.3.25]
│   ├── Core.lean            # Master: Foundations ∧ Predictions ∧ Spectral
│   ├── Foundations.lean     # E₈, G₂, octonions, K₇, Joyce, NK cert (26 conjuncts)
│   ├── Predictions.lean     # 33+ relations, ~50 observables (48 conjuncts)
│   └── Spectral.lean        # Mass gap 14/99, TCS, selection (27 conjuncts)
├── Certificate.lean         # Backward-compat wrapper (legacy aliases)
│
├── Foundations/              # Mathematical foundations (23 files)
│   ├── RootSystems.lean     # E₈ roots in ℝ⁸ (240 vectors)
│   ├── E8Lattice.lean       # E₈ lattice, Weyl reflection
│   ├── G2CrossProduct.lean  # 7D cross product, Fano plane
│   ├── OctonionBridge.lean  # R8-R7 connection via octonions
│   ├── AmbroseSinger.lean   # Holonomy diagnostics (so(7)=g₂⊕g₂⊥)
│   ├── ExplicitG2Metric.lean # 169-param Chebyshev-Cholesky [v3.3.25]
│   ├── NewtonKantorovich.lean # NK cert: h=6.65e-8 < 0.5 [v3.3.25]
│   ├── K3HarmonicCorrection.lean # ×2995 torsion reduction [v3.3.25]
│   ├── NumericalBounds.lean # Taylor series bounds (axiom-free)
│   ├── GoldenRatioPowers.lean # φ power bounds
│   ├── PoincareDuality.lean # H*=1+2*dim_K7², holonomy chain
│   ├── ConformalRigidity.lean # G₂ rep theory, metric uniqueness
│   ├── SpectralScaling.lean # Neumann eigenvalue hierarchy
│   ├── TCSConstruction.lean, TCSPiecewiseMetric.lean, G2Holonomy.lean, ...
│   └── Analysis/            # G₂ forms, Hodge theory, Sobolev
│       └── G2Forms/         # d, ⋆, TorsionFree, Bridge
│
├── Geometry/                # Axiom-free DG infrastructure [v3.3.7]
│   ├── Exterior.lean        # Λ*(ℝ⁷) exterior algebra
│   ├── DifferentialFormsR7.lean # DiffForm, d, d²=0
│   ├── HodgeStarCompute.lean # Explicit Hodge star (Levi-Civita)
│   └── HodgeStarR7.lean     # ⋆, ψ=⋆φ PROVEN, TorsionFree
│
├── Spectral/                # Spectral gap theory (14 files) [v3.3.17]
│   ├── PhysicalSpectralGap.lean # ev₁ = 13/99 (zero axioms)
│   ├── SelbergBridge.lean   # Trace formula: MollifiedSum <-> Spectral
│   ├── SelectionPrinciple.lean # κ = π²/14, building blocks
│   ├── TCSBounds.lean       # Model Theorem: ev₁ ~ 1/L²
│   ├── NeckGeometry.lean    # TCS structure, H1-H6 hypotheses
│   ├── CheegerInequality.lean # Cheeger-Buser bounds
│   ├── ConnesBridge.lean    # Noncommutative geometry connection
│   ├── UniversalLaw.lean    # λ₁ × H* = dim(G₂)
│   ├── MassGapRatio.lean    # 14/99 bare algebraic
│   ├── YangMills.lean       # Gauge theory connection
│   └── LiteratureAxioms.lean, G2Manifold.lean, RefinedSpectralBounds.lean, SpectralTheory.lean
│
├── MollifiedSum/            # Mollified Dirichlet polynomial [v3.3.16]
│   ├── Mollifier.lean       # Cosine-squared kernel w(x)
│   ├── Sum.lean             # S_w(T) as Finset.sum over primes
│   ├── Adaptive.lean        # Adaptive cutoff θ(T) = θ₀ + θ₁/log T
│   └── AdaptiveGIFT.lean    # GIFT-specific adaptive parameters
│
├── Relations/               # Physical predictions (21 files)
│   ├── GaugeSector.lean, LeptonSector.lean, NeutrinoSector.lean, QuarkSector.lean
│   ├── Cosmology.lean, MassFactorization.lean, YukawaDuality.lean
│   ├── ExceptionalGroups.lean, ExceptionalChain.lean, SO16Relations.lean
│   └── Structural.lean, BaseDecomposition.lean, IrrationalSector.lean, ...
│
├── Observables/             # PMNS, CKM, quark masses, cosmology
├── Algebraic/               # Octonions, Betti numbers, G₂, SO(16)
├── Hierarchy/               # Dimensional gap, absolute masses, E₆ cascade
│
├── Exploratory/             # Number-theoretic curiosities [v3.3.25]
│   ├── Sequences/           # Fibonacci, Lucas embeddings
│   ├── Primes/              # Prime Atlas (direct, derived, Heegner)
│   ├── Moonshine/           # Monster group, j-invariant, supersingular
│   ├── McKay/               # McKay correspondence, golden emergence
│   └── Zeta/                # Riemann zeta correspondences (conjectures)
│
├── Joyce.lean               # Joyce existence theorem
├── Sobolev.lean             # Sobolev embedding
├── DifferentialForms.lean   # Differential forms
└── ImplicitFunction.lean    # Implicit function theorem

gift_core/                   # Python package (giftpy)
```

## Quick Start

```bash
pip install giftpy
```

```python
from gift_core import *

print(SIN2_THETA_W)   # Fraction(3, 13)
print(GAMMA_GIFT)     # Fraction(511, 884)
print(TAU)            # Fraction(3472, 891)
```

## Building Proofs

```bash
cd Lean && lake build
```

## Documentation

For extended observables, publications, and detailed analysis:

**[gift-framework/GIFT](https://github.com/gift-framework/GIFT)**

---

[Changelog](CHANGELOG.md) | [MIT License](LICENSE)

*GIFT Core v3.3.25*
