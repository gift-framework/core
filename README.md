# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)

Formally verified mathematical relations from the GIFT framework. All theorems proven in **Lean 4**.

## Structure

```
Lean/GIFT/
├── Core.lean              # Constants (dim_E8, b2, b3, H*, ...)
├── Certificate.lean       # Master theorem (415+ relations)
├── Foundations/           # E8 roots, G2 cross product, Joyce
│   ├── TCSPiecewiseMetric.lean    # Building block asymmetry, Fano [v3.3.20]
│   ├── ConformalRigidity.lean     # G2 rep theory, metric uniqueness [v3.3.20]
│   ├── SpectralScaling.lean       # Neumann eigenvalue hierarchy [v3.3.21]
│   └── Analysis/G2Forms/  # G2 structure: d, ⋆, TorsionFree, Bridge
├── Geometry/              # DG-ready infrastructure [v3.3.7] AXIOM-FREE!
│   ├── Exterior.lean      # Λ*(ℝ⁷) exterior algebra
│   ├── DifferentialFormsR7.lean  # DiffForm, d, d²=0
│   ├── HodgeStarCompute.lean     # Explicit Hodge star (Levi-Civita)
│   └── HodgeStarR7.lean   # ⋆, ψ=⋆φ PROVEN, TorsionFree
├── Spectral/              # Spectral theory [v3.3.17]
│   ├── PhysicalSpectralGap.lean  # ev₁ = 13/99 (zero axioms)
│   ├── SelbergBridge.lean        # Trace formula: MollifiedSum <-> Spectral
│   ├── SelectionPrinciple.lean   # κ = π²/14, building blocks
│   ├── RefinedSpectralBounds.lean # Refined bounds with H7
│   ├── NeckGeometry.lean         # TCS structure, H1-H6 hypotheses
│   ├── TCSBounds.lean            # Model Theorem: ev₁ ~ 1/L²
│   ├── LiteratureAxioms.lean     # Langlais 2024, CGN 2024
│   ├── MassGapRatio.lean         # 14/99 bare algebraic
│   └── YangMills.lean            # Gauge theory connection
├── MollifiedSum/         # Mollified Dirichlet polynomial S_w(T) [v3.3.16]
│   ├── Mollifier.lean         # Cosine-squared kernel w(x)
│   ├── Sum.lean               # S_w(T) as Finset.sum over primes
│   └── Adaptive.lean          # Adaptive cutoff θ(T) = θ₀ + θ₁/log T
├── Zeta/                  # GIFT-Zeta correspondences [v3.3.10]
│   ├── Basic.lean         # gamma, lambda axioms
│   ├── Correspondences.lean      # γ_n ~ GIFT constants
│   └── MultiplesOf7.lean  # Structure theorem
├── Moonshine/             # Monster group connections [v3.3.11]
│   ├── MonsterCoxeter.lean# Monster dim via Coxeter numbers NEW!
│   ├── Supersingular.lean # 15 primes GIFT-expressible
│   └── MonsterZeta.lean   # Monster-Zeta Moonshine
├── Algebraic/             # Octonions, Betti numbers
├── Observables/           # PMNS, CKM, quark masses, cosmology
├── Relations/             # Physical predictions
│   └── G2MetricProperties.lean    # Non-flatness, SPD₇, det(g) [v3.3.20]

gift_core/                 # Python package (giftpy)
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

*GIFT Core v3.3.21*
