# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)

Formally verified mathematical relations from the GIFT framework. All theorems proven in **Lean 4** and **Coq**.

## Structure

```
Lean/GIFT/
├── Core.lean              # Constants (dim_E8, b2, b3, H*, ...)
├── Certificate.lean       # Master theorem (250+ relations)
├── Foundations/           # E8 roots, G2 cross product, Joyce
│   └── Analysis/G2Forms/  # G2 structure: d, ⋆, TorsionFree, Bridge
├── Geometry/              # DG-ready infrastructure [v3.3.7] AXIOM-FREE!
│   ├── Exterior.lean      # Λ*(ℝ⁷) exterior algebra
│   ├── DifferentialFormsR7.lean  # DiffForm, d, d²=0
│   ├── HodgeStarCompute.lean     # Explicit Hodge star (Levi-Civita)
│   └── HodgeStarR7.lean   # ⋆, ψ=⋆φ PROVEN, TorsionFree
├── Spectral/              # Spectral theory [v3.3.14]
│   ├── SelectionPrinciple.lean   # κ = π²/14, building blocks NEW!
│   ├── Tier1Bounds.lean          # Refined bounds with H7 NEW!
│   ├── NeckGeometry.lean         # TCS structure, H1-H6 hypotheses
│   ├── TCSBounds.lean            # Model Theorem: λ₁ ~ 1/L²
│   ├── LiteratureAxioms.lean     # Langlais 2024, CGN 2024
│   ├── MassGapRatio.lean         # λ₁ = 14/99
│   └── YangMills.lean            # Gauge theory connection
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
└── Relations/             # Physical predictions

COQ/                       # Coq mirror proofs

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
# Lean 4
cd Lean && lake build

# Coq
cd COQ && make
```

## Documentation

For extended observables, publications, and detailed analysis:

**[gift-framework/GIFT](https://github.com/gift-framework/GIFT)**

---

[Changelog](CHANGELOG.md) | [MIT License](LICENSE)

*GIFT Core v3.3.12*
