# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)

Formally verified mathematical relations from the GIFT framework. All theorems proven in **Lean 4** and **Coq**.

**🎉 v3.3.7: Tier 1 Complete!** All numerical axioms (rpow bounds, log bounds, phi powers) are now PROVEN via Taylor series.

## Structure

```
Lean/GIFT/
├── Core.lean              # Constants (dim_E8, b2, b3, H*, ...)
├── Certificate.lean       # Master theorem (185+ relations)
├── Foundations/           # E8 roots, G2 cross product, Joyce
│   └── Analysis/G2Forms/  # G2 structure: d, ⋆, TorsionFree, Bridge
├── Geometry/              # DG-ready infrastructure [v3.3.7] AXIOM-FREE!
│   ├── Exterior.lean      # Λ*(ℝ⁷) exterior algebra
│   ├── DifferentialFormsR7.lean  # DiffForm, d, d²=0
│   ├── HodgeStarCompute.lean     # Explicit Hodge star (Levi-Civita)
│   └── HodgeStarR7.lean   # ⋆, ψ=⋆φ PROVEN, TorsionFree
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

*GIFT Core v3.3.7*
