# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.27-blue)](Lean/)
[![Coq](https://img.shields.io/badge/Coq-8.18-orange)](COQ/)

Formally verified mathematical relations from the GIFT (Geometric Information Field Theory) framework. All relations are proven in both **Lean 4** and **Coq**.

## Overview

This repository contains **180+ exact mathematical identities** derived from topological invariants of E₈ gauge theory on G₂ holonomy manifolds.

### Core Results

- **Explicit G₂ Metric**: Closed-form solution g = (65/32)^{1/7} × I₇ with det(g) = 65/32 and zero torsion
- **E₈ Root System**: Complete enumeration (240 = 112 + 128) with Weyl reflection theorems
- **G₂ Cross Product**: 7D Lagrange identity ‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩² proven via coassociative 4-form
- **Joyce Existence**: K₇ admits torsion-free G₂ structure (Banach fixed-point formalization)

### Extensions

- **Sequence Embeddings**: Fibonacci F₃–F₁₂ and Lucas L₀–L₉ map to GIFT constants
- **Prime Atlas**: 100% coverage of primes < 200 via three generators (b₃, H*, dim_E₈)
- **Monstrous Moonshine**: 196883 = 47 × 59 × 71, j-invariant 744 = 3 × dim_E₈
- **McKay Correspondence**: E₈ ↔ Binary Icosahedral ↔ Golden Ratio

### Infrastructure

- **Dual Verification**: All theorems proven in Lean 4 + Coq
- **Blueprint**: Dependency graph with 185 linked declarations ([leanblueprint](blueprint/))
- **Python Package**: `giftpy` with certified constants

## Installation

```bash
pip install giftpy
```

## Quick Start

```python
from gift_core import *

# Certified constants
print(SIN2_THETA_W)   # Fraction(3, 13)
print(KAPPA_T)        # Fraction(1, 61)
print(GAMMA_GIFT)     # Fraction(511, 884)
```

## Building Proofs

```bash
# Lean 4
cd Lean && lake build

# Coq
cd COQ && make
```

## Documentation

- [Changelog](CHANGELOG.md)
- [Usage Guide](docs/USAGE.md)
- [Full Framework](https://github.com/gift-framework/GIFT)

## Acknowledgments

Blueprint structure inspired by [KakeyaFiniteFields](https://github.com/math-inc/KakeyaFiniteFields).

## License

MIT

---

*GIFT Core v3.1.10*
