# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![Publish to PyPI](https://github.com/gift-framework/core/actions/workflows/publish.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/publish.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.14-blue)](Lean/)
[![Coq](https://img.shields.io/badge/Coq-8.18-orange)](COQ/)

Formally verified mathematical relations from the GIFT (Geometric Information Field Theory) framework. All relations are proven in both **Lean 4** and **Coq**.

## What is this?

This repository contains **165+ exact mathematical identities** derived from topological invariants of E8 × E8 gauge theory on G2 holonomy manifolds. Each relation is:

- An exact rational or integer value (no fitting or approximation)
- Independently verified in two proof assistants
- Available as Python constants via `giftpy`

**Note**: The physical interpretation of these relations remains conjectural. This package proves mathematical identities only.

## Installation

```bash
pip install giftpy
```

## Quick Start

```python
from gift_core import *

# Access certified constants
print(SIN2_THETA_W)   # Fraction(3, 13)
print(KAPPA_T)        # Fraction(1, 61)
print(GAMMA_GIFT)     # Fraction(511, 884)

# List all proven relations
for r in PROVEN_RELATIONS:
    print(f"{r.symbol} = {r.value}")
```

## What's New in v5.0

**Octonion-Based Algebraic Foundations**: GIFT constants are now **derived** from octonion structure, not arbitrary inputs!

The algebraic chain ℍ → 𝕆 → G₂ → GIFT is fully formalized:

```lean
-- Octonions have 7 imaginary units
imaginary_count = 7

-- G₂ = Aut(𝕆) has dimension 2 × 7 = 14
dim_G2 = 2 * imaginary_count

-- b₂ = C(7,2) = 21 (pairs of imaginary units)
b2 = Nat.choose imaginary_count 2

-- b₃ = b₂ + fund(E₇) = 21 + 56 = 77
b3 = b2 + fund_E7

-- Physical predictions DERIVE from this chain:
-- sin²θ_W = 21/91 = 3/13
-- Q_Koide = 14/21 = 2/3
-- N_gen = 3
```

New modules in `Lean/GIFT/Algebraic/`:
- **Quaternions.lean**: K₄ ↔ ℍ correspondence
- **Octonions.lean**: 7 imaginary units, Fano plane structure
- **CayleyDickson.lean**: Doubling construction ℝ → ℂ → ℍ → 𝕆
- **G2.lean**: Aut(𝕆) with dim = 14
- **BettiNumbers.lean**: b₂, b₃, H* from octonion pairs
- **GIFTConstants.lean**: Physical predictions from algebra

## Building Proofs

```bash
# Lean 4
cd Lean && lake build

# Coq
cd COQ && make
```

## Documentation

- **giftpy usage guide**: [docs/USAGE.md](docs/USAGE.md) — all constants, K7 pipeline, examples
- **Changelog**: [CHANGELOG.md](CHANGELOG.md)
- **Full framework**: [gift-framework/GIFT](https://github.com/gift-framework/GIFT)
- **Lean Blueprint**: [Interactive visualization](https://gift-framework.github.io/GIFT/docs/figures/gift_blueprint.html)

## License

MIT

---

*GIFT Core v5.0.0
