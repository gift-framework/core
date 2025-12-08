# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![Publish to PyPI](https://github.com/gift-framework/core/actions/workflows/publish.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/publish.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.14-blue)](Lean/)
[![Coq](https://img.shields.io/badge/Coq-8.18-orange)](COQ/)

Formally verified mathematical relations from the GIFT (Geometric Information Field Theory) framework. All relations are proven in both **Lean 4** and **Coq**.

## What is this?

This repository contains **54 exact mathematical identities** derived from topological invariants of E8 × E8 gauge theory on G2 holonomy manifolds. Each relation is:

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

*GIFT Core v1.5.0 — 54 certified relations*
