# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.14-blue)](Lean/)
[![Coq](https://img.shields.io/badge/Coq-8.18-orange)](COQ/)

Formally verified mathematical relations from the GIFT (Geometric Information Field Theory) framework. All relations are proven in both **Lean 4** and **Coq**.

## Overview

This repository contains **180+ exact mathematical identities** derived from topological invariants of E8 gauge theory on G2 holonomy manifolds. Each relation is:

- An exact rational or integer value (no fitting)
- Independently verified in two proof assistants
- Available as Python constants via `giftpy`

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

## License

MIT

---

*GIFT Core v3.1.3*
