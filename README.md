# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![Publish to PyPI](https://github.com/gift-framework/core/actions/workflows/publish.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/publish.yml)
[![PyPI](https://img.shields.io/pypi/v/gift-core)](https://pypi.org/project/gift-core/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.14-blue)](Lean/)
[![Coq](https://img.shields.io/badge/Coq-8.18-orange)](COQ/)

Formally verified mathematical constants from the GIFT framework.

## Install

```bash
pip install gift-core
```

## Usage

```python
from gift_core import *

print(SIN2_THETA_W)  # Fraction(3, 13)
print(B2, B3)        # 21 77
print(DET_G)         # Fraction(65, 32)

# All 13 proven relations
for r in PROVEN_RELATIONS:
    print(f"{r.symbol} = {r.value}")
```

## What's inside

| Constant | Value | Proven |
|----------|-------|--------|
| sin^2(theta_W) | 3/13 | Lean + Coq |
| tau | 3472/891 | Lean + Coq |
| det(g) | 65/32 | Lean + Coq |
| kappa_T | 1/61 | Lean + Coq |
| delta_CP | 197 | Lean + Coq |
| m_tau/m_e | 3477 | Lean + Coq |
| m_s/m_d | 20 | Lean + Coq |
| Q_Koide | 2/3 | Lean + Coq |
| lambda_H_num | 17 | Lean + Coq |
| H* | 99 | Lean + Coq |
| p2 | 2 | Lean + Coq |
| N_gen | 3 | Lean + Coq |
| dim(E8xE8) | 496 | Lean + Coq |

13 relations total, all proven in both Lean 4 and Coq.

## Verification

```bash
# Lean
cd Lean && lake build

# Coq
cd COQ && make
```

## Links

- Full framework: [gift-framework/GIFT](https://github.com/gift-framework/GIFT)
- Publications: [gift_2_3_main.md](https://github.com/gift-framework/GIFT/blob/main/gift_2_3_main.md)

MIT License | gift-framework
