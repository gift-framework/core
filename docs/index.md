# giftpy

**Formally verified mathematical constants from the GIFT framework.**

[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)
[![Lean](https://img.shields.io/badge/Lean_4-verified-green)](https://github.com/gift-framework/core/tree/main/Lean)
[![Coq](https://img.shields.io/badge/Coq-verified-green)](https://github.com/gift-framework/core/tree/main/COQ)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

## Overview

`giftpy` provides access to mathematical constants derived from the GIFT (Geometric Information Field Theory) framework. All 13 exact relations are formally verified in both Lean 4 and Coq proof assistants.

```python
from gift_core import *

print(SIN2_THETA_W)  # Fraction(3, 13)
print(TAU)           # Fraction(3472, 891)
print(DELTA_CP)      # 197
```

## Key Features

| Feature | Description |
|---------|-------------|
| **13 Verified Relations** | All exact relations proven in Lean 4 and Coq |
| **Pure Python** | No external dependencies for core functionality |
| **Exact Arithmetic** | Uses `fractions.Fraction` for rational numbers |
| **Type Hints** | Full type annotations for IDE support |

## The Constants

All constants derive from fixed topological structures:

- **E₈×E₈ gauge group**: dim = 496
- **K₇ manifold**: b₂ = 21, b₃ = 77
- **G₂ holonomy**: dim = 14

No continuous parameters are adjusted to fit data.

## Quick Example

```python
from gift_core import PROVEN_RELATIONS

for relation in PROVEN_RELATIONS:
    print(f"{relation.symbol:12} = {relation.value}")
```

Output:
```
sin²θ_W      = 3/13
τ            = 3472/891
det(g)       = 65/32
κ_T          = 1/61
δ_CP         = 197
m_τ/m_e      = 3477
m_s/m_d      = 20
Q_Koide      = 2/3
λ_H_num      = 17
H*           = 99
p₂           = 2
N_gen        = 3
dim(E₈×E₈)   = 496
```

## Links

- **Full Framework**: [gift-framework/GIFT](https://github.com/gift-framework/GIFT)
- **Publications**: [Zenodo](https://zenodo.org/records/15526659)
- **Updates**: [@GIFTheory](https://x.com/GIFTheory)

## Citation

If using this package in academic work:

```bibtex
@software{gift_core,
  author = {GIFT Framework},
  title = {giftpy: Formally Verified GIFT Constants},
  url = {https://github.com/gift-framework/core},
  version = {0.1.0},
  year = {2024}
}
```

## License

MIT License. See [LICENSE](https://github.com/gift-framework/core/blob/main/LICENSE) for details.
