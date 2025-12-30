# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.27-blue)](Lean/)
[![Coq](https://img.shields.io/badge/Coq-8.18-orange)](COQ/)

Formally verified mathematical relations from the GIFT framework. All theorems proven in **Lean 4** and **Coq**.

## Certificate Structure

The GIFT Certificate proves **180+ mathematical identities** organized in five foundational pillars:

### 1. E₈ Root System (248 dimensions)

```
dim(E₈) = 248 = 240 roots + 8 rank
        = 8 × 31 (Mersenne structure)
        = 120 + 128 (SO(16) decomposition)
```

- Complete root enumeration: 112 (D₈) + 128 (half-integer)
- Weyl group order: 2¹⁴ × 3⁵ × 5² × 7 = 696,729,600
- Weyl reflection preserves E₈ lattice

### 2. G₂ Holonomy (14 dimensions)

```
dim(G₂) = 14 = 12 roots + 2 rank
             = GL(7) orbit stabilizer: 49 - 35
```

- 7D cross product with Lagrange identity: ‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩²
- Fano plane structure (7 lines ↔ 7 octonion imaginaries)
- Bilinearity, antisymmetry, octonion structure proven

### 3. K₇ Manifold (Betti numbers)

```
b₀ = 1,  b₁ = 0,  b₂ = 21,  b₃ = 77
H* = b₂ + b₃ + 1 = 99
```

- Hodge duality and Poincaré duality
- 2-forms decomposition: Ω² = Ω²₇ ⊕ Ω²₁₄ (7 + 14 = 21)
- 3-forms decomposition: Ω³ = Ω³₁ ⊕ Ω³₇ ⊕ Ω³₂₇ (1 + 7 + 27 = 35)

### 4. Joyce Existence Theorem

```
K₇ admits torsion-free G₂ structure
‖T‖ < 0.00141 vs threshold 0.0288 (20× margin)
```

- Banach fixed-point formalization
- Sobolev embedding H⁴ -> C⁰ (4 > 7/2)
- Implicit function theorem conditions verified

### 5. Exceptional Chain

```
dim(E₆) = 78  = 6 × 13 = b₃ + 1
dim(E₇) = 133 = 7 × 19 = b₃ + 8 × 7
dim(E₈) = 248 = 8 × 31
```

- F₄ (52) → E₆ (78) → E₇ (133) → E₈ (248)
- Jordan algebra: dim(J₃(𝕆)) = 27 = dim(E₆) - dim(F₄) - 1

---

## Physical Relations

The Certificate derives Standard Model parameters from topology:

| Relation | Formula | Value |
|----------|---------|-------|
| Weinberg angle | sin²θ_W = 3(b₃+dim_G₂)/(13×b₂) | 3/13 |
| Koide parameter | Q = 2×dim_G₂/(3×b₂) | 2/3 |
| Generation count | N_gen | 3 |
| κ_T denominator | b₃ - dim_G₂ - p₂ | 61 |
| γ_GIFT | (2×rank_E₈ + 5×H*)/(10×dim_G₂ + 3×dim_E₈) | 511/884 |
| Ω_DE | (b₂ + b₃)/H* | 98/99 |

See `Lean/GIFT/Certificate.lean` for complete theorem statements.

---

## Extensions

- **Sequence Embeddings**: Fibonacci F₃–F₁₂ and Lucas L₀–L₉ map to GIFT constants
- **Prime Atlas**: 100% coverage of primes < 200 via three generators (b₃, H*, dim_E₈)
- **Monstrous Moonshine**: 196883 = 47 × 59 × 71, j-invariant 744 = 3 × dim_E₈
- **McKay Correspondence**: E₈ ↔ Binary Icosahedral ↔ Golden Ratio

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

*GIFT Core v3.1.12*
