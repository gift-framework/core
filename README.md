# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.14.0-blue)](Lean/)
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

### 3. K₇ Manifold via TCS (v3.2)

```
M₁ = Quintic in CP⁴:    b₂ = 11,  b₃ = 40
M₂ = CI(2,2,2) in CP⁶:  b₂ = 10,  b₃ = 37
─────────────────────────────────────────
K₇ = M₁ #_TCS M₂:       b₂ = 21,  b₃ = 77  (BOTH DERIVED!)

H* = b₂ + b₃ + 1 = 99
```

- TCS (Twisted Connected Sum) construction from Corti-Haskins-Nordström-Pacini
- Both Betti numbers now **derived** from building blocks (was: b₃ input)
- Hodge duality and Poincaré duality verified

### 4. Joyce Existence Theorem

```
K₇ admits torsion-free G₂ structure
‖T‖² = 1.3e-7 vs threshold 0.0288 (220000× margin!)
```

- Banach fixed-point formalization
- Sobolev embedding H⁴ ↪ C⁰ (4 > 7/2)
- **PINN validation** (v3.2.11): G₂ torsion minimization on A100
- Implicit function theorem conditions verified

### 5. Structural Identities (v3.2)

```
Weyl Triple Identity: 3 independent paths to Weyl = 5
  (dim_G₂ + 1) / N_gen = 5
  b₂ / N_gen - p₂ = 5
  dim_G₂ - rank_E₈ - 1 = 5

PSL(2,7) = 168: Fano plane symmetry
  (b₃ + dim_G₂) + b₃ = 168
  rank_E₈ × b₂ = 168
  N_gen × (b₃ - b₂) = 168
```

### 6. Tau Structural Derivation (v3.2.10)

```
τ = dim(E₈×E₈) × b₂ / (dim(J₃(𝕆)) × H*)
  = 496 × 21 / (27 × 99)
  = 3472 / 891

E-series Jordan: dim(J₃(𝕆)) = (248 - 78 - 8) / 6 = 27
```

- τ established as **geometric invariant** (not free parameter)
- Formal bounds: 230 < τ⁴ < 231, 898 < τ⁵ < 899
- Target proximity: τ⁴ → 231 = N_gen × b₃, τ⁵ → 900 = h(E₈)²

---

## Physical Relations

The Certificate derives Standard Model parameters from topology:

| Relation | Formula | Value |
|----------|---------|-------|
| Weinberg angle | sin²θ_W = b₂/(b₃+dim_G₂) | 3/13 |
| Koide parameter | Q = 2×dim_G₂/(3×b₂) | 2/3 |
| Generation count | N_gen | 3 |
| κ_T denominator | b₃ - dim_G₂ - p₂ | 61 |
| γ_GIFT | (2×rank_E₈ + 5×H*)/(10×dim_G₂ + 3×dim_E₈) | 511/884 |
| Ω_DE | (b₂ + b₃)/H* | 98/99 |
| m_τ/m_e | (b₃ - b₂) × 62 + 5 | 3477 |

See `Lean/GIFT/Certificate.lean` for complete theorem statements.

### Extended Observables (v3.2.12)

22+ physical observables formally verified in `GIFT.Observables`:

| Observable | GIFT Formula | Value | Deviation |
|------------|--------------|-------|-----------|
| sin²θ₁₂ (PMNS) | (Weyl-1)/α_sum | 4/13 | 0.26% |
| sin²θ₂₃ (PMNS) | (D_bulk-Weyl)/D_bulk | 6/11 | 0.02% |
| m_s/m_d | b2-b0 | 20 | 0.00% |
| m_b/m_t | b₀/χ(K₇) | 1/42 | 0.71% |
| m_H/m_W | (b3+4)/b2 | 81/52 | 0.13% |
| Ω_DM/Ω_b | (b₀+χ(K₇))/rank_E₈ | 43/8 | 0.23% |
| h (Hubble) | (PSL27-b₀)/dim_E₈ | 167/248 | 0.01% |

**The 42 Connection**: χ(K₇)=42 appears in both m_b/m_t=1/42 and Ω_DM/Ω_b=43/8!

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

## Colab Notebook

Run axiom verification on GPU:

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gift-framework/core/blob/main/notebooks/GIFT_Axiom_Verification.ipynb)

- **7/7 numerical axioms** verified (100-digit precision)
- **Joyce PINN validation** with 220000× safety margin
- Exports certificates in JSON + Lean format

## Documentation

- [Changelog](CHANGELOG.md)
- [Usage Guide](docs/USAGE.md)
- [Full Framework](https://github.com/gift-framework/GIFT)

---

## Interactive Visualizations

| Blueprint | Description |
|-----------|-------------|
| [GIFT Lean Blueprint](https://gift-framework.github.io/core/home_page/gift_blueprint.html) | Dependency graph |

*Created with [Lean Blueprint Copilot](https://github.com/augustepoiroux/LeanBlueprintCopilot)*

---

## Acknowledgments

Blueprint structure inspired by [KakeyaFiniteFields](https://github.com/math-inc/KakeyaFiniteFields).

## License

MIT

---

*GIFT Core v3.2.12*
