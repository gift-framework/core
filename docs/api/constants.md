# Constants Reference

All constants in `gift_core` derive from fixed topological structures. No continuous parameters are adjusted.

## Topological Inputs

These are the fundamental topological integers from which all relations derive.

### E₈ Structure

| Constant | Value | Description |
|----------|-------|-------------|
| `DIM_E8` | 248 | Dimension of E₈ Lie algebra |
| `RANK_E8` | 8 | Rank of E₈ (Cartan subalgebra dimension) |
| `DIM_E8XE8` | 496 | Dimension of E₈×E₈ (heterotic gauge group) |
| `WEYL_FACTOR` | 5 | From E₈ Weyl group factorization: 2¹⁴ × 3⁵ × **5²** × 7 |
| `E8_ROOTS` | 240 | Number of roots in E₈ root system |

```python
from gift_core import DIM_E8, RANK_E8, DIM_E8XE8, WEYL_FACTOR

print(DIM_E8)       # 248
print(DIM_E8XE8)    # 496 = 2 × 248
print(WEYL_FACTOR)  # 5
```

### K₇ Manifold

| Constant | Value | Description |
|----------|-------|-------------|
| `B2` | 21 | Second Betti number b₂(K₇) |
| `B3` | 77 | Third Betti number b₃(K₇) |
| `DIM_K7` | 7 | Dimension of the internal manifold |

The Betti numbers arise from the Twisted Connected Sum construction:

- Quintic threefold: b₂ = 11, b₃ = 40
- Complete intersection CI(2,2,2): b₂ = 10, b₃ = 37
- Sum: b₂ = 21, b₃ = 77

```python
from gift_core import B2, B3, DIM_K7

print(B2)      # 21
print(B3)      # 77
print(DIM_K7)  # 7
```

### G₂ Holonomy

| Constant | Value | Description |
|----------|-------|-------------|
| `DIM_G2` | 14 | Dimension of G₂ exceptional Lie group |
| `RANK_G2` | 2 | Rank of G₂ |

```python
from gift_core import DIM_G2, RANK_G2

print(DIM_G2)   # 14
print(RANK_G2)  # 2
```

### Exceptional Jordan Algebra

| Constant | Value | Description |
|----------|-------|-------------|
| `DIM_J3O` | 27 | Dimension of J₃(𝕆), the exceptional Jordan algebra |

The 27 arises from 3×3 Hermitian matrices over octonions: 3 diagonal + 3×8 off-diagonal = 27.

```python
from gift_core import DIM_J3O

print(DIM_J3O)  # 27
```

### Derived Structural Constants

| Constant | Value | Formula | Description |
|----------|-------|---------|-------------|
| `H_STAR` | 99 | b₂ + b₃ + 1 | Effective cohomological dimension |
| `P2` | 2 | dim(G₂) / dim(K₇) | Binary duality parameter |
| `N_GEN` | 3 | Topological constraint | Number of generations |

```python
from gift_core import H_STAR, P2, N_GEN

print(H_STAR)  # 99 = 21 + 77 + 1
print(P2)      # 2 = 14 / 7
print(N_GEN)   # 3
```

## Physical Relations

These are the 13 exact relations, all formally verified in Lean 4 and Coq.

### Gauge Sector

| Constant | Value | Formula |
|----------|-------|---------|
| `SIN2_THETA_W` | 3/13 | b₂ / (b₃ + dim G₂) = 21/91 |

```python
from gift_core import SIN2_THETA_W

print(SIN2_THETA_W)              # 3/13
print(float(SIN2_THETA_W))       # 0.23076923...
```

### Hierarchy Parameter

| Constant | Value | Formula |
|----------|-------|---------|
| `TAU` | 3472/891 | (dim E₈×E₈ × b₂) / (dim J₃(𝕆) × H*) |

```python
from gift_core import TAU

print(TAU)          # 3472/891
print(float(TAU))   # 3.8967...
```

### Metric and Torsion

| Constant | Value | Formula |
|----------|-------|---------|
| `DET_G` | 65/32 | (Weyl × 13) / 32 |
| `KAPPA_T` | 1/61 | 1 / (b₃ - dim G₂ - 2) |

```python
from gift_core import DET_G, KAPPA_T

print(DET_G)    # 65/32
print(KAPPA_T)  # 1/61
```

### Neutrino Sector

| Constant | Value | Formula |
|----------|-------|---------|
| `DELTA_CP` | 197 | 7 × dim(G₂) + H* = 98 + 99 |

```python
from gift_core import DELTA_CP

print(DELTA_CP)  # 197 (degrees)
```

### Fermion Masses

| Constant | Value | Formula |
|----------|-------|---------|
| `M_TAU_M_E` | 3477 | dim(K₇) + 10×dim(E₈) + 10×H* |
| `M_S_M_D` | 20 | 4 × Weyl = b₂ - 1 |
| `Q_KOIDE` | 2/3 | dim(G₂) / b₂ = 14/21 |

```python
from gift_core import M_TAU_M_E, M_S_M_D, Q_KOIDE

print(M_TAU_M_E)  # 3477
print(M_S_M_D)    # 20
print(Q_KOIDE)    # 2/3
```

### Higgs Sector

| Constant | Value | Formula |
|----------|-------|---------|
| `LAMBDA_H_NUM` | 17 | dim(G₂) + N_gen = 14 + 3 |

The Higgs self-coupling is λ_H = √(17/32).

```python
from gift_core import LAMBDA_H_NUM

print(LAMBDA_H_NUM)  # 17
```

## Summary Table

| Symbol | Constant | Value | Type |
|--------|----------|-------|------|
| sin²θ_W | `SIN2_THETA_W` | 3/13 | Fraction |
| τ | `TAU` | 3472/891 | Fraction |
| det(g) | `DET_G` | 65/32 | Fraction |
| κ_T | `KAPPA_T` | 1/61 | Fraction |
| δ_CP | `DELTA_CP` | 197 | int |
| m_τ/m_e | `M_TAU_M_E` | 3477 | int |
| m_s/m_d | `M_S_M_D` | 20 | int |
| Q | `Q_KOIDE` | 2/3 | Fraction |
| λ_H num | `LAMBDA_H_NUM` | 17 | int |
| H* | `H_STAR` | 99 | int |
| p₂ | `P2` | 2 | int |
| N_gen | `N_GEN` | 3 | int |
| dim(E₈×E₈) | `DIM_E8XE8` | 496 | int |
