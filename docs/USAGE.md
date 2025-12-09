# giftpy Usage Guide

Complete documentation for the `giftpy` Python package.

## Installation

```bash
pip install giftpy
```

For K7 metric modules (optional):
```bash
pip install giftpy numpy
```

## Basic Usage

```python
from gift_core import *

# Access any certified constant
print(SIN2_THETA_W)      # Fraction(3, 13)
print(TAU)               # Fraction(3472, 891)
print(KAPPA_T)           # Fraction(1, 61)
print(GAMMA_GIFT)        # Fraction(511, 884)
print(ALPHA_INV_BASE)    # 137

# Iterate over all proven relations
for r in PROVEN_RELATIONS:
    print(f"{r.symbol} = {r.value}")
```

## Certified Constants

### Original Relations

| Constant | Value | Description |
|----------|-------|-------------|
| `SIN2_THETA_W` | 3/13 | Weinberg angle |
| `TAU` | 3472/891 | Hierarchy parameter |
| `KAPPA_T` | 1/61 | Torsion parameter |
| `DET_G` | 65/32 | Metric determinant |
| `Q_KOIDE` | 2/3 | Koide formula |
| `M_TAU_M_E` | 3477 | Tau/electron mass ratio |
| `M_S_M_D` | 20 | Strange/down mass ratio |
| `DELTA_CP` | 197 | CP violation phase (degrees) |
| `H_STAR` | 99 | Topological invariant |
| `P2` | 2 | Pontryagin class |
| `N_GEN` | 3 | Number of generations |

### Topological Extension

| Constant | Value | Description |
|----------|-------|-------------|
| `GAMMA_GIFT` | 511/884 | GIFT parameter |
| `THETA_23` | 85/99 | Neutrino mixing angle |
| `ALPHA_INV_BASE` | 137 | Fine structure constant inverse (base) |
| `OMEGA_DE_FRAC` | 98/99 | Dark energy fraction |

### Yukawa Duality

| Constant | Value | Description |
|----------|-------|-------------|
| `ALPHA_SUM_A` | 12 | Structure A sum (2+3+7) |
| `ALPHA_SUM_B` | 13 | Structure B sum (2+5+6) |
| `ALPHA_PROD_A` | 42 | Structure A product |
| `ALPHA_PROD_B` | 60 | Structure B product |
| `DUALITY_GAP` | 18 | Gap between structures |
| `VISIBLE_DIM` | 43 | Visible sector dimension |
| `HIDDEN_DIM` | 34 | Hidden sector dimension |

### Irrational Sector

| Constant | Value | Description |
|----------|-------|-------------|
| `ALPHA_INV_COMPLETE` | 267489/1952 | Complete alpha inverse (~137.033) |
| `THETA_13_DEGREES_SIMPLIFIED` | 60/7 | Theta_13 in degrees (~8.57) |
| `PHI_LOWER_BOUND` | 1618/1000 | Golden ratio lower bound |
| `M_MU_M_E_LOWER` | 206 | Muon/electron mass ratio bound |

### Exceptional Groups

| Constant | Value | Description |
|----------|-------|-------------|
| `DIM_F4` | 52 | Dimension of F4 |
| `DELTA_PENTA` | 25 | Pentagonal structure (Weyl^2) |
| `WEYL_E8_ORDER` | 696729600 | Order of Weyl(E8) |

### Mass Factorization (v1.6.0)

| Constant | Value | Description |
|----------|-------|-------------|
| `MASS_FACTORIZATION` | 3477 | 3 x 19 x 61 (tau/electron mass ratio) |
| `PRIME_8` | 19 | 8th prime (Von Staudt-Clausen) |
| `T61_DIM` | 61 | Torsion configuration space |
| `W_SUM` | 49 | G2 torsion classes (1+7+14+27) |
| `T61_RESIDUE` | 12 | Gauge residue (dim(G2) - p2) |
| `IMPEDANCE` | 9 | H*/D_bulk |

### Sequence Embeddings (v2.0)

```python
from gift_core.sequences import fib, lucas, FIBONACCI_GIFT, LUCAS_GIFT

# Fibonacci embedding: F_3...F_12 are GIFT constants
print(fib(8))   # 21 = b2
print(fib(9))   # 34 = hidden_dim
print(fib(12))  # 144 = (dim_G2 - p2)^2

# Lucas embedding
print(lucas(6))  # 18 = duality_gap
print(lucas(8))  # 47 = Monster factor

# View all embeddings
for n, (val, name) in FIBONACCI_GIFT.items():
    print(f"F_{n} = {val} = {name}")
```

### Prime Atlas (v2.0)

```python
from gift_core.primes import prime_expression, prime_generator, is_heegner

# All primes < 200 have GIFT expressions
print(prime_expression(67))   # "b3 - 2 * Weyl_factor"
print(prime_expression(163))  # "dim_E8 - rank_E8 - b3"

# Which generator?
print(prime_generator(59))   # "b3"
print(prime_generator(137))  # "H_star"
print(prime_generator(197))  # "dim_E8"

# Heegner numbers
print(is_heegner(163))  # True (largest Heegner number)
```

### Monster Group (v2.0)

```python
from gift_core.monster import MONSTER_DIM, MONSTER_FACTORS, J_CONSTANT

# Monster dimension factorization
print(MONSTER_DIM)     # 196883
print(MONSTER_FACTORS) # (47, 59, 71) - all GIFT-expressible!

# j-invariant
print(J_CONSTANT)      # 744 = 3 x 248 = N_gen x dim_E8
```

### McKay Correspondence (v2.0)

```python
from gift_core.mckay import COXETER_E8, ICOSAHEDRON, PHI_RATIOS

# E8 <-> Icosahedron correspondence
print(COXETER_E8)           # 30 = icosahedron edges
print(ICOSAHEDRON["faces"]) # 20 = m_s_m_d

# Golden ratio from GIFT ratios
for name, (num, den, error) in PHI_RATIOS.items():
    print(f"{name}: {num}/{den} (error: {error:.3f}%)")
```

## Topological Constants

These are the fundamental constants from which relations are derived:

```python
from gift_core import *

print(DIM_E8)      # 248 - Dimension of E8
print(RANK_E8)     # 8   - Rank of E8
print(DIM_G2)      # 14  - Dimension of G2
print(DIM_K7)      # 7   - Dimension of K7 manifold
print(B2)          # 21  - Second Betti number
print(B3)          # 77  - Third Betti number
print(DIM_J3O)     # 27  - Jordan algebra dimension
print(WEYL_FACTOR) # 5   - Weyl factor
print(D_BULK)      # 11  - M-theory dimension
```

## K7 Metric Pipeline

Build G2 holonomy metrics on K7 manifolds (requires numpy):

```python
import gift_core as gc

if gc.NUMPY_AVAILABLE:
    # Configure pipeline
    config = gc.PipelineConfig(
        neck_length=15.0,      # TCS gluing parameter
        resolution=32,         # Grid resolution
        pinn_epochs=1000,      # Neural network training
        use_pinn=True          # Enable physics-informed learning
    )

    # Run computation
    result = gc.run_pipeline(config)

    # Access results
    print(f"det(g) = {result.det_g}")
    print(f"kappa_T = {result.kappa_T}")
    print(f"b2 = {result.betti[2]}")
    print(f"b3 = {result.betti[3]}")

    # Export to proof assistants
    lean_proof = result.certificate.to_lean()
    coq_proof = result.certificate.to_coq()

    # Physics extraction
    yukawa = gc.YukawaTensor(result.harmonic_forms)
    masses = yukawa.fermion_masses()
```

### Pipeline Modules

| Module | Purpose |
|--------|---------|
| `geometry/` | K3, CY3, TCS manifold construction |
| `g2/` | G2 3-form, holonomy, torsion constraints |
| `harmonic/` | Hodge Laplacian, harmonic forms, Betti validation |
| `nn/` | Physics-informed neural networks |
| `physics/` | Yukawa tensors, mass spectrum, gauge couplings |
| `verification/` | Interval arithmetic, certificate generation |

## Relation Object

Each relation is a `CertifiedRelation` object:

```python
from gift_core import PROVEN_RELATIONS

r = PROVEN_RELATIONS[0]
print(r.symbol)      # Human-readable symbol
print(r.value)       # Exact value (Fraction or int)
print(r.derivation)  # How it's derived
print(r.status)      # "Lean + Coq"
```

## Version History

See [CHANGELOG.md](../CHANGELOG.md) for detailed version history.
