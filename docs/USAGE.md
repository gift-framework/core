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

### Mass Factorization

| Constant | Value | Description |
|----------|-------|-------------|
| `MASS_FACTORIZATION` | 3477 | 3 x 19 x 61 (tau/electron mass ratio) |
| `PRIME_8` | 19 | 8th prime (Von Staudt-Clausen) |
| `T61_DIM` | 61 | Torsion configuration space |
| `W_SUM` | 49 | G2 torsion classes (1+7+14+27) |
| `T61_RESIDUE` | 12 | Gauge residue (dim(G2) - p2) |
| `IMPEDANCE` | 9 | H*/D_bulk |

### Sequence Embeddings

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

### Joyce Existence Theorem

```python
from gift_core.analysis import JoyceCertificate, verify_pinn_bounds

# Quick verification
assert verify_pinn_bounds()  # K7 admits torsion-free G2!

# Detailed certificate
cert = JoyceCertificate.verify()
print(cert)
# JoyceCertificate:
#   Torsion < threshold: True
#   Safety margin: 20.4x
#   Contraction K < 1: True
#   det(g) = 65/32: True
#   Status: VALID

# Check individual conditions
print(cert.torsion_below_threshold)  # True
print(float(cert.safety_margin))     # ~20.4
```

### Interval Arithmetic

```python
from gift_core.analysis import (
    Interval, TORSION_BOUND, JOYCE_THRESHOLD,
    DET_G_BOUND, DET_G_TARGET
)

# PINN torsion bound: [0.00139, 0.00141]
print(TORSION_BOUND)  # [0.001390, 0.001410]

# Joyce threshold: 0.0288
print(JOYCE_THRESHOLD.lo)  # 0.0288

# Verify bound is below threshold
print(TORSION_BOUND.hi < JOYCE_THRESHOLD.lo)  # True

# det(g) verification
print(DET_G_BOUND.contains(DET_G_TARGET))  # True
```

## Algebraic Foundations (v3.2)

GIFT constants are now **derived** from octonion algebraic structure:

```python
from gift_core import *

# The derivation chain: ℍ → 𝕆 → G₂ → GIFT

# Octonions have 7 imaginary units
IMAGINARY_COUNT = 7

# G₂ = Aut(𝕆) has dimension 2 × 7 = 14
DIM_G2 = 14  # = 2 * IMAGINARY_COUNT

# b₂ = C(7,2) = 21 (pairs of imaginary units)
B2 = 21  # = choose(7, 2)

# fund(E₇) = 2 × b₂ + dim(G₂) = 56
FUND_E7 = 56

# b₃ = b₂ + fund(E₇) = 77
B3 = 77  # = 21 + 56

# H* = b₂ + b₃ + 1 = 99
H_STAR = 99

# Physical predictions from the algebraic chain:
# sin²θ_W = 21/91 = 3/13  (b₂ / (b₃ + dim_G2))
# Q_Koide = 14/21 = 2/3   (dim_G2 / b₂)
# N_gen = 3               (from K₄ matchings, E₇ structure)
```

### Key Insight

Previous versions defined constants arbitrarily:
```python
DIM_E8 = 248  # Just a number
```

V3.2 **derives** them from octonion structure:
```
𝕆 has 7 imaginary units
  → G₂ = Aut(𝕆) has dim = 2×7 = 14
  → b₂ = C(7,2) = 21
  → fund(E₇) = 56
  → b₃ = 77
  → Physical predictions follow
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

## Lean 4 Usage (v3.3+)

### GIFT.Core - Single Source of Truth

As of v3.3, use `GIFT.Core` for all GIFT constants:

```lean
import GIFT.Core
open GIFT.Core

-- All constants are available
#check b2        -- 21
#check b3        -- 77
#check H_star    -- 99
#check dim_E8    -- 248
#check dim_G2    -- 14
```

### Migration from Legacy Modules

If you have code using `GIFT.Algebra`, `GIFT.Topology`, or `GIFT.Geometry`:

**Before:**
```lean
import GIFT.Algebra
import GIFT.Topology
import GIFT.Geometry
open GIFT.Algebra GIFT.Topology GIFT.Geometry
```

**After:**
```lean
import GIFT.Core
open GIFT.Core
```

The legacy modules still work (they re-export from Core), but new code should use Core directly.

### Constant Derivation Hierarchy

Constants are derived from octonion structure:

```
GIFT.Algebraic.Octonions
  └─ imaginary_count = 7

GIFT.Algebraic.G2
  └─ dim_G2 = 2 × imaginary_count = 14

GIFT.Algebraic.BettiNumbers
  ├─ b2 = C(7,2) = 21
  ├─ fund_E7 = 2 × b2 + dim_G2 = 56
  ├─ b3 = b2 + fund_E7 = 77
  └─ H_star = b2 + b3 + 1 = 99

GIFT.Core
  ├─ Re-exports from Algebraic modules
  └─ Defines remaining constants (dim_E8, dim_K7, etc.)
```

### Available Constants in GIFT.Core

| Category | Constants |
|----------|-----------|
| **Octonion-derived** | `imaginary_count`, `dim_G2`, `rank_G2`, `b2`, `b3`, `H_star`, `fund_E7` |
| **Exceptional Lie** | `dim_E8`, `rank_E8`, `dim_E8xE8`, `dim_E7`, `dim_E6`, `dim_F4` |
| **Geometry** | `dim_K7`, `dim_J3O`, `D_bulk` |
| **Topology** | `p2`, `det_g_num`, `det_g_den`, `kappa_T_den` |
| **Weyl Group** | `Weyl_factor`, `Weyl_sq`, `weyl_E8_order` |
| **Standard Model** | `dim_SU3`, `dim_SU2`, `dim_U1`, `dim_SM_gauge` |
| **Primes** | `prime_6`, `prime_8`, `prime_11` |

## Version History

See [CHANGELOG.md](../CHANGELOG.md) for detailed version history.
