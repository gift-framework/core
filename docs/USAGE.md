# giftpy Usage Guide

Complete documentation for the `giftpy` Python package (v3.2.13).

## Installation

```bash
pip install giftpy
```

For visualization (optional):
```bash
pip install giftpy matplotlib numpy
```

## Quick Start (v3.2)

```python
from gift_core import *

# Certified constants
print(SIN2_THETA_W)      # Fraction(3, 13)
print(B2, B3, H_STAR)    # 21, 77, 99 (all DERIVED from TCS!)

# E8 root system (240 actual vectors in R^8)
from gift_core.roots import E8_ROOTS, E8_SIMPLE_ROOTS
print(len(E8_ROOTS))     # 240

# Fano plane / G2 cross product
from gift_core.fano import cross_product, FANO_LINES
u = (1, 0, 0, 0, 0, 0, 0)
v = (0, 1, 0, 0, 0, 0, 0)
print(cross_product(u, v))  # 7D cross product

# Verify all relations
from gift_core import verify
print(verify())          # True
```

## New in v3.2.13

### GitHub Pages Blueprint Update

The blueprint visualization has been streamlined:
- **50+ observables** with **0.24% mean deviation** (updated from 0.087%)
- Dependency graph reduced by 14 nodes (cleaner visualization)
- Orphan nodes connected, redundant clusters merged

## New in v3.2.12

### Extended Observables (Lean 4)

Complete formalization of 22+ physical observables in `GIFT.Observables`:

```lean
import GIFT.Observables

-- Electroweak
#check Observables.sin2_theta_W           -- 3/13
#check Observables.sin2_theta_W_primary   -- b₂/(b₃+dim_G₂) = 3/13

-- PMNS Neutrino Mixing
#check Observables.sin2_theta12           -- 4/13
#check Observables.sin2_theta23           -- 6/11
#check Observables.sin2_theta13           -- 11/496

-- Quark Masses
#check Observables.m_s_over_m_d           -- 20
#check Observables.m_b_over_m_t           -- 1/42 (THE 42!)

-- Boson Masses
#check Observables.m_H_over_m_W           -- 81/52
#check Observables.m_Z_over_m_W           -- 11/10

-- CKM Matrix
#check Observables.sin2_theta12_CKM       -- 56/248 = 7/31
#check Observables.A_Wolf                 -- 83/99

-- Cosmology
#check Observables.Omega_DM_over_Omega_b  -- 43/8 (contains the 42!)
#check Observables.reduced_hubble         -- 167/248
#check Observables.sigma_8                -- 17/21
```

### The 42 Universality

The Euler characteristic χ(K₇) = 42 appears in two independent domains:

```lean
-- In particle physics: m_b/m_t = 1/42
theorem m_b_over_m_t_primary :
    (Core.b0 : ℚ) / Core.chi_K7 = 1 / 42 := ...

-- In cosmology: Ω_DM/Ω_b = (1 + 42)/8 = 43/8
theorem Omega_DM_primary :
    (Core.b0 + Core.chi_K7 : ℚ) / Core.rank_E8 = 43 / 8 := ...
```

---

## New in v3.2.10

### Tau Structural Derivation

The hierarchy parameter τ is now **derived** from framework invariants:

```python
from gift_core import TAU, DIM_E8xE8, B2, DIM_J3O, H_STAR

# τ = dim(E₈×E₈) × b₂ / (dim(J₃(𝕆)) × H*)
#   = 496 × 21 / (27 × 99) = 3472/891
tau_num = DIM_E8xE8 * B2      # 496 × 21 = 10416
tau_den = DIM_J3O * H_STAR    # 27 × 99 = 2673
# Reduced: 10416/2673 = 3472/891

print(float(TAU))  # 3.8967...
```

### E-Series Jordan Algebra

The Jordan algebra dimension **emerges** from the E-series:

```python
from gift_core import (
    DIM_E8, DIM_E6, DIM_SU3, DIM_J3O,
    E_SERIES_DIFF, J3O_FROM_E_SERIES
)

# dim(J₃(𝕆)) = (dim(E₈) - dim(E₆) - dim(SU₃)) / 6
#            = (248 - 78 - 8) / 6 = 162 / 6 = 27
print(E_SERIES_DIFF)       # 162
print(J3O_FROM_E_SERIES)   # 27
assert J3O_FROM_E_SERIES == DIM_J3O
```

### Numerical Observations

Approximate relations with computed deviations:

```python
from gift_core import verify_numerical_observations, get_numerical_summary

# Get all observations
obs = verify_numerical_observations()
print(obs['tau_powers'])  # τ², τ³, τ⁴, τ⁵ bounds

# Summary with deviations
summary = get_numerical_summary()
print(summary['tau^5'])
# {'computed': 898.48, 'target': 900, 'deviation_percent': 0.17, ...}

# Key observations:
# - τ⁴ ≈ 231 = N_gen × b₃ (0.19% deviation)
# - τ⁵ ≈ 900 = h(E₈)² (0.17% deviation)
# - τ ≈ 8γ^(5π/12) (0.0045% deviation)
```

### Exceptional Ranks Sum

```python
from gift_core import (
    RANK_E8, RANK_E7, RANK_E6, RANK_F4, RANK_G2,
    EXCEPTIONAL_RANKS_SUM, DIM_J3O
)

# Sum of exceptional Lie algebra ranks = 27 = dim(J₃(𝕆))
print(RANK_E8 + RANK_E7 + RANK_E6 + RANK_F4 + RANK_G2)  # 8+7+6+4+2 = 27
assert EXCEPTIONAL_RANKS_SUM == DIM_J3O
```

---

## New in v3.2

### E8 Root System

The 240 roots of E8 as actual vectors in ℝ⁸:

```python
from gift_core.roots import (
    E8_ROOTS,           # All 240 roots
    D8_ROOTS,           # 112 integer roots (±eᵢ ± eⱼ)
    HALF_INTEGER_ROOTS, # 128 half-integer roots
    E8_SIMPLE_ROOTS,    # 8 simple roots (Bourbaki)
    E8_CARTAN_MATRIX,   # 8×8 Cartan matrix
)

# Root operations
from gift_core.roots import (
    inner_product,      # ⟨u, v⟩
    norm, norm_sq,      # ‖v‖, ‖v‖²
    weyl_reflection,    # Weyl reflection s_α(v)
    is_root,            # Check if vector is a root
    is_in_E8_lattice,   # Check lattice membership
    positive_roots,     # 120 positive roots
    highest_root,       # θ = 2α₁ + 3α₂ + ...
)

# Example: Simple roots (Bourbaki convention)
print(E8_SIMPLE_ROOTS[0])  # (1, -1, 0, 0, 0, 0, 0, 0) = α₁
print(E8_SIMPLE_ROOTS[7])  # (-0.5, -0.5, ...) = α₈

# Statistics
from gift_core.roots import root_statistics
stats = root_statistics()
print(stats)
# {'total_roots': 240, 'd8_roots': 112, 'half_integer_roots': 128,
#  'coxeter_number': 30, 'weyl_group_order': 696729600, ...}
```

### Fano Plane & G2 Cross Product

The Fano plane encodes octonion multiplication and G₂ structure:

```python
from gift_core.fano import (
    FANO_LINES,         # 7 lines, each with 3 points
    epsilon,            # Structure constants ε(i,j,k)
    cross_product,      # G2-invariant cross product in R^7
    phi0,               # Associative 3-form
)

# The 7 lines of the Fano plane
print(FANO_LINES)
# [(0,1,3), (1,2,4), (2,3,5), (3,4,6), (4,5,0), (5,6,1), (6,0,2)]

# Epsilon tensor: ε(i,j,k) = ±1 or 0
print(epsilon(0, 1, 3))  # +1 (cyclic order on line)
print(epsilon(1, 0, 3))  # -1 (antisymmetric)

# G2 cross product in R^7
u = (1, 0, 0, 0, 0, 0, 0)
v = (0, 1, 0, 0, 0, 0, 0)
w = cross_product(u, v)
print(w)  # Result in R^7

# Verify Lagrange identity: ‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩²
from gift_core.fano import verify_lagrange_identity
print(verify_lagrange_identity(u, v))  # True

# Octonion multiplication (imaginary units)
from gift_core.fano import octonion_multiply_imaginaries
sign, result = octonion_multiply_imaginaries(0, 1)  # e₁ * e₂
print(f"e₁ × e₂ = {'+' if sign > 0 else '-'}e{result+1}")  # +e₄
```

### Verification Module

Check all GIFT relations programmatically:

```python
from gift_core import verify, verify_all, verify_summary

# Quick check
assert verify()  # True if all pass

# Detailed results
results = verify_all()
for r in results:
    print(f"{r.name}: {'✓' if r.passed else '✗'}")

# Summary
summary = verify_summary()
print(f"Passed: {summary['passed']}/{summary['total']}")
print(f"By category: {summary['by_category']}")

# Pretty report
from gift_core import print_verification_report
print_verification_report()
```

### Visualization (requires matplotlib)

```python
from gift_core.visualize import (
    plot_fano,          # Fano plane diagram
    plot_e8_projection, # E8 roots 2D projection
    plot_dynkin_e8,     # E8 Dynkin diagram
    plot_gift_constants,# Bar chart of constants
)

# Fano plane
plot_fano(save_path='fano.png')

# E8 roots (requires numpy)
plot_e8_projection(projection='random', save_path='e8.png')

# Dynkin diagram
plot_dynkin_e8(save_path='dynkin.png')

# All visualizations
from gift_core.visualize import plot_all
plot_all(save_dir='./figures/')
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

## TCS Construction (v3.2+)

K₇ Betti numbers are now **derived** from Twisted Connected Sum building blocks:

```python
from gift_core import *

# TCS Building Blocks (v3.2)
# M₁ = Quintic hypersurface in CP⁴
M1_B2 = 11  # b₂(M₁)
M1_B3 = 40  # b₃(M₁)

# M₂ = Complete Intersection (2,2,2) in CP⁶
M2_B2 = 10  # b₂(M₂)
M2_B3 = 37  # b₃(M₂)

# K₇ = M₁ #_TCS M₂ (Twisted Connected Sum)
B2 = M1_B2 + M2_B2  # 11 + 10 = 21 ✓
B3 = M1_B3 + M2_B3  # 40 + 37 = 77 ✓

# Both Betti numbers DERIVED from building blocks!
H_STAR = B2 + B3 + 1  # 99
```

### Structural Identities (v3.2)

```python
# Weyl Triple Identity: 3 independent paths to Weyl = 5
assert (DIM_G2 + 1) // N_GEN == WEYL_FACTOR      # 15 / 3 = 5
assert B2 // N_GEN - P2 == WEYL_FACTOR           # 21 / 3 - 2 = 5
assert DIM_G2 - RANK_E8 - 1 == WEYL_FACTOR       # 14 - 8 - 1 = 5

# PSL(2,7) = 168: Fano plane symmetry group
PSL27_ORDER = 168
assert (B3 + DIM_G2) + B3 == PSL27_ORDER         # 91 + 77 = 168
assert RANK_E8 * B2 == PSL27_ORDER               # 8 × 21 = 168
assert N_GEN * (B3 - B2) == PSL27_ORDER          # 3 × 56 = 168
```

## Algebraic Foundations (v3.1+)

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

v3.1+ **derives** them from octonion structure:
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

## Lean 4 Usage (v3.1+)

### GIFT.Core - Single Source of Truth

As of v3.1, use `GIFT.Core` for all GIFT constants:

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

## Blueprint Documentation

GIFT includes a LaTeX blueprint that generates an interactive dependency graph showing proof structure.

### Viewing the Blueprint

The blueprint is hosted at the project's GitHub Pages (if enabled), or can be built locally:

```bash
cd blueprint
pip install leanblueprint
leanblueprint build
# Open _build/html/index.html
```

### Blueprint Structure

The dependency graph shows how theorems and definitions connect:

| Chapter | Contents |
|---------|----------|
| **E8 Lattice** | AllInteger, SumEven, E8_lattice, reflect_preserves_lattice |
| **G2 Cross Product** | Fano plane, epsilon tensor, Lagrange identity |
| **Algebraic Foundations** | Octonions, G2, Betti numbers, H* |
| **SO(16) Decomposition** | dim_SO, spinor, geometric/spinorial parts |
| **Physical Relations** | Weinberg angle, Koide, fine structure, lepton masses |
| **Sequences** | Fibonacci F₃-F₁₂, Lucas L₀-L₉ embeddings |
| **Prime Atlas** | Tier 1 primes, Heegner numbers |
| **Moonshine** | Monster dimension, j-invariant |
| **McKay** | Coxeter number, binary icosahedral, E8 kissing |
| **Joyce Theorem** | PINN verification, torsion bounds, existence |
| **Explicit G2 Metric** | phi0, scale factor, torsion-free proof |

### Key Dependencies

The central hub is `def:H_star` (H* = b₂ + b₃ + 1 = 99), which connects to:
- Physical relations (mass ratios, coupling constants)
- Topological invariants (Betti numbers)
- Cosmological parameters (Ω_DE)

Other important hubs:
- `def:b2`, `def:b3` → Algebraic chain from octonions
- `def:fib`, `def:lucas` → Sequence embeddings
- `def:coxeter` → McKay correspondence
- `def:monster_dim` → Moonshine connections

## Version History

See [CHANGELOG.md](../CHANGELOG.md) for detailed version history.
