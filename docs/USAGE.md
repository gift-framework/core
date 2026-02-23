# giftpy Usage Guide

Complete documentation for the `giftpy` Python package (v3.3.24).

## Installation

```bash
pip install giftpy
```

For visualization (optional):
```bash
pip install giftpy matplotlib numpy
```

## Quick Start

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

# K7 topology (v3.3 corrected!)
from gift_core.topology import K7
print(K7.euler_characteristic)  # 0 (NOT 42!)
print(K7.two_b2)                # 42 (structural invariant)

# Verify all relations
from gift_core import verify
print(verify())          # True
```

## New in v3.3.24

### Ambrose-Singer Holonomy Diagnostics

New `AmbroseSinger.lean` formalizing the gap between torsion-free G₂ structures and G₂ holonomy:

```lean
import GIFT.Foundations.AmbroseSinger

-- so(7) = g₂ ⊕ g₂⊥ decomposition
#check so7_g2_decomposition         -- 21 = 14 + 7
#check dim_g2_complement_eq_dim_K7  -- dim(g₂⊥) = 7 = dim(K₇)
#check b2_holonomy_manifold_sum     -- b₂ = dim(g₂) + dim(K₇)

-- Holonomy rank gap (Phase 3 PINN: hol_rank=21, target=14)
#check holonomy_rank_gap            -- 21 - 14 = 7
#check as_constraints_per_point     -- 147 = 7 × 21

-- Master certificate (10 conjuncts, all proven)
#check ambrose_singer_certificate
```

**Key insight**: Torsion-free (nabla phi = 0) is NECESSARY but NOT SUFFICIENT for G₂ holonomy. The curvature must additionally lie in g₂ subset so(7) (Ambrose-Singer theorem).

### Axiom Classification (87/87 tagged)

All axioms now carry category labels:

| Category | Count | Description | Example |
|----------|-------|-------------|---------|
| A | ~5 | Definitions | `CompactManifold.volume_pos` |
| B | ~15 | Standard results | `cheeger_inequality` (Cheeger 1970) |
| C | ~25 | Geometric structure | `ProductNeckMetric` |
| D | ~8 | Literature axioms | `langlais_spectral_density` |
| E | ~12 | GIFT claims | `universality_conjecture` |
| F | ~22 | Numerically verified | `gamma_1_approx` |

---

## New in v3.3.23

### Certificate Modularization

The monolithic `Certificate.lean` (2281 lines) has been restructured into domain-organized sub-certificates:

```
GIFT/Certificate/
├── Core.lean         # Master: Foundations ∧ Predictions ∧ Spectral
├── Foundations.lean  # E₈, G₂, octonions, K₇, Joyce, conformal rigidity
├── Predictions.lean  # 33+ published relations, V5.0 observables, hierarchy
└── Spectral.lean     # Mass gap 14/99, TCS bounds, selection principle
```

**Lean 4 usage:**

```lean
-- Import the master certificate
import GIFT.Certificate.Core

-- Access sub-certificates
#check GIFT.Certificate.gift_master_certificate
-- : Foundations.statement ∧ Predictions.statement ∧ Spectral.statement

-- Or import individual pillars
import GIFT.Certificate.Predictions
#check GIFT.Certificate.Predictions.observables_certified
```

**Adding new relations:** Add imports and abbrevs to the appropriate sub-module (`Foundations.lean`, `Predictions.lean`, or `Spectral.lean`), then add conjuncts to its `def statement : Prop`.

**Backward compatibility:** `import GIFT.Certificate` still works and provides legacy aliases.

---

## Lean 4 Module Reference

### Core Constants

```lean
import GIFT.Core
open GIFT.Core

#check b2        -- 21
#check b3        -- 77
#check H_star    -- 99
#check dim_E8    -- 248
#check dim_G2    -- 14
#check dim_K7    -- 7
```

### Spectral Theory (v3.3.8+)

```lean
import GIFT.Spectral

-- Mass gap ratio (proven, no axioms!)
#check GIFT.Spectral.MassGapRatio.mass_gap_ratio_value       -- 14/99
#check GIFT.Spectral.MassGapRatio.mass_gap_ratio_irreducible -- gcd(14,99) = 1

-- Physical spectral gap (v3.3.17, zero axioms)
#check physical_gap_from_topology   -- 13/99 = (dim(G₂) - h) / H*
#check pell_equation                -- 99² - 50 × 14² = 1

-- TCS Bounds (v3.3.12)
#check tcs_spectral_bounds          -- c₁/L² ≤ λ₁ ≤ c₂/L²

-- Connes Bridge (v3.3.18)
#check connes_bridge_certificate    -- 19-conjunct master certificate
```

### Geometry (v3.3.4+, axiom-free)

```lean
import GIFT.Geometry

-- ψ = ⋆φ is a THEOREM, not an axiom!
#check HodgeStarR7.psi_eq_star_phi
#check HodgeStarCompute.hodgeStar_invol_3  -- ⋆⋆ = +1 PROVEN
#check HodgeStarR7.standardG2Geom_torsionFree
```

### Moonshine (v3.3.11)

```lean
import GIFT.Moonshine.MonsterCoxeter

-- Monster dimension from Coxeter numbers
#check monster_dim_coxeter_formula
-- (77-6) × (77-18) × (77-30) = 71 × 59 × 47 = 196883
```

---

## Python API

### Certified Constants

| Constant | Value | Description |
|----------|-------|-------------|
| `SIN2_THETA_W` | 3/13 | Weinberg angle |
| `TAU` | 3472/891 | Hierarchy parameter |
| `KAPPA_T` | 1/61 | Torsion parameter |
| `DET_G` | 65/32 | Metric determinant |
| `Q_KOIDE` | 2/3 | Koide formula |
| `H_STAR` | 99 | Topological invariant |
| `N_GEN` | 3 | Number of generations |
| `GAMMA_GIFT` | 511/884 | GIFT parameter |

### Topological Constants

```python
from gift_core import *

print(DIM_E8)      # 248
print(RANK_E8)     # 8
print(DIM_G2)      # 14
print(DIM_K7)      # 7
print(B2)          # 21
print(B3)          # 77
print(DIM_J3O)     # 27
print(WEYL_FACTOR) # 5
print(D_BULK)      # 11
```

### E8 Root System

```python
from gift_core.roots import E8_ROOTS, E8_SIMPLE_ROOTS, E8_CARTAN_MATRIX
from gift_core.roots import inner_product, weyl_reflection, root_statistics

print(len(E8_ROOTS))     # 240
stats = root_statistics()
print(stats['coxeter_number'])  # 30
```

### Fano Plane & G2 Cross Product

```python
from gift_core.fano import FANO_LINES, epsilon, cross_product, phi0

print(FANO_LINES)           # 7 lines, each with 3 points
print(epsilon(0, 1, 3))     # +1
print(cross_product(u, v))  # 7D result
```

### Verification

```python
from gift_core import verify, verify_all, print_verification_report

assert verify()           # True
print_verification_report()
```

### Joyce Existence

```python
from gift_core.analysis import JoyceCertificate, verify_pinn_bounds

assert verify_pinn_bounds()  # K7 admits torsion-free G2!
cert = JoyceCertificate.verify()
print(cert.safety_margin)    # ~20.4x
```

### K7 Metric Pipeline (requires numpy)

```python
import gift_core as gc

if gc.NUMPY_AVAILABLE:
    config = gc.PipelineConfig(neck_length=15.0, resolution=32, pinn_epochs=1000)
    result = gc.run_pipeline(config)
    print(f"det(g) = {result.det_g}")
```

---

## Building Proofs Locally

```bash
cd Lean && lake build
```

## Blueprint

```bash
cd blueprint
pip install leanblueprint
leanblueprint build
# Open _build/html/index.html
```

## Version History

See [CHANGELOG.md](../CHANGELOG.md) for detailed version history.
