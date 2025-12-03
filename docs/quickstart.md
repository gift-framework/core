# Quick Start

## Basic Usage

### Import the Module

```python
from gift_core import *
```

Or import specific items:

```python
from gift_core import SIN2_THETA_W, TAU, DELTA_CP
```

### Access Constants

All topological inputs:

```python
from gift_core import (
    DIM_E8,      # 248
    RANK_E8,     # 8
    DIM_E8XE8,   # 496
    B2,          # 21
    B3,          # 77
    DIM_G2,      # 14
    DIM_J3O,     # 27
    H_STAR,      # 99
)
```

### Access Derived Relations

```python
from gift_core import (
    SIN2_THETA_W,  # Fraction(3, 13)
    TAU,           # Fraction(3472, 891)
    DET_G,         # Fraction(65, 32)
    KAPPA_T,       # Fraction(1, 61)
    DELTA_CP,      # 197
    M_TAU_M_E,     # 3477
    M_S_M_D,       # 20
    Q_KOIDE,       # Fraction(2, 3)
    LAMBDA_H_NUM,  # 17
    P2,            # 2
    N_GEN,         # 3
)
```

## Working with Fractions

Constants that are rational numbers are represented as `fractions.Fraction`:

```python
from gift_core import SIN2_THETA_W

# Exact representation
print(SIN2_THETA_W)              # 3/13
print(SIN2_THETA_W.numerator)    # 3
print(SIN2_THETA_W.denominator)  # 13

# Convert to float
print(float(SIN2_THETA_W))       # 0.23076923076923078

# Arithmetic preserves exactness
result = SIN2_THETA_W * 13
print(result)                     # 3
```

## Iterating Over Relations

```python
from gift_core import PROVEN_RELATIONS

for rel in PROVEN_RELATIONS:
    print(f"{rel.name}")
    print(f"  Symbol: {rel.symbol}")
    print(f"  Value:  {rel.value}")
    print(f"  Formula: {rel.formula}")
    print()
```

## Verification Status

Check which relations are formally verified:

```python
from gift_core import PROVEN_RELATIONS

# All relations are proven in both Lean 4 and Coq
for rel in PROVEN_RELATIONS:
    print(f"{rel.symbol}: Lean={rel.lean_proven}, Coq={rel.coq_proven}")
```

## Example: Computing Observables

```python
from gift_core import *

# Weinberg angle
sin2_theta_w = B2 / (B3 + DIM_G2)
print(f"sin²θ_W = {B2}/{B3 + DIM_G2} = {sin2_theta_w}")
# Output: sin²θ_W = 21/91 = 3/13

# Hierarchy parameter
tau = (DIM_E8XE8 * B2) / (DIM_J3O * H_STAR)
print(f"τ = ({DIM_E8XE8} × {B2})/({DIM_J3O} × {H_STAR}) = {tau}")
# Output: τ = (496 × 21)/(27 × 99) = 3472/891

# CP violation phase
delta_cp = 7 * DIM_G2 + H_STAR
print(f"δ_CP = 7 × {DIM_G2} + {H_STAR} = {delta_cp}°")
# Output: δ_CP = 7 × 14 + 99 = 197°
```

## Example: Comparison with Experiment

```python
from gift_core import SIN2_THETA_W, DELTA_CP

# Experimental values (PDG 2024)
sin2_exp = 0.23122  # ± 0.00003
delta_exp = 197     # ± 24°

# GIFT predictions
sin2_gift = float(SIN2_THETA_W)  # 0.23077

# Deviation
deviation = abs(sin2_gift - sin2_exp) / sin2_exp * 100
print(f"sin²θ_W deviation: {deviation:.2f}%")
# Output: sin²θ_W deviation: 0.19%

print(f"δ_CP: GIFT = {DELTA_CP}°, Exp = {delta_exp}° ± 24°")
# Output: δ_CP: GIFT = 197°, Exp = 197° ± 24°
```

## Next Steps

- [API Reference](api/constants.md): Complete list of all constants
- [Formal Proofs](proofs/overview.md): How the relations are verified
- [Theory Background](theory/background.md): Mathematical foundations
