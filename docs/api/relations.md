# Relations Reference

The `PROVEN_RELATIONS` list contains all 13 exact relations with metadata about their verification status.

## The Relation Class

Each relation is represented as a named tuple with the following fields:

```python
class Relation(NamedTuple):
    name: str           # Human-readable name
    symbol: str         # Mathematical symbol
    value: Any          # The value (int or Fraction)
    formula: str        # Derivation formula
    lean_proven: bool   # Verified in Lean 4
    coq_proven: bool    # Verified in Coq
```

## Accessing Relations

### Iterate Over All Relations

```python
from gift_core import PROVEN_RELATIONS

for rel in PROVEN_RELATIONS:
    print(f"{rel.symbol} = {rel.value}")
```

### Access by Index

```python
from gift_core import PROVEN_RELATIONS

weinberg = PROVEN_RELATIONS[0]
print(weinberg.name)     # "Weinberg angle"
print(weinberg.symbol)   # "sin²θ_W"
print(weinberg.value)    # Fraction(3, 13)
print(weinberg.formula)  # "b₂/(b₃ + dim G₂)"
```

### Filter Relations

```python
from gift_core import PROVEN_RELATIONS
from fractions import Fraction

# Get only fractional relations
fractional = [r for r in PROVEN_RELATIONS if isinstance(r.value, Fraction)]

# Get only integer relations
integer = [r for r in PROVEN_RELATIONS if isinstance(r.value, int)]
```

## Complete Relations List

### 1. Weinberg Angle

```python
Relation(
    name="Weinberg angle",
    symbol="sin²θ_W",
    value=Fraction(3, 13),
    formula="b₂/(b₃ + dim G₂) = 21/91",
    lean_proven=True,
    coq_proven=True
)
```

**Derivation**: The Weinberg angle emerges from the ratio of gauge field components.

$$\sin^2\theta_W = \frac{b_2}{b_3 + \dim G_2} = \frac{21}{77 + 14} = \frac{21}{91} = \frac{3}{13}$$

---

### 2. Hierarchy Parameter

```python
Relation(
    name="Hierarchy parameter",
    symbol="τ",
    value=Fraction(3472, 891),
    formula="(dim E₈×E₈ × b₂)/(dim J₃(𝕆) × H*)",
    lean_proven=True,
    coq_proven=True
)
```

**Derivation**:

$$\tau = \frac{\dim(E_8 \times E_8) \cdot b_2}{\dim(J_3(\mathbb{O})) \cdot H^*} = \frac{496 \times 21}{27 \times 99} = \frac{10416}{2673} = \frac{3472}{891}$$

---

### 3. Metric Determinant

```python
Relation(
    name="Metric determinant",
    symbol="det(g)",
    value=Fraction(65, 32),
    formula="(Weyl × 13)/32 = 5×13/32",
    lean_proven=True,
    coq_proven=True
)
```

---

### 4. Torsion Magnitude

```python
Relation(
    name="Torsion magnitude",
    symbol="κ_T",
    value=Fraction(1, 61),
    formula="1/(b₃ - dim G₂ - 2) = 1/(77-14-2)",
    lean_proven=True,
    coq_proven=True
)
```

---

### 5. CP Violation Phase

```python
Relation(
    name="CP violation phase",
    symbol="δ_CP",
    value=197,
    formula="7 × dim(G₂) + H* = 98 + 99",
    lean_proven=True,
    coq_proven=True
)
```

**Derivation**:

$$\delta_{CP} = 7 \cdot \dim(G_2) + H^* = 7 \times 14 + 99 = 98 + 99 = 197°$$

---

### 6. Tau-Electron Mass Ratio

```python
Relation(
    name="Tau-electron mass ratio",
    symbol="m_τ/m_e",
    value=3477,
    formula="dim(K₇) + 10×dim(E₈) + 10×H*",
    lean_proven=True,
    coq_proven=True
)
```

**Derivation**:

$$\frac{m_\tau}{m_e} = \dim(K_7) + 10 \cdot \dim(E_8) + 10 \cdot H^* = 7 + 2480 + 990 = 3477$$

---

### 7. Strange-Down Mass Ratio

```python
Relation(
    name="Strange-down mass ratio",
    symbol="m_s/m_d",
    value=20,
    formula="4 × Weyl = b₂ - 1",
    lean_proven=True,
    coq_proven=True
)
```

---

### 8. Koide Parameter

```python
Relation(
    name="Koide parameter",
    symbol="Q_Koide",
    value=Fraction(2, 3),
    formula="dim(G₂)/b₂ = 14/21",
    lean_proven=True,
    coq_proven=True
)
```

---

### 9. Higgs Coupling Numerator

```python
Relation(
    name="Higgs coupling numerator",
    symbol="λ_H_num",
    value=17,
    formula="dim(G₂) + N_gen = 14 + 3",
    lean_proven=True,
    coq_proven=True
)
```

---

### 10. Cohomological Dimension

```python
Relation(
    name="Cohomological dimension",
    symbol="H*",
    value=99,
    formula="b₂ + b₃ + 1 = 21 + 77 + 1",
    lean_proven=True,
    coq_proven=True
)
```

---

### 11. Binary Duality

```python
Relation(
    name="Binary duality",
    symbol="p₂",
    value=2,
    formula="dim(G₂)/dim(K₇) = 14/7",
    lean_proven=True,
    coq_proven=True
)
```

---

### 12. Generation Number

```python
Relation(
    name="Generation number",
    symbol="N_gen",
    value=3,
    formula="Unique solution to (rank E₈ + N)×b₂ = N×b₃",
    lean_proven=True,
    coq_proven=True
)
```

---

### 13. E₈×E₈ Dimension

```python
Relation(
    name="E8×E8 dimension",
    symbol="dim(E₈×E₈)",
    value=496,
    formula="2 × dim(E₈) = 2 × 248",
    lean_proven=True,
    coq_proven=True
)
```

## Verification Status

All 13 relations are proven in both proof assistants:

```python
from gift_core import PROVEN_RELATIONS

lean_count = sum(1 for r in PROVEN_RELATIONS if r.lean_proven)
coq_count = sum(1 for r in PROVEN_RELATIONS if r.coq_proven)

print(f"Lean 4: {lean_count}/13 proven")  # 13/13
print(f"Coq:    {coq_count}/13 proven")   # 13/13
```
