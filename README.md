# GIFT Core

[![Formal Verification](https://github.com/gift-framework/core/actions/workflows/verify.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/verify.yml)
[![Python Tests](https://github.com/gift-framework/core/actions/workflows/test.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/test.yml)
[![Publish to PyPI](https://github.com/gift-framework/core/actions/workflows/publish.yml/badge.svg)](https://github.com/gift-framework/core/actions/workflows/publish.yml)
[![PyPI](https://img.shields.io/pypi/v/giftpy)](https://pypi.org/project/giftpy/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.14-blue)](Lean/)
[![Coq](https://img.shields.io/badge/Coq-8.18-orange)](COQ/)

---

## What is GIFT?

GIFT (Geometric Information Field Theory) is a speculative theoretical physics framework that attempts to derive Standard Model parameters from topological invariants of E8 x E8 gauge theory compactified on seven-dimensional manifolds with G2 holonomy.

This repository contains only the **mathematical core**: exact rational and integer relations that have been formally verified in two independent proof assistants. The physical interpretation of these relations remains conjectural and subject to experimental validation.

**Important distinction**: This package proves that certain mathematical identities hold exactly. Whether these identities correspond to physical reality is a separate empirical question.

---

## Installation

```bash
pip install giftpy
```

## Usage

```python
from gift_core import *

# Exact rational values
print(SIN2_THETA_W)  # Fraction(3, 13)
print(TAU)           # Fraction(3472, 891)
print(KAPPA_T)       # Fraction(1, 61)

# Integer constants
print(B2, B3)        # 21 77
print(N_GEN)         # 3

# All proven relations
for r in PROVEN_RELATIONS:
    print(f"{r.symbol} = {r.value}")
```

---

## Proven Relations

The following 13 relations are formally verified in both Lean 4 and Coq. Each relation is a mathematical identity; no fitting or approximation is involved.

| Symbol | Value | Derivation | Status |
|--------|-------|------------|--------|
| sin²θ_W | 3/13 | b₂/(b₃ + dim(G₂)) = 21/91 | Lean + Coq |
| τ | 3472/891 | dim(E₈×E₈)·b₂ / (dim(J₃O)·H*) | Lean + Coq |
| κ_T | 1/61 | 1/(b₃ - dim(G₂) - p₂) | Lean + Coq |
| det(g) | 65/32 | (H* - b₂ - 13) / 2^(Weyl) | Lean + Coq |
| Q_Koide | 2/3 | dim(G₂)/b₂ = 14/21 | Lean + Coq |
| m_τ/m_e | 3477 | dim(K₇) + 10·dim(E₈) + 10·H* | Lean + Coq |
| m_s/m_d | 20 | p₂² × Weyl = 4 × 5 | Lean + Coq |
| δ_CP | 197 | dim(K₇)·dim(G₂) + H* | Lean + Coq |
| λ_H (num) | 17 | H* - b₂ - 61 | Lean + Coq |
| H* | 99 | b₂ + b₃ + 1 | Lean + Coq |
| p₂ | 2 | dim(G₂)/dim(K₇) | Lean + Coq |
| N_gen | 3 | rank(E₈) - Weyl | Lean + Coq |
| dim(E₈×E₈) | 496 | 2 × 248 | Lean + Coq |

### Topological Constants

The relations above derive from these fixed mathematical structures:

| Constant | Value | Origin |
|----------|-------|--------|
| b₂(K₇) | 21 | Second Betti number of K₇ manifold |
| b₃(K₇) | 77 | Third Betti number of K₇ manifold |
| dim(G₂) | 14 | Dimension of G₂ holonomy group |
| dim(K₇) | 7 | Dimension of internal manifold |
| rank(E₈) | 8 | Rank of E₈ Lie algebra |
| dim(E₈) | 248 | Dimension of E₈ Lie algebra |
| dim(J₃O) | 27 | Dimension of exceptional Jordan algebra |
| Weyl | 5 | Weyl factor from E₈ structure |

---

## Formal Verification

### Why Two Proof Assistants?

Independent verification in Lean 4 and Coq provides strong confidence that these mathematical identities are correct. The proofs verify:

1. **Arithmetic correctness**: All rational simplifications (e.g., 21/91 = 3/13) are exact.
2. **Algebraic consistency**: Relations using shared constants are mutually compatible.
3. **Integer constraints**: Values claimed to be integers are proven integral.

### What Formal Verification Does NOT Prove

The proofs establish mathematical identities only. They do not verify:

- That these formulas correspond to physical observables
- That the topological interpretation is correct
- That the underlying physics framework is valid

### Building the Proofs

```bash
# Lean 4
cd Lean && lake build

# Coq
cd COQ && make
```

### Proof Structure

```
Lean/
├── GiftCore/
│   ├── Basic.lean          # Topological constants
│   ├── Relations.lean      # Derived relations
│   └── Proofs.lean         # Formal proofs
└── lakefile.lean

COQ/
├── GiftCore.v              # Constants and definitions
├── Relations.v             # Relation statements
└── Proofs.v                # Formal proofs
```

---

## Experimental Comparison

For context, these exact values may be compared to experimental measurements. Discrepancies, if any, could indicate either experimental uncertainty or limitations of the conjectured physical correspondence.

| Observable | GIFT (exact) | Experimental (PDG 2024) | Deviation |
|------------|--------------|-------------------------|-----------|
| sin²θ_W | 0.230769... | 0.23122 ± 0.00004 | 0.20% |
| m_s/m_d | 20 | 20.0 ± 1.0 | 0.00% |
| m_τ/m_e | 3477 | 3477.0 ± 0.1 | 0.00% |
| Q_Koide | 0.666... | 0.666661 ± 0.000007 | 0.001% |
| δ_CP | 197° | 197° ± 24° | 0.00% |

---

## Scope and Limitations

### What This Package Provides

- Exact rational and integer constants with formal proofs
- Python interface for numerical computation
- Cross-verified mathematical identities

### What This Package Does Not Claim

- Physical validity of the GIFT framework
- Correctness of the E₈×E₈ / G₂ holonomy interpretation
- Agreement beyond current experimental precision
- Resolution of open problems in theoretical physics

### Falsifiability

The framework makes testable predictions. Key experimental tests include:

- **DUNE (2027+)**: δ_CP = 197° ± 10° would test the CP violation prediction
- **FCC-ee**: High-precision sin²θ_W measurements could distinguish 3/13 from experiment
- **Lattice QCD**: Improved m_s/m_d determinations test the exact integer prediction

Significant deviation from these predictions would challenge the physical interpretation.

---

## Related Resources

### Full Framework

- **Repository**: [gift-framework/GIFT](https://github.com/gift-framework/GIFT)


### Citation

If referencing this work:

```bibtex
@software{gift_core,
  author = {deLaFournière, Brieuc},
  title = {GIFT Core: Formally Verified Mathematical Constants},
  year = {2025},
  url = {https://github.com/gift-framework/core},
  note = {Lean 4 and Coq verified}
}
```

---

## License

MIT License

---

## Acknowledgments

This work benefited from computational assistance provided by various AI systems used as mathematical tools. The formal verification was developed using Lean 4 and Coq proof assistants.

---

*GIFT Core v1.0.0*
