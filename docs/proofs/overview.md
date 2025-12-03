# Formal Proofs Overview

All 13 exact relations in GIFT are formally verified using proof assistants. This provides machine-checked guarantees that the mathematical relationships hold exactly.

## Why Formal Verification?

### Eliminating Human Error

Traditional mathematical proofs can contain subtle errors. Proof assistants mechanically verify every logical step, eliminating this possibility for the verified statements.

### Ensuring Logical Consistency

The proof assistants ensure that no hidden assumptions or circular reasoning are present in the derivations.

### Reproducibility

Anyone can run the proofs and verify the results independently.

## What Is Proven?

The formal proofs verify **arithmetic identities** such as:

- 21/91 = 3/13 ✓
- 496 × 21 / (27 × 99) = 3472/891 ✓
- 7 × 14 + 99 = 197 ✓

These are mathematical facts, not physical claims. The proofs do not verify that these relations correspond to physical reality—that requires experimental verification.

## Proof Assistants Used

### Lean 4

- **Version**: Lean 4.14.0
- **Library**: Mathlib 4.14.0
- **Modules**: 17
- **Theorems**: ~100
- **Sorry statements**: 0

[View Lean proofs →](lean.md)

### Coq

- **Version**: Coq 8.18+
- **Library**: Coq stdlib
- **Modules**: 21
- **Theorems**: ~100
- **Admitted statements**: 0

[View Coq proofs →](coq.md)

## Verification Status Summary

| Relation | Formula | Lean 4 | Coq |
|----------|---------|--------|-----|
| sin²θ_W = 3/13 | 21/91 | ✅ | ✅ |
| τ = 3472/891 | 496×21/(27×99) | ✅ | ✅ |
| det(g) = 65/32 | 5×13/32 | ✅ | ✅ |
| κ_T = 1/61 | 1/(77-14-2) | ✅ | ✅ |
| δ_CP = 197 | 7×14 + 99 | ✅ | ✅ |
| m_τ/m_e = 3477 | 7 + 2480 + 990 | ✅ | ✅ |
| m_s/m_d = 20 | 4×5 | ✅ | ✅ |
| Q_Koide = 2/3 | 14/21 | ✅ | ✅ |
| λ_H_num = 17 | 14+3 | ✅ | ✅ |
| H* = 99 | 21+77+1 | ✅ | ✅ |
| p₂ = 2 | 14/7 | ✅ | ✅ |
| N_gen = 3 | constraint | ✅ | ✅ |
| dim(E₈×E₈) = 496 | 2×248 | ✅ | ✅ |

## Running the Proofs

### Lean 4

```bash
cd Lean
lake build
```

Expected output:
```
Build completed successfully.
```

### Coq

```bash
cd COQ
make
```

Expected output:
```
COQC GIFT_Unified.v
All proofs verified.
```

## What Is NOT Proven

The formal proofs do **not** establish:

1. That E₈×E₈ is the correct gauge group for physics
2. That K₇ with these Betti numbers exists physically
3. That the cohomology-to-physics map is correct
4. That the predictions match experiment

These require physical arguments and experimental verification, not mathematical proof.

## Cross-Validation Value

Having proofs in two independent proof assistants (Lean 4 and Coq) provides:

- Different implementations catch different bugs
- Different type theories (both are sound)
- Community verification in both ecosystems
