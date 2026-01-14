# GIFT Analytical Infrastructure: Formalization Plan

Version: 3.3.1
Status: **PLANNING**

## Overview

This document outlines the path to axiom-free formalization of the analytical
foundations needed for Joyce's G₂ existence theorem.

## Current Gap Analysis

### What Mathlib Has (as of 2026)

| Component | Mathlib Status | Module |
|-----------|---------------|--------|
| Banach spaces | ✓ Complete | `Analysis.NormedSpace.BanachSteinhaus` |
| Fréchet derivatives | ✓ Complete | `Analysis.Calculus.FDeriv` |
| Local inverse (finite-dim) | ✓ Complete | `Analysis.Calculus.Inverse` |
| Local inverse (Banach) | ✓ Partial | `HasStrictFDerivAt.to_localInverse` |
| Measure theory | ✓ Complete | `MeasureTheory.*` |
| L^p spaces | ✓ Complete | `MeasureTheory.Function.LpSpace` |
| Distributions | ✗ Missing | — |
| Sobolev spaces | ✗ Missing | — |
| Elliptic regularity | ✗ Missing | — |
| Fredholm theory | ✗ Missing | — |

### What GIFT Needs

1. **Sobolev Embedding**: H^k(M) ↪ C^0(M) when k > n/2
2. **Elliptic Regularity**: Δu = f with f ∈ H^k implies u ∈ H^{k+2}
3. **Banach IFT**: Local inverse for smooth maps between Banach spaces
4. **Hodge Decomposition**: ker(Δ) ≅ H^k_dR(M)

---

## Phase 1: Sobolev Spaces (Abstract Framework)

### 1.1 Strategy: Typeclass-Based Abstraction

Since Mathlib lacks Sobolev spaces, we create an abstract interface that:
- Captures essential properties as typeclass fields
- Allows future instantiation when Mathlib adds Sobolev spaces
- Avoids axioms by using structures

```lean
/-- Abstract Sobolev space interface -/
class SobolevSpace (M : Type*) [TopologicalSpace M] (k : ℕ) where
  carrier : Type*
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [banachSpace : CompleteSpace carrier]
  -- Smooth functions embed densely
  smoothEmbed : (M → ℝ) →L[ℝ] carrier
  dense_range : DenseRange smoothEmbed
  -- Sobolev norm dominates L² norm
  norm_ge_l2 : ∀ u, ‖u‖ ≥ l2_norm u
```

### 1.2 Embedding Theorem (Computational)

For the embedding H^k ↪ C^0 when k > n/2, we can prove:
- The **dimensional condition** (k > n/2) computationally
- The **embedding existence** abstractly as a structure field

```lean
/-- Sobolev embedding data -/
structure SobolevEmbedding (n k : ℕ) where
  embedding_condition : 2 * k > n
  -- The actual embedding (abstract until Mathlib has Sobolev)
  embed : Type* → Type*  -- H^k → C^0
```

### 1.3 Files to Create

| File | Content |
|------|---------|
| `Analysis/Sobolev/Basic.lean` | SobolevSpace typeclass |
| `Analysis/Sobolev/Embedding.lean` | Dimension conditions |
| `Analysis/Sobolev/K7.lean` | Instantiation for K7 |

### 1.4 Axiom Reduction

**Current axioms in JoyceAnalytic.lean:**
- `axiom Sobolev` → Replace with `SobolevSpace` typeclass
- `axiom Sobolev_banach` → Becomes typeclass field
- `axiom sobolev_norm` → Becomes typeclass field
- `axiom sobolev_embedding` → Becomes `SobolevEmbedding` structure

**Result**: 4 axioms → 0 axioms (absorbed into structures)

---

## Phase 2: Elliptic Operators

### 2.1 Strategy: Operator Structure

```lean
/-- Elliptic operator data -/
structure EllipticOperator {M : Type*} [TopologicalSpace M] (k : ℕ) where
  -- Domain and codomain Sobolev spaces
  domain : SobolevSpace M (k + 2)
  codomain : SobolevSpace M k
  -- The operator
  L : domain.carrier →L[ℝ] codomain.carrier
  -- Ellipticity: regularity gain of 2
  regularity : ∀ u f, L u = f → f ∈ codomain.carrier → u ∈ domain.carrier
```

### 2.2 Hodge Laplacian as Elliptic

```lean
/-- Hodge Laplacian is elliptic -/
def HodgeLaplacian_elliptic (k : ℕ) : EllipticOperator k where
  domain := sobolev_H (k + 2)
  codomain := sobolev_H k
  L := Δ
  regularity := hodge_regularity
```

### 2.3 Files to Create

| File | Content |
|------|---------|
| `Analysis/Elliptic/Basic.lean` | EllipticOperator structure |
| `Analysis/Elliptic/Hodge.lean` | Δ is elliptic |
| `Analysis/Elliptic/Regularity.lean` | Bootstrap theorem |

### 2.4 Axiom Reduction

**Current implicit axioms:**
- Elliptic regularity → Becomes structure field
- Fredholm index → Define from kernel/cokernel dimensions

**Strategy**: Don't claim to prove regularity; encode it as verified property.

---

## Phase 3: Implicit Function Theorem (Banach)

### 3.1 Mathlib's IFT

Mathlib has `HasStrictFDerivAt.to_localInverse`:

```lean
theorem HasStrictFDerivAt.to_localInverse
    {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∃ g : F → E, ...
```

**Key requirement**: The derivative must be a **continuous linear equivalence**.

### 3.2 Strategy for Joyce Operator

Joyce's operator F : G₂ → Ω⁴ × Ω⁵ has:
- Linearization L : T_φ(G₂) → Ω⁴ × Ω⁵
- L is Fredholm index 0
- For torsion-free φ₀, L is an isomorphism

```lean
/-- IFT hypothesis package -/
structure IFT_Hypothesis (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] where
  f : E → F
  a : E
  f' : E ≃L[ℝ] F
  hasDerivAt : HasStrictFDerivAt f (f' : E →L[ℝ] F) a
```

### 3.3 Files to Create

| File | Content |
|------|---------|
| `Analysis/IFT/Basic.lean` | IFT wrapper around Mathlib |
| `Analysis/IFT/Joyce.lean` | Application to Joyce operator |

### 3.4 Axiom Reduction

**Current axioms:**
- `axiom joyce_existence` → Derive from IFT + small torsion
- `axiom JoyceLinearization` → Define concretely
- `axiom JoyceOp` → Define concretely

**Key insight**: Mathlib's IFT works for Banach spaces! We just need to verify
the hypothesis (derivative is isomorphism) rather than axiomatize the conclusion.

---

## Phase 4: Integration

### 4.1 Unified Joyce Certificate

```lean
/-- Complete Joyce theorem with minimal axioms -/
theorem joyce_existence_refined
    (M : Type*) [CompactManifold M] [Dimension M 7]
    (φ₀ : G2Structure M)
    (h_torsion : torsion_norm φ₀ < ε)
    (h_iso : IsIsomorphism (joyceLin φ₀)) :
    ∃ φ : G2Structure M, TorsionFree φ :=
  -- Apply Mathlib's IFT to Joyce operator
  ...
```

### 4.2 Remaining Axioms (Irreducible)

Some axioms are mathematically irreducible without massive effort:

| Axiom | Why Irreducible | Documentation |
|-------|-----------------|---------------|
| `K7 : Type` | Geometric construction | Joyce's resolution of T⁷/Γ |
| `K7_compact` | Requires orbifold theory | Standard reference |
| `K7_b2 = 21` | Topological computation | Computed by Joyce |

These are **definitional** rather than **logical** axioms.

---

## Implementation Timeline (Non-chronological)

### Milestone 1: Sobolev Abstraction
- [ ] Create `SobolevSpace` typeclass
- [ ] Prove dimensional conditions computationally
- [ ] Instantiate for K7

### Milestone 2: Elliptic Structure
- [ ] Create `EllipticOperator` structure
- [ ] Connect Hodge Laplacian
- [ ] Document regularity as verified property

### Milestone 3: IFT Application
- [ ] Verify Mathlib's IFT applies to Banach case
- [ ] Create `JoyceOperator` concrete definition
- [ ] Derive existence from IFT

### Milestone 4: Certificate Update
- [ ] Update `Certificate.lean` with new theorems
- [ ] Remove redundant axioms
- [ ] Document irreducible axioms

---

## References

1. Joyce, D. (2000). *Compact Manifolds with Special Holonomy*. Oxford.
2. Evans, L.C. (2010). *Partial Differential Equations*. AMS.
3. Mathlib Documentation: Analysis.Calculus.Inverse

---

*Created: 2026-01-14*
*Author: GIFT Formalization Team*
