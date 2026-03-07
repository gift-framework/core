/-
GIFT Mollified Sum Module
==========================

Master import for the mollified Dirichlet polynomial formalization.

This module formalizes the mollified Dirichlet polynomial S_w(T)
that approximates S(T) = π⁻¹ arg ζ(½+iT) on the critical line.
Reference: de La Fournière (2026).

## Architecture

The formalization follows a three-layer design:

### Layer B (this module): Constructive Core — ZERO AXIOMS
- `Mollifier`: Cosine-squared kernel w(x) = cos²(πx/2)
- `Sum`: Mollified Dirichlet polynomial S_w(T) as Finset.sum
- `Adaptive`: Adaptive cutoff θ(T) = θ₀ + θ₁/log T

### Layer A (future): Number Theory Foundations
- Zeta zero sequence (axiomatized, cf. GIFT.Zeta.Basic)
- Riemann-Siegel theta function (from Complex.logGamma)
- Riemann-von Mangoldt counting formula (axiom)
- Explicit formula (axiom, Iwaniec-Kowalski Ch.5)

### Layer C (future): Main Results
- 100% zero counting (numerical certificate)
- 98% zero localization
- R² = 0.939 variance explained
- Out-of-sample stability on 2M zeros

## Key Design Principle

The mollified sum S_w(T) is always a FINITE SUM because the
cosine-squared kernel has compact support. This eliminates all
convergence issues at the definitional level. The non-trivial
convergence analysis (§3.9 of the paper) concerns the
approximation quality S_w ≈ S as T → ∞, not the well-definedness
of S_w itself.

Version: 1.0.0
-/

import GIFT.MollifiedSum.Mollifier
import GIFT.MollifiedSum.Sum
import GIFT.MollifiedSum.Adaptive

namespace GIFT.MollifiedSum

open Mollifier Sum Adaptive

/-!
## Module Summary
-/

/-- Complete mollified sum module certificate. -/
theorem mollified_sum_certified :
    -- Mollifier kernel properties
    cosineKernel 0 = 1 ∧
    (∀ x, 0 ≤ cosineKernel x) ∧
    (∀ x, cosineKernel x ≤ 1) ∧
    -- Sum is well-defined
    (∀ T θ : ℝ, ∀ N K : ℕ, ∃ v : ℝ, S_mollified T θ N K = v) ∧
    -- Standard cutoff K = 3
    standardKMax = 3 :=
  ⟨cosineKernel_at_zero,
   cosineKernel_nonneg,
   cosineKernel_le_one,
   fun T θ N K => S_mollified_welldefined T θ N K,
   rfl⟩

end GIFT.MollifiedSum
