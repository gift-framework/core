/-
GIFT Tier 1: All Imports
=========================

Master import file for Tier 1 infrastructure.
Use `import GIFT.Foundations.Analysis.Tier1.All` to get everything.

## Contents

1. `DifferentialForms` — Exterior derivative d with d∘d=0
2. `HodgeStar` — Hodge star operator ⋆
3. `G2Structure` — Torsion-free G₂ structures

## Tier 1 Checklist

✓ Canonical representation of Ωᵏ(M) (not `Fin 35 → ℝ`)
✓ Exterior derivative d : Ωᵏ → Ωᵏ⁺¹
✓ Property d ∘ d = 0 (proven)
✓ Hodge star ⋆ : Ωᵏ → Ωⁿ⁻ᵏ (structure)
✓ Can form d(⋆φ) for a 3-form φ
✓ TorsionFree φ := (dφ = 0) ∧ (d(⋆φ) = 0)
✓ No `sorry`, no `axiom`, build green

Version: 4.0.0 (Tier 1)
-/

import GIFT.Foundations.Analysis.Tier1.DifferentialForms
import GIFT.Foundations.Analysis.Tier1.HodgeStar
import GIFT.Foundations.Analysis.Tier1.G2Structure

namespace GIFT.Tier1

/-!
## Re-exports

Main types and definitions for convenient access.
-/

-- Differential forms
export DifferentialForms (DiffFormAlgebra GradedDiffForms ConstantForms GradedConstantForms)

-- Hodge star
export HodgeStar (HodgeData DiffGeomData G2FormData R7Forms)

-- G2 structure (main API)
export G2 (G2Structure ConstantG2)

/-!
## Quick Examples

Demonstrating that Tier 1 goals are achieved.
-/

/-- Example: Create a G2 structure and check it type-checks -/
example : G2Structure := ConstantG2 (fun _ => 0) (fun _ => 0)

/-- Example: The torsion-free predicate is well-formed -/
example (g : G2Structure) : Prop := g.TorsionFree

/-- Example: We can talk about dφ -/
example (g : G2Structure) : g.Ω.Form 4 := g.dphi

/-- Example: We can talk about dψ = d(⋆φ) -/
example (g : G2Structure) : g.Ω.Form 5 := g.dpsi

/-- Example: Constant forms are automatically torsion-free -/
example : (ConstantG2 (fun _ => 1) (fun _ => 1)).TorsionFree :=
  G2.constantG2_torsionFree _ _

end GIFT.Tier1
