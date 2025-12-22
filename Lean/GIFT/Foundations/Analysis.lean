-- GIFT Foundations Analysis Aggregator
-- Bundles all Analysis submodules for convenient import
--
-- Usage:
--   import GIFT.Foundations.Analysis
-- instead of:
--   import GIFT.Foundations.Analysis.InnerProductSpace
--   import GIFT.Foundations.Analysis.ExteriorAlgebra
--   ...etc (8 imports)

import GIFT.Foundations.Analysis.InnerProductSpace
import GIFT.Foundations.Analysis.ExteriorAlgebra
import GIFT.Foundations.Analysis.E8Lattice
import GIFT.Foundations.Analysis.WedgeProduct
import GIFT.Foundations.Analysis.HodgeTheory
import GIFT.Foundations.Analysis.HarmonicForms
import GIFT.Foundations.Analysis.G2TensorForm
import GIFT.Foundations.Analysis.JoyceAnalytic

namespace GIFT.Foundations.Analysis

/-!
# Analysis Module Overview

This module collects advanced analytical foundations for GIFT:

## Inner Product Spaces (InnerProductSpace.lean)
- ℝ⁷ and ℝ⁸ inner product formalization
- Norm and orthogonality

## Exterior Algebra (ExteriorAlgebra.lean)
- Λᵏ(V) construction
- Wedge product properties

## E₈ Lattice (E8Lattice.lean)
- Lattice vectors and closure
- Weyl reflections

## Wedge Product (WedgeProduct.lean)
- Concrete wedge computations
- Basis elements

## Hodge Theory (HodgeTheory.lean)
- Hodge star operator *
- Harmonic forms ker(Δ)

## Harmonic Forms (HarmonicForms.lean)
- H^k(M) spaces
- Hodge decomposition

## G₂ Tensor Form (G2TensorForm.lean)
- Associative 3-form φ₀
- G₂ structure on ℝ⁷

## Joyce Analytic (JoyceAnalytic.lean)
- Analytic framework for Joyce theorem
- Perturbation estimates
-/

-- Note: This module bundles imports only. Access definitions via their
-- original namespaces, e.g., GIFT.Foundations.Analysis.HodgeTheory.*

end GIFT.Foundations.Analysis
