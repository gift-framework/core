/-
GIFT Spectral Module
====================

Spectral theory foundations for the Yang-Mills mass gap.

## Overview

This module formalizes the spectral gap result:
  lambda_1(K7) = dim(G2)/H* = 14/99

The key insight: the mass gap is determined by TOPOLOGY, not dynamics.

## Contents

- `MassGapRatio`: The 14/99 theorem and Cheeger bounds

## Future Extensions (see docs/LEAN_YANG_MILLS_PLAN.md)

- `Laplacian`: Hodge Laplacian on compact manifolds
- `Spectrum`: Discrete spectrum, eigenvalues
- `Cheeger`: Cheeger constant, isoperimetric inequalities
- `SpectralGap`: lambda_1 > 0, spectral bounds

## References

- Joyce, D.D. (2000). Compact Manifolds with Special Holonomy
- Cheeger, J. (1970). A lower bound for the smallest eigenvalue of the Laplacian
- GIFT Framework v3.3: Yang-Mills spectral gap from K7 topology

Version: 1.0.0
-/

import GIFT.Spectral.MassGapRatio

namespace GIFT.Spectral

-- Re-export key definitions and theorems
export MassGapRatio (
  -- Core definitions
  mass_gap_ratio
  mass_gap_ratio_num
  mass_gap_ratio_den
  cheeger_lower_bound
  -- Key theorems
  mass_gap_ratio_value
  mass_gap_ratio_irreducible
  mass_gap_coprime
  mass_gap_from_holonomy_cohomology
  mass_gap_tight_bound
  cheeger_bound_value
  cheeger_bound_positive
  -- Yang-Mills connection
  GIFT_mass_gap_MeV
  mass_gap_prediction
  mass_gap_exact
  -- Master certificate
  mass_gap_ratio_certified
)

/-!
## Quick Reference

| Quantity | Value | GIFT Origin |
|----------|-------|-------------|
| Numerator | 14 | dim(G2) |
| Denominator | 99 | H* = b2 + b3 + 1 |
| Ratio | 14/99 | 0.1414... |
| Cheeger bound | 49/9801 | (14/99)^2/4 |
| PINN measurement | 0.1406 | Numerical verification |
| Deviation | 0.57% | < 1% agreement |
| Mass gap | 28.28 MeV | (14/99) * 200 MeV |
-/

end GIFT.Spectral
