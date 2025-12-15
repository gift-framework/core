import GIFT.Core

/-!
# GIFT Topology Module (DEPRECATED)

⚠️ **DEPRECATED**: Use `import GIFT.Core` instead.

This module is maintained for backward compatibility only.
All constants are now re-exported from `GIFT.Core`.

## Migration Guide

Replace:
```lean
import GIFT.Topology
open GIFT.Topology
```

With:
```lean
import GIFT.Core
open GIFT.Core
```

## Why the change?

`GIFT.Core` provides a single source of truth for all GIFT constants.
The Betti numbers are now derived from octonion structure:
- b₂ = C(7,2) = 21 (from imaginary unit pairs)
- b₃ = b₂ + fund(E₇) = 77
- H* = b₂ + b₃ + 1 = 99

See `GIFT.Algebraic.BettiNumbers` for the derivation.
-/

namespace GIFT.Topology

-- Re-export all constants from Core for backward compatibility
export GIFT.Core (
  b2 b3 H_star fund_E7
  p2 kappa_T_den det_g_num det_g_den
)

-- Legacy theorems for compatibility
theorem H_star_certified : H_star = 99 := rfl
theorem p2_certified : p2 = 2 := rfl
theorem b2_certified : b2 = 21 := rfl
theorem b3_certified : b3 = 77 := rfl

end GIFT.Topology
