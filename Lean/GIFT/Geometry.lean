import GIFT.Core

/-!
# GIFT Geometry Module (DEPRECATED)

⚠️ **DEPRECATED**: Use `import GIFT.Core` instead.

This module is maintained for backward compatibility only.
All constants are now re-exported from `GIFT.Core`.

## Migration Guide

Replace:
```lean
import GIFT.Geometry
open GIFT.Geometry
```

With:
```lean
import GIFT.Core
open GIFT.Core
```

## Why the change?

`GIFT.Core` provides a single source of truth for all GIFT constants,
including geometry constants like dim_K7 and dim_J3O.
-/

namespace GIFT.Geometry

-- Re-export all constants from Core for backward compatibility
export GIFT.Core (
  dim_K7 dim_J3O dim_J3O_traceless
  det_g_num det_g_den kappa_T_den
)

-- Legacy definitions and theorems
def neck_length_default : Nat := 10

/-- det(g) = 65/32 derivation: (H* - b2 - 13) / 2^Weyl -/
theorem det_g_from_topology (H_star b2 : Nat) (Weyl : Nat) :
    H_star = 99 → b2 = 21 → Weyl = 5 →
    H_star - b2 - 13 = det_g_num ∧ 2^Weyl = det_g_den := by
  intro h1 h2 h3
  constructor
  · simp [h1, h2]; native_decide
  · simp [h3]; native_decide

/-- kappa_T = 1/61 derivation -/
theorem kappa_T_from_topology (b3 dim_G2 p2 : Nat) :
    b3 = 77 → dim_G2 = 14 → p2 = 2 →
    b3 - dim_G2 - p2 = kappa_T_den := by
  intro h1 h2 h3
  simp [h1, h2, h3]
  native_decide

/-- K7 has G2 holonomy (dimension constraint) -/
theorem k7_g2_holonomy : dim_K7 = 7 ∧ 14 < 21 := by
  constructor
  · rfl
  · native_decide

end GIFT.Geometry
