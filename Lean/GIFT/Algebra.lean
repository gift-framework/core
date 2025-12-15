import GIFT.Core

/-!
# GIFT Algebra Module (DEPRECATED)

⚠️ **DEPRECATED**: Use `import GIFT.Core` instead.

This module is maintained for backward compatibility only.
All constants are now re-exported from `GIFT.Core`.

## Migration Guide

Replace:
```lean
import GIFT.Algebra
open GIFT.Algebra
```

With:
```lean
import GIFT.Core
open GIFT.Core
```

## Why the change?

`GIFT.Core` provides a single source of truth for all GIFT constants,
eliminating duplicate definitions that were causing confusion.
The constants are derived from octonion structure (not arbitrary values).
-/

namespace GIFT.Algebra

-- Re-export all constants from Core for backward compatibility
export GIFT.Core (
  dim_E8 rank_E8 dim_E8xE8
  dim_E7 dim_fund_E7 dim_E6 dim_F4
  dim_G2 rank_G2
  Weyl_factor Weyl_sq weyl_E8_order
  D_bulk dim_SU3 dim_SU2 dim_U1 dim_SM_gauge
  prime_6 prime_8 prime_11
  dim_J3O_traceless
)

-- Legacy theorems for compatibility
theorem E8xE8_dim_certified : dim_E8xE8 = 496 := rfl
theorem Weyl_sq_certified : Weyl_sq = 25 := rfl
theorem SM_gauge_certified : dim_SM_gauge = 12 := rfl
theorem dim_F4_certified : dim_F4 = 52 := rfl
theorem dim_E6_certified : dim_E6 = 78 := rfl
theorem weyl_E8_order_certified : weyl_E8_order = 696729600 := rfl
theorem dim_J3O_traceless_certified : dim_J3O_traceless = 26 := rfl
theorem dim_E7_certified : dim_E7 = 133 := rfl
theorem dim_fund_E7_certified : dim_fund_E7 = 56 := rfl
theorem prime_6_certified : prime_6 = 13 := rfl
theorem prime_8_certified : prime_8 = 19 := rfl
theorem prime_11_certified : prime_11 = 31 := rfl

end GIFT.Algebra
