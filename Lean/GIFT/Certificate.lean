/-!
# GIFT Certificate (Backward Compatibility)

**DEPRECATED**: This file redirects to the new modular certificate structure.

The certificate is now organized by mathematical domain:
- `Certificate/Foundations.lean` — E₈, G₂, octonions, K₇, Joyce
- `Certificate/Predictions.lean` — 33+ published relations, V5.0 observables
- `Certificate/Spectral.lean` — Mass gap, TCS bounds, selection principle
- `Certificate/Core.lean` — Master certificate combining all three

Use `import GIFT.Certificate.Core` for the master certificate.
-/

import GIFT.Certificate.Core

-- Re-export all sub-certificate namespaces for backward compatibility
open GIFT.Certificate.Foundations in
open GIFT.Certificate.Predictions in
open GIFT.Certificate.Spectral in

namespace GIFT.Certificate

-- Legacy aliases for the most commonly referenced theorems

/-- Legacy alias: master certificate -/
abbrev all_relations_certified := GIFT.Certificate.Predictions.certified

/-- Legacy alias: foundations -/
abbrev gift_v32_foundations_certificate := GIFT.Certificate.Foundations.certified

/-- Legacy alias: spectral gap -/
abbrev gift_v338_yang_mills_certificate := GIFT.Certificate.Spectral.certified

/-- Legacy alias: observables -/
abbrev gift_v50_extended_observables_certificate := GIFT.Certificate.Predictions.observables_certified

end GIFT.Certificate
