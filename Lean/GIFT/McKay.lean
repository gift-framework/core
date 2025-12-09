-- GIFT McKay Correspondence Module
-- v2.0.0: E8 ↔ Icosahedron ↔ Golden Ratio
--
-- This module provides:
-- - McKay correspondence (E8 ↔ Binary Icosahedral)
-- - Coxeter number connections
-- - Golden ratio emergence from icosahedral geometry
--
-- Total: 15 new relations (Relations 186-200)

import GIFT.McKay.Correspondence
import GIFT.McKay.GoldenEmergence

namespace GIFT.McKay

open Correspondence GoldenEmergence

/-- Master theorem: All McKay correspondence relations certified -/
theorem all_mckay_relations_certified :
    Correspondence.all_mckay_correspondence_relations_certified ∧
    GoldenEmergence.all_golden_emergence_relations_certified := by
  constructor
  · exact Correspondence.all_mckay_correspondence_relations_certified
  · exact GoldenEmergence.all_golden_emergence_relations_certified

end GIFT.McKay
