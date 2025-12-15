/-!
# GIFT Topology Module (LEGACY)

This module provides basic topological constants for K₇ manifolds.

## Status: LEGACY (but still primary reference)

This module defines Betti numbers as simple values (e.g., `b2 := 21`).
For derived/justified definitions, see:
- `GIFT.Algebraic.BettiNumbers` — b₂ = C(7,2) derived from octonion imaginary pairs
- `GIFT.Foundations.TCSConstruction` — b₂ = 10+10+1 from Twisted Connected Sum
- `GIFT.Foundations.G2Holonomy` — b₂ = dim(K₇) + dim(G₂) from representation theory

## Usage

Most existing GIFT code (28+ modules) imports this module.
New code should prefer the Algebraic.* modules for documented derivations.
-/

namespace GIFT.Topology

/-- Second Betti number of K7 -/
def b2 : Nat := 21

/-- Third Betti number of K7 (TCS: 40 + 37) -/
def b3 : Nat := 77

/-- Effective degrees of freedom H* = b2 + b3 + 1 -/
def H_star : Nat := b2 + b3 + 1

theorem H_star_certified : H_star = 99 := rfl

/-- Pontryagin class contribution p2 -/
def p2 : Nat := 2

theorem p2_certified : p2 = 2 := rfl

end GIFT.Topology
