# Phase A.2 - Model B Route

**Status**: active work package, 2026-05-12.

Phase A.1 is closed at the algebraic-counting and symbolic-certificate level.
The remaining open work is Phase A.2: an explicit smooth global K3 model
with the required `Z_2^3` action, suitable for the resolved `N_epsilon`
atlas.

## Current route

The current route is Model B:

- anchor model: `K3GenusTwoSymmetricDoubleCover`
- secondary skeleton: `EllipticK3WeierstrassFull2Torsion`
- target status: explicit high-Picard K3 with a completed `Z_2^3` action

This anchor already matches the `tau` profile `(11, 7, 1)` in the
Garbagnati-Salgado Proposition 7.3 setup. The remaining gap is the
completion of the anti-symplectic side:

- a second commuting symmetry on the branch sextic,
- full `s_i tau` fixed-locus profiles `(11, 9, 1)`,
- and a resolved atlas suitable for the Phase B patching.

## What is documented in code

The current audit entry point is:

```bash
PYTHONPATH=contrib/python python3 -m gift_core.examples.donaldson_direct --phase-a2-route
```

The audit report records:

- the route name,
- the current blocker,
- the next concrete subproblem,
- and the supporting Weierstrass skeleton.

## Next step

Search a sigma'-symmetric branch sextic, or an equivalent high-Picard
double-cover model, that completes the missing `s_i tau` profiles while
keeping the model explicit and smooth.
