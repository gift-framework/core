"""Verification for the current Phase A.2 route selection."""

from __future__ import annotations

from gift_core.geometry.k3_explicit import audit_phase_a2_route


def verify() -> dict[str, bool]:
    report = audit_phase_a2_route()
    return {
        "phase_a2_route_selected": report["route_name"] == "Model B / Garbagnati-Salgado Prop. 7.3 double cover",
        "phase_a2_anchor_tau_matches_11_7_1": report["anchor_tau_matches_11_7_1"] is True,
        "phase_a2_route_is_incomplete": report["status"] == "selected_but_incomplete",
        "phase_a2_blocker_documented": "pending" in report["documented_blocker"].lower(),
        "phase_a2_next_step_mentions_sigma_prime": "sigma'" in report["next_concrete_step"],
        "phase_a2_weierstrass_skeleton_present": report["weierstrass_skeleton_present"] is True,
        "phase_a2_weierstrass_picard_rank_geq_11": report["weierstrass_picard_rank_geq_11"] is True,
    }


def main() -> None:
    results = verify()
    for name, passed in results.items():
        print(f"{name}: {'PASS' if passed else 'FAIL'}")
    if not all(results.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
