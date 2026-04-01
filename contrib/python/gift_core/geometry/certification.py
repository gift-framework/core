"""Newton-Kantorovich certification for G2 metrics.

Given an approximate torsion-free G2 metric, the NK theorem provides
rigorous bounds guaranteeing the existence of a true torsion-free
metric nearby, with quantitative error estimates.

Key parameters:
    beta: Inverse operator bound (1/lambda_1_perp)
    eta_0: Initial residual (||T(phi_0)|| / lambda_1_perp)
    rho: Contraction rate
    h: Kantorovich parameter (must be < 0.5 for convergence)
    r: Uniqueness ball radius (eta_0 / (1 - rho))

The G2 calibration form phi_0 has norm |phi_0| = sqrt(42) = sqrt(2*b2),
which sets the natural scale for metric corrections.
"""

import math
from dataclasses import dataclass
from typing import Optional


# |phi_0| = sqrt(42) for the canonical G2 3-form on R^7
_PHI0_NORM = math.sqrt(42)


@dataclass
class NKCertification:
    """Newton-Kantorovich certification result.

    Parameters:
        torsion_norm: ||T(phi_0)|| (C^0 norm of torsion)
        spectral_gap: lambda_1_perp (first nonzero eigenvalue)
        lipschitz: Lipschitz constant of the linearized operator
    """
    torsion_norm: float
    spectral_gap: float
    lipschitz: float

    @property
    def beta(self) -> float:
        """Inverse operator bound: beta = 1 / lambda_1_perp."""
        return 1.0 / self.spectral_gap

    @property
    def eta_0(self) -> float:
        """Initial step size: eta_0 = ||T(phi_0)|| / lambda_1_perp."""
        return self.torsion_norm / self.spectral_gap

    @property
    def gamma(self) -> float:
        """Second derivative bound (Lipschitz constant)."""
        return self.lipschitz

    @property
    def h(self) -> float:
        """Kantorovich parameter h = beta * gamma * eta_0. Must be < 0.5."""
        return self.beta * self.gamma * self.eta_0

    @property
    def is_certified(self) -> bool:
        """Whether the NK certification succeeds (h < 0.5)."""
        return self.h < 0.5

    @property
    def contraction_rate(self) -> float:
        """Contraction rate rho = h / (1 - sqrt(1 - 2h)).

        For h < 0.5, this gives rho < 1, ensuring geometric convergence.
        """
        if not self.is_certified:
            return float("inf")
        return self.h / (1.0 - math.sqrt(1.0 - 2.0 * self.h))

    @property
    def uniqueness_radius(self) -> float:
        """Radius of the uniqueness ball: r = eta_0 / (1 - rho)."""
        rho = self.contraction_rate
        if rho >= 1.0:
            return float("inf")
        return self.eta_0 / (1.0 - rho)

    @property
    def safety_margin(self) -> float:
        """How far below the h < 0.5 threshold. Higher = safer."""
        return 0.5 / self.h if self.h > 0 else float("inf")

    @property
    def uniqueness_ball(self) -> tuple:
        """Inner and outer radii of the Kantorovich uniqueness ball.

        Returns (r_inner, r_outer) where:
            r_inner = (1 - sqrt(1 - 2h)) / (beta * gamma)
            r_outer = (1 + sqrt(1 - 2h)) / (beta * gamma)

        The true solution lies within B(phi_0, r_inner).
        No other solution exists in B(phi_0, r_outer).
        """
        if not self.is_certified:
            return (float("inf"), float("inf"))
        discriminant = math.sqrt(1.0 - 2.0 * self.h)
        denom = self.beta * self.gamma
        r_inner = (1.0 - discriminant) / denom
        r_outer = (1.0 + discriminant) / denom
        return (r_inner, r_outer)

    def iteration_table(self, n_max: int = 8) -> list:
        """Compute the NK iteration convergence table.

        Returns a list of dicts, one per iteration, with:
            n: iteration number (0-indexed)
            torsion_bound: T_0 * rho^n (residual at step n)
            distance_to_solution: eta_0 * rho^n / (1 - rho)
            metric_correction: distance / sqrt(42)  (relative to |phi_0|)

        The geometric decay rho^n guarantees rapid convergence when
        the certification succeeds.
        """
        if not self.is_certified:
            return []
        rho = self.contraction_rate
        T0 = self.torsion_norm
        rows = []
        for n in range(n_max):
            rho_n = rho ** n
            torsion_bound = T0 * rho_n
            distance = self.eta_0 * rho_n / (1.0 - rho)
            metric_correction = distance / _PHI0_NORM
            rows.append({
                "n": n,
                "torsion_bound": torsion_bound,
                "distance_to_solution": distance,
                "metric_correction": metric_correction,
            })
        return rows

    def scale_to_neck_length(self, L: float) -> "NKCertification":
        """Return a new NKCertification rescaled by neck length L.

        Under L-scaling of a TCS G2 manifold:
            - Torsion scales as 1/L (concentration in the neck region)
            - Spectral gap is scale-invariant (eigenvalue ratio)
            - Lipschitz constant scales as 1/L (derivative of torsion map)

        Args:
            L: Neck length parameter (must be positive).

        Returns:
            New NKCertification with rescaled parameters.
        """
        if L <= 0:
            raise ValueError(f"Neck length must be positive, got {L}")
        return NKCertification(
            torsion_norm=self.torsion_norm / L,
            spectral_gap=self.spectral_gap,
            lipschitz=self.lipschitz / L,
        )

    def observable_corrections(self, condition_number: float = 3.88) -> dict:
        """Propagate metric uncertainty to physical observables.

        The relative metric error is:
            delta_g/g = eta_0 / ((1 - rho) * sqrt(42))

        Observable sensitivities fall into two classes:

        1. Topological (exact): sin^2(theta_W), N_gen, selection rules
           depend only on topology (Betti numbers, cohomology), not the
           metric. These have zero error regardless of metric uncertainty.

        2. Metric-dependent: Yukawa couplings, volume, eigenvalues
           pick up errors through their dependence on the G2 metric.
           The condition number kappa controls eigenvalue sensitivity.

        Args:
            condition_number: Condition number kappa for eigenvalue
                sensitivity. Default 3.88 from K7 Laplacian estimates.

        Returns:
            Dict with relative error bounds for each observable class.
        """
        if not self.is_certified:
            return {"error": "certification failed, no error bounds available"}

        rho = self.contraction_rate
        dg_over_g = self.eta_0 / ((1.0 - rho) * _PHI0_NORM)

        return {
            # Topological observables: exact
            "sin2_theta_W": {"relative_error": 0.0, "type": "topological"},
            "N_gen": {"relative_error": 0.0, "type": "topological"},
            "selection_rules": {"relative_error": 0.0, "type": "topological"},
            # Metric-dependent observables
            "yukawa": {
                "relative_error": 4.0 * dg_over_g,
                "formula": "delta_Y/Y <= 4 * delta_g/g",
                "type": "metric-dependent",
            },
            "volume": {
                "relative_error": 3.5 * dg_over_g,
                "formula": "delta_V/V = 3.5 * delta_g/g",
                "type": "metric-dependent",
            },
            "eigenvalues": {
                "relative_error": condition_number * dg_over_g,
                "formula": "delta_lambda/lambda <= kappa * delta_g/g",
                "condition_number": condition_number,
                "type": "metric-dependent",
            },
            # Summary
            "delta_g_over_g": dg_over_g,
        }

    def iterations_to_precision(self, target: float = 1e-15) -> int:
        """Number of NK iterations needed to reach a target precision.

        The distance to the true solution after n iterations is bounded by:
            d_n <= eta_0 * rho^n / (1 - rho)

        We solve for the smallest n such that d_n <= target.

        Args:
            target: Desired upper bound on the distance to the true
                solution. Default 1e-15 (double precision).

        Returns:
            Number of iterations needed (0 if already below target).

        Raises:
            ValueError: If certification failed (no convergence guarantee).
        """
        if not self.is_certified:
            raise ValueError("Certification failed: no convergence guarantee")
        rho = self.contraction_rate
        if rho <= 0:
            return 0
        # d_n = eta_0 * rho^n / (1 - rho) <= target
        # rho^n <= target * (1 - rho) / eta_0
        threshold = target * (1.0 - rho) / self.eta_0
        if threshold >= 1.0:
            return 0
        if threshold <= 0.0:
            return -1  # unreachable
        # n >= log(threshold) / log(rho)
        n = math.log(threshold) / math.log(rho)
        return math.ceil(n)

    def error_budget(self) -> dict:
        """Decompose the total error into contributing sources.

        Returns a dict mapping each error source to its contribution
        and relative weight in the total error budget:
            - torsion_residual: from ||T(phi_0)|| (initial torsion)
            - inverse_bound: from 1/lambda_1_perp (spectral gap)
            - nonlinearity: from Lipschitz constant (curvature of map)
            - convergence: from contraction rate rho
        """
        if not self.is_certified:
            return {"error": "certification failed"}

        rho = self.contraction_rate
        total_distance = self.eta_0 / (1.0 - rho)
        metric_error = total_distance / _PHI0_NORM

        # Each factor's logarithmic contribution to h = beta * gamma * eta_0
        log_h = math.log(self.h) if self.h > 0 else float("-inf")
        log_beta = math.log(self.beta)
        log_gamma = math.log(self.gamma) if self.gamma > 0 else float("-inf")
        log_eta = math.log(self.eta_0) if self.eta_0 > 0 else float("-inf")
        log_total = abs(log_beta) + abs(log_gamma) + abs(log_eta)

        def weight(log_val: float) -> float:
            return abs(log_val) / log_total if log_total > 0 else 0.0

        return {
            "torsion_residual": {
                "value": self.torsion_norm,
                "description": "||T(phi_0)||: initial torsion of approximate metric",
                "weight": weight(log_eta),
            },
            "inverse_bound": {
                "value": self.beta,
                "description": "1/lambda_1_perp: inverse spectral gap",
                "weight": weight(log_beta),
            },
            "nonlinearity": {
                "value": self.gamma,
                "description": "Lipschitz constant of linearized torsion map",
                "weight": weight(log_gamma),
            },
            "convergence": {
                "contraction_rate": rho,
                "iterations_to_1e-15": self.iterations_to_precision(1e-15),
                "description": "geometric convergence rate rho",
            },
            "total_metric_error": metric_error,
            "total_distance_to_solution": total_distance,
            "kantorovich_parameter": self.h,
        }

    def summary(self) -> dict:
        """Summary dict of the certification result."""
        result = {
            "certified": self.is_certified,
            "h": self.h,
            "h_threshold": 0.5,
            "safety_margin": f"{self.safety_margin:.1f}x",
            "contraction_rate": self.contraction_rate,
            "uniqueness_radius": self.uniqueness_radius,
            "torsion_norm": self.torsion_norm,
            "spectral_gap": self.spectral_gap,
        }
        if self.is_certified:
            r_inner, r_outer = self.uniqueness_ball
            result["uniqueness_ball_inner"] = r_inner
            result["uniqueness_ball_outer"] = r_outer
        return result

    def __repr__(self) -> str:
        status = "CERTIFIED" if self.is_certified else "FAILED"
        return (
            f"NKCertification({status}: h={self.h:.6f}, "
            f"margin={self.safety_margin:.1f}x, "
            f"rho={self.contraction_rate:.4f})"
        )
