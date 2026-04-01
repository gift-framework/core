"""Base class for compact G₂ manifolds.

A compact 7-manifold with G₂ holonomy has:
    - b₁ = 0 (simply connected)
    - b₂, b₃ free (topological data)
    - χ = 0 (odd-dimensional, oriented, compact)
    - π₁ = 1 (finite fundamental group for full G₂ holonomy)

Construction methods in the literature:
    - Joyce (2000): resolution of T⁷/Γ orbifolds
    - Kovalev (2003): Twisted Connected Sums (TCS)
    - Corti-Haskins-Nordström-Pacini (2015): extended TCS from semi-Fano 3-folds
    - Foscolo-Haskins-Nordström (2021): cohomogeneity-one constructions
"""

from dataclasses import dataclass
from typing import Optional, Dict
from fractions import Fraction


@dataclass
class G2Manifold:
    """A compact 7-manifold with G₂ holonomy.

    This is the base class for all G₂ manifold constructions.
    Subclasses (TCSManifold, etc.) add construction-specific data.

    Parameters:
        name: Human-readable identifier
        b2: Second Betti number
        b3: Third Betti number
        construction: Construction method (e.g., "orbifold", "TCS", "cohom-1")
        reference: Literature reference
    """
    name: str
    b2: int
    b3: int
    construction: str = "unknown"
    reference: str = ""

    @property
    def h_star(self) -> int:
        """Effective cohomological dimension: H* = b₂ + b₃ + 1."""
        return self.b2 + self.b3 + 1

    @property
    def dim(self) -> int:
        return 7

    @property
    def euler_characteristic(self) -> int:
        """Euler characteristic (always 0 for compact oriented odd-dim manifolds)."""
        return 0

    @property
    def moduli_count(self) -> int:
        """Dimension of the G₂ moduli space (= b₃)."""
        return self.b3

    # ------------------------------------------------------------------
    # Physics predictions (from topology alone)
    # ------------------------------------------------------------------

    @property
    def sin2_theta_w(self) -> Optional[Fraction]:
        """Weinberg angle prediction: sin²θ_W = b₂/(b₃ + dim_G₂).

        Only meaningful if b₃ + 14 ≠ 0.
        """
        denom = self.b3 + 14  # dim(G₂) = 14
        if denom == 0:
            return None
        return Fraction(self.b2, denom)

    @property
    def n_generations(self) -> Optional[int]:
        """Number of fermion generations from b₂ = N_gen × dim(K₇).

        Only returns integer if b₂ is divisible by 7.
        """
        if self.b2 % 7 == 0:
            return self.b2 // 7
        return None

    @property
    def h_star_decomposition(self) -> Dict[str, int]:
        """H* and derived quantities."""
        return {
            "b2": self.b2,
            "b3": self.b3,
            "h_star": self.h_star,
            "b2_plus_b3": self.b2 + self.b3,
        }

    def topological_predictions(self) -> Dict:
        """Compute all predictions that depend only on topology.

        These are exact (zero metric dependence) and include:
        - Weinberg angle
        - Generation count
        - Cohomological ratios
        """
        sin2 = self.sin2_theta_w
        n_gen = self.n_generations
        return {
            "sin2_theta_w": float(sin2) if sin2 else None,
            "sin2_theta_w_exact": str(sin2) if sin2 else None,
            "n_generations": n_gen,
            "b2_over_b3": float(Fraction(self.b2, self.b3)) if self.b3 else None,
            "h_star": self.h_star,
            "moduli": self.moduli_count,
            "dark_energy_fraction": float(Fraction(self.b2 + self.b3, self.h_star)),
            # Koide-like parameter: dim_G₂ / b₂
            "koide_param": float(Fraction(14, self.b2)) if self.b2 else None,
        }

    def compare_to_k7(self) -> Dict:
        """Compare this manifold's predictions to GIFT's K₇ (b₂=21, b₃=77)."""
        k7 = {"b2": 21, "b3": 77, "h_star": 99,
               "sin2_theta_w": 3/13, "n_gen": 3, "koide": 2/3}
        mine = self.topological_predictions()
        comparison = {}
        if mine["sin2_theta_w"] is not None:
            comparison["sin2_theta_w"] = {
                "this": mine["sin2_theta_w"],
                "k7": k7["sin2_theta_w"],
                "ratio": mine["sin2_theta_w"] / k7["sin2_theta_w"],
                "exp": 0.2312,
            }
        comparison["n_generations"] = {
            "this": mine["n_generations"],
            "k7": k7["n_gen"],
            "match": mine["n_generations"] == k7["n_gen"],
        }
        comparison["koide"] = {
            "this": mine["koide_param"],
            "k7": k7["koide"],
            "exp": 0.6667,
        }
        comparison["h_star"] = {
            "this": self.h_star,
            "k7": k7["h_star"],
        }
        return comparison

    def summary(self) -> dict:
        return {
            "name": self.name,
            "b2": self.b2,
            "b3": self.b3,
            "h_star": self.h_star,
            "construction": self.construction,
            "euler": self.euler_characteristic,
            "moduli": self.moduli_count,
        }

    def __repr__(self) -> str:
        return (f"G2Manifold({self.name}, b2={self.b2}, b3={self.b3}, "
                f"construction={self.construction})")


# =========================================================================
# Joyce orbifold resolutions (2000)
# =========================================================================
# From "Compact Manifolds with Special Holonomy", Oxford University Press
# Chapter 12: Examples of compact G₂ manifolds

JOYCE_12_2_1 = G2Manifold(
    name="Joyce-T7/Z2^3",
    b2=12, b3=43,
    construction="orbifold",
    reference="Joyce (2000), Example 12.2.1 — T^7/Z_2^3 resolution",
)

JOYCE_12_2_3 = G2Manifold(
    name="Joyce-T7/Z2^3-v2",
    b2=8, b3=33,
    construction="orbifold",
    reference="Joyce (2000), Example 12.2.3",
)

JOYCE_12_2_5 = G2Manifold(
    name="Joyce-T7/Z2^3-v3",
    b2=0, b3=7,
    construction="orbifold",
    reference="Joyce (2000), Example 12.2.5 — minimal Betti numbers",
)

# =========================================================================
# Other constructions
# =========================================================================

FOSCOLO_HASKINS_NORDSTROM = G2Manifold(
    name="FHN-cohom1",
    b2=1, b3=22,
    construction="cohomogeneity-one",
    reference="Foscolo-Haskins-Nordström (2021), Duke Math J.",
)


def list_joyce_manifolds():
    """Return all pre-built Joyce orbifold examples."""
    return [JOYCE_12_2_1, JOYCE_12_2_3, JOYCE_12_2_5]


def list_all_manifolds():
    """Return all pre-built G₂ manifold examples (all constructions)."""
    return [
        JOYCE_12_2_1,
        JOYCE_12_2_3,
        JOYCE_12_2_5,
        FOSCOLO_HASKINS_NORDSTROM,
    ]
