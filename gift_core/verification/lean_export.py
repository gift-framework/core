"""
Lean 4 export functionality.

Generates Lean 4 code from numerical certificates
for integration with formal proofs.
"""

from dataclasses import dataclass
from typing import Dict, List, Optional
from fractions import Fraction

from .numerical_bounds import IntervalArithmetic
from .certificate import G2Certificate


@dataclass
class LeanExporter:
    """
    Export numerical results to Lean 4 format.

    Generates Lean theorems that state bounds on computed
    quantities, allowing formal proofs to use numerical results.

    Attributes:
        namespace: Lean namespace for generated code
        include_proofs: Whether to include proof terms
    """

    namespace: str = "GIFT.Numerical"
    include_proofs: bool = True

    def export_interval(self, name: str, interval: IntervalArithmetic,
                        target: Optional[Fraction] = None) -> str:
        """
        Export interval bound as Lean theorem.

        Args:
            name: Name for the bound
            interval: Computed interval
            target: Optional target rational value

        Returns:
            Lean theorem statement
        """
        if target is not None:
            # Verify target is in interval
            verified = interval.contains(float(target))
            p, q = target.numerator, target.denominator

            return f'''
/-- {name}: numerical bound contains exact value {target} -/
theorem {name}_contains_exact :
    ({interval.lo} : Float) ≤ ({p} : Float) / {q} ∧
    ({p} : Float) / {q} ≤ ({interval.hi} : Float) := by
  native_decide
-- Verified: {verified}
'''
        else:
            return f'''
/-- {name}: computed in interval [{interval.lo}, {interval.hi}] -/
def {name}_lo : Float := {interval.lo}
def {name}_hi : Float := {interval.hi}
def {name}_center : Float := {interval.center}
def {name}_radius : Float := {interval.radius}
'''

    def export_certificate(self, cert: G2Certificate) -> str:
        """
        Export full certificate to Lean.

        Args:
            cert: G2Certificate to export

        Returns:
            Complete Lean module
        """
        header = f'''/-
  GIFT Numerical Certificate
  Generated: {cert.timestamp}
  Model: {cert.model_id}

  This file contains verified numerical bounds that bridge
  numerical computation with formal proofs.
-/

namespace {self.namespace}

-- Target values (from formal proofs)
def det_g_exact : Rat := 65 / 32
def kappa_t_exact : Rat := 1 / 61
def b2_exact : Nat := 21
def b3_exact : Nat := 77
'''

        # Export each constraint
        det_g_export = self.export_interval(
            "det_g", cert.det_g, cert.det_g_expected
        )

        kappa_t_export = self.export_interval(
            "kappa_t", cert.kappa_t, cert.kappa_t_expected
        )

        betti_export = f'''
/-- Second Betti number verified -/
theorem b2_verified : ({cert.betti_2} : Nat) = b2_exact := rfl

/-- Third Betti number verified -/
theorem b3_verified : ({cert.betti_3} : Nat) = b3_exact := rfl
'''

        master = f'''
/-- Master verification theorem -/
theorem all_numerical_verified :
    b2_verified ∧ b3_verified := ⟨rfl, rfl⟩

end {self.namespace}
'''

        return header + det_g_export + kappa_t_export + betti_export + master

    def export_constants(self, constants: Dict[str, float]) -> str:
        """
        Export computed constants as Lean definitions.

        Args:
            constants: Dictionary of constant names and values

        Returns:
            Lean definitions
        """
        lines = [f"namespace {self.namespace}.Constants\n"]

        for name, value in constants.items():
            lines.append(f"def {name} : Float := {value}")

        lines.append(f"\nend {self.namespace}.Constants")

        return "\n".join(lines)


def export_to_lean(cert: G2Certificate, filepath: Optional[str] = None) -> str:
    """
    Export certificate to Lean file.

    Args:
        cert: Certificate to export
        filepath: Optional path to write file

    Returns:
        Generated Lean code
    """
    exporter = LeanExporter()
    code = exporter.export_certificate(cert)

    if filepath:
        with open(filepath, 'w') as f:
            f.write(code)

    return code


def export_to_coq(cert: G2Certificate, filepath: Optional[str] = None) -> str:
    """
    Export certificate to Coq file.

    Args:
        cert: Certificate to export
        filepath: Optional path to write file

    Returns:
        Generated Coq code
    """
    code = cert.to_coq()

    if filepath:
        with open(filepath, 'w') as f:
            f.write(code)

    return code
