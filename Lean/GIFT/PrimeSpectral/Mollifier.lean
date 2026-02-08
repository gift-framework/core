/-
GIFT Prime-Spectral: Mollifier Kernel
======================================

Cosine-squared mollifier kernel and its properties.

This module is FULLY CONSTRUCTIVE: zero axioms, zero `sorry`.
All theorems follow from Mathlib's trigonometric and real analysis
infrastructure.

The cosine-squared kernel w(x) = cos²(πx/2) for x ∈ [0,1), w(x) = 0
for x ≥ 1, is the smooth weight function used in the mollified
Dirichlet polynomial S_w(T).

Reference: Paper 1, §3.2–3.3
Version: 1.0.0
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Basic

namespace GIFT.PrimeSpectral.Mollifier

open Real

/-!
## Cosine-Squared Kernel Definition
-/

/-- The cosine-squared mollifier kernel.
    w(x) = cos²(πx/2) for x < 1, 0 otherwise.

    This kernel has several desirable properties:
    - Compact support: w(x) = 0 for x ≥ 1
    - Smooth decay: C² on [0,1]
    - Unit normalization: w(0) = 1
    - Boundary vanishing: w(1) = 0
    - Non-negativity: w(x) ≥ 0 for all x -/
noncomputable def cosineKernel (x : ℝ) : ℝ :=
  if x < 1 then (Real.cos (Real.pi * x / 2))^2 else 0

/-!
## Basic Properties (all proven from Mathlib)
-/

/-- The kernel is non-negative everywhere. -/
theorem cosineKernel_nonneg (x : ℝ) : 0 ≤ cosineKernel x := by
  unfold cosineKernel
  split
  · exact sq_nonneg _
  · le_refl

/-- The kernel is bounded above by 1. -/
theorem cosineKernel_le_one (x : ℝ) : cosineKernel x ≤ 1 := by
  unfold cosineKernel
  split
  · exact sq_le_one_of_abs_le_one (abs_cos_le_one _)
  · linarith

/-- At x = 0, the kernel equals 1. -/
theorem cosineKernel_at_zero : cosineKernel 0 = 1 := by
  unfold cosineKernel
  simp [cos_zero]

/-- For x ≥ 1, the kernel vanishes (compact support). -/
theorem cosineKernel_support (x : ℝ) (hx : 1 ≤ x) : cosineKernel x = 0 := by
  unfold cosineKernel
  simp [not_lt.mpr hx]

/-!
## Kernel Comparison

Seven kernel families were tested (Paper 1, §3.3):
- Sharp: 𝟙{x<1}       — α = 0.805, R² = 0.887
- Linear: (1−x)₊       — α = 1.247, R² = 0.881
- Selberg: (1−x²)₊     — α = 1.018, R² = 0.909
- Cosine: cos²(πx/2)   — α = 1.131, R² = 0.853 (at fixed cutoff)
- Quadratic: (1−x)²₊   — α = 1.516, R² = 0.789
- Gaussian: e^{−x²/σ²} — α = 1.160, R² = 0.855
- Cubic: (1−x)³₊       — α = 1.752, R² = 0.711

The cosine kernel combined with adaptive X(T) = T^{θ(T)} achieves
α = 1.000 exactly, making it the optimal choice under the self-
normalization constraint.
-/

/-- The seven tested kernel families (indices 0–6). -/
def kernelFamilies : Fin 7 → String :=
  ![  "Sharp (indicator)",
      "Linear ((1-x)₊)",
      "Selberg ((1-x²)₊)",
      "Cosine (cos²(πx/2))",
      "Quadratic ((1-x)²₊)",
      "Gaussian (e^{-x²/σ²})",
      "Cubic ((1-x)³₊)" ]

/-- The cosine kernel is family index 3. -/
theorem cosine_is_family_3 : kernelFamilies 3 = "Cosine (cos²(πx/2))" := rfl

/-!
## Certified Properties
-/

/-- Master certificate for mollifier kernel properties. -/
theorem mollifier_certified :
    cosineKernel 0 = 1 ∧
    (∀ x, 0 ≤ cosineKernel x) ∧
    (∀ x, cosineKernel x ≤ 1) ∧
    (∀ x, 1 ≤ x → cosineKernel x = 0) :=
  ⟨cosineKernel_at_zero,
   cosineKernel_nonneg,
   cosineKernel_le_one,
   cosineKernel_support⟩

end GIFT.PrimeSpectral.Mollifier
