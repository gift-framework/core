# K₇ Metric Implementation Plan for GIFT Core

**Objective**: Implement the explicit K₇ G₂ metric in `gift-framework/core` following the same rigorous approach used in `private`.

---

## Current State Analysis

### What We Have (in `private`)

| Component | File | Status |
|-----------|------|--------|
| TCS Topology | `K7_TCS_Construction.py` | ✅ b₃=77 derived |
| Kummer K3 | `K3_Kummer_Surface.py` | ✅ b₂=22 validated |
| ACyl CY3 | `ACyl_CY3_Construction.py` | ✅ Building blocks |
| TCS Metric | `K7_TCS_Metric.py` | ✅ Gluing framework |
| Lean 4 Proofs | `lean4-g2/` | ✅ Machine verified |

### What Exists in Research Modules

| Module | Purpose | Maturity |
|--------|---------|----------|
| `variational_g2/` | PINN for G₂ 3-form | 🔶 Architecture done |
| `meta_hodge/` | Hodge operators | 🔶 Exploratory |
| `harmonic_yukawa/` | Yukawa extraction | 🔶 Pipeline defined |
| `tcs_joyce/` | TCS global modes | 🔶 Analysis ready |

### Gap Analysis

**Missing for Production**:
1. Unified K₇ metric class (combining TCS + PINN)
2. Certified numerical bounds (for Lean integration)
3. End-to-end pipeline from geometry → physics
4. Core library integration

---

## Proposed Architecture for Core

### Module Structure

```
gift-framework/core/
├── geometry/
│   ├── __init__.py
│   ├── k3_surface.py           # Kummer K3 (from K3_Kummer_Surface.py)
│   ├── acyl_cy3.py             # ACyl building blocks
│   ├── tcs_construction.py     # TCS gluing
│   └── k7_metric.py            # Main K₇ metric class
│
├── g2/
│   ├── __init__.py
│   ├── g2_form.py              # G₂ 3-form φ and *φ
│   ├── holonomy.py             # Holonomy computation
│   ├── torsion.py              # dφ, d*φ, torsion classes
│   └── constraints.py          # det(g)=65/32, κ_T=1/61
│
├── harmonic/
│   ├── __init__.py
│   ├── hodge_laplacian.py      # Δ = dδ + δd
│   ├── harmonic_forms.py       # Extract basis
│   └── betti_validation.py     # Verify b₂=21, b₃=77
│
├── physics/
│   ├── __init__.py
│   ├── yukawa_tensor.py        # Y_ijk computation
│   ├── mass_spectrum.py        # Fermion masses
│   └── coupling_constants.py   # sin²θ_W, etc.
│
├── nn/
│   ├── __init__.py
│   ├── g2_pinn.py              # Physics-Informed NN
│   ├── fourier_features.py     # Coordinate encoding
│   ├── training.py             # Multi-phase curriculum
│   └── loss_functions.py       # Torsion + constraint losses
│
├── verification/
│   ├── __init__.py
│   ├── numerical_bounds.py     # Certified intervals
│   ├── lean_export.py          # Export to Lean format
│   └── certificate.py          # Verification certificates
│
└── pipeline/
    ├── __init__.py
    ├── full_pipeline.py        # End-to-end execution
    └── config.py               # Global configuration
```

---

## Implementation Phases

### Phase 1: Core Geometry (Week 1-2)

**Goal**: Port validated K₇ construction to core.

#### 1.1 K3 Surface Module

```python
# core/geometry/k3_surface.py

class KummerK3:
    """Kummer K3 surface: T⁴/Z₂ resolved."""

    betti: List[int] = [1, 0, 22, 0, 1]
    euler: int = 24
    hodge: Dict = {'h20': 1, 'h11': 20, 'h02': 1}

    def __init__(self, resolution: int = 16):
        self.exceptional_divisors = resolution  # 16 P¹s
        self.validate()

    def metric_flat(self, x: Tensor) -> Tensor:
        """Flat metric inherited from T⁴."""
        return torch.eye(4).expand(x.shape[0], 4, 4)

    def metric_ricci_flat(self, x: Tensor) -> Tensor:
        """Ricci-flat Kähler metric (approximation)."""
        # TODO: Implement Donaldson balanced metrics
        pass
```

#### 1.2 TCS Construction Module

```python
# core/geometry/tcs_construction.py

class TCSManifold:
    """K₇ = X₊ ∪_{K3×S¹} X₋"""

    def __init__(self, X_plus: ACylCY3, X_minus: ACylCY3, T: float = 10.0):
        self.X_plus = X_plus
        self.X_minus = X_minus
        self.neck_length = T
        self.cutoff = SmoothCutoff(T)

    def betti_numbers(self) -> List[int]:
        """Compute via Mayer-Vietoris."""
        kernel = self.X_plus.b3 + self.X_minus.b3 - 6  # = 34
        boundary = 43
        b3 = kernel + boundary  # = 77
        return [1, 0, 12, b3, b3, 12, 0, 1]

    def metric(self, region: str, coords: Tensor) -> Tensor:
        """Get metric tensor at coordinates."""
        if region == 'plus':
            return self.X_plus.metric(coords)
        elif region == 'minus':
            return self.X_minus.metric(coords)
        else:  # neck
            return self._neck_metric(coords)
```

### Phase 2: G₂ Structure (Week 2-3)

**Goal**: Implement G₂ 3-form with constraints.

#### 2.1 G₂ Form Class

```python
# core/g2/g2_form.py

class G2Form:
    """G₂ 3-form φ on 7-manifold."""

    # Standard form indices (7 terms)
    STANDARD_INDICES = [
        ((0,1,2), +1),  # e¹²³
        ((0,3,4), +1),  # e¹⁴⁵
        ((0,5,6), +1),  # e¹⁶⁷
        ((1,3,5), +1),  # e²⁴⁶
        ((1,4,6), -1),  # e²⁵⁷
        ((2,3,6), -1),  # e³⁴⁷
        ((2,4,5), -1),  # e³⁵⁶
    ]

    def __init__(self, components: Tensor):
        """Initialize from 35 independent components."""
        self.components = components
        self._build_full_tensor()

    def metric(self) -> Tensor:
        """Extract metric g_ij from φ."""
        # g_ij = (1/6) φ_ikl φ_jmn ε^{klmn...}
        pass

    def hodge_star(self) -> 'G2Form4':
        """Compute *φ (the G₂ 4-form ψ)."""
        pass

    @property
    def det_g(self) -> Tensor:
        """Determinant of induced metric."""
        return torch.det(self.metric())

    def torsion_free_loss(self) -> Tensor:
        """||dφ||² + ||d*φ||²"""
        pass
```

#### 2.2 Constraint Module

```python
# core/g2/constraints.py

class G2Constraints:
    """GIFT constraints for G₂ structure."""

    # Target values
    DET_G_TARGET = Fraction(65, 32)  # = 2.03125
    KAPPA_T_TARGET = Fraction(1, 61)  # ≈ 0.01639
    B2_TARGET = 21
    B3_TARGET = 77

    def det_g_loss(self, phi: G2Form) -> Tensor:
        """Loss for det(g) = 65/32."""
        return (phi.det_g - float(self.DET_G_TARGET))**2

    def kappa_t_loss(self, phi: G2Form) -> Tensor:
        """Loss for κ_T = 1/61."""
        kappa = self.compute_torsion_parameter(phi)
        return (kappa - float(self.KAPPA_T_TARGET))**2

    def total_constraint_loss(self, phi: G2Form, weights: Dict) -> Tensor:
        """Combined constraint loss."""
        return (weights['det'] * self.det_g_loss(phi) +
                weights['kappa'] * self.kappa_t_loss(phi) +
                weights['torsion'] * phi.torsion_free_loss())
```

### Phase 3: Neural Network (Week 3-4)

**Goal**: PINN that learns torsion-free G₂ structure.

#### 3.1 Network Architecture

```python
# core/nn/g2_pinn.py

class G2PINN(nn.Module):
    """Physics-Informed Neural Network for G₂ 3-form."""

    def __init__(self,
                 hidden_dims: List[int] = [256, 256, 256, 256],
                 num_frequencies: int = 64):
        super().__init__()

        # Fourier feature encoding
        self.fourier = FourierFeatures(
            input_dim=7,
            num_frequencies=num_frequencies
        )

        # MLP: encoded coords → 35 components
        layers = []
        in_dim = 2 * num_frequencies
        for h in hidden_dims:
            layers.extend([nn.Linear(in_dim, h), nn.SiLU()])
            in_dim = h
        layers.append(nn.Linear(in_dim, 35))
        self.mlp = nn.Sequential(*layers)

    def forward(self, x: Tensor) -> G2Form:
        """Map coordinates to G₂ 3-form."""
        encoded = self.fourier(x)
        components = self.mlp(encoded)
        return G2Form(components)
```

#### 3.2 Training Pipeline

```python
# core/nn/training.py

class G2Trainer:
    """Multi-phase curriculum training for G₂ PINN."""

    PHASES = [
        {'name': 'init', 'epochs': 100, 'lr': 1e-3,
         'weights': {'torsion': 0.1, 'det': 1.0, 'kappa': 0.0}},
        {'name': 'constraint', 'epochs': 200, 'lr': 5e-4,
         'weights': {'torsion': 0.5, 'det': 1.0, 'kappa': 0.5}},
        {'name': 'torsion', 'epochs': 500, 'lr': 1e-4,
         'weights': {'torsion': 1.0, 'det': 0.5, 'kappa': 1.0}},
        {'name': 'refine', 'epochs': 200, 'lr': 1e-5,
         'weights': {'torsion': 1.0, 'det': 1.0, 'kappa': 1.0}},
    ]

    def train(self, model: G2PINN, config: TrainConfig) -> TrainResult:
        """Execute multi-phase training."""
        for phase in self.PHASES:
            self._train_phase(model, phase)
        return self._collect_results(model)
```

### Phase 4: Harmonic Forms & Physics (Week 4-5)

**Goal**: Extract physics from trained metric.

#### 4.1 Harmonic Form Extraction

```python
# core/harmonic/harmonic_forms.py

class HarmonicExtractor:
    """Extract harmonic forms from G₂ metric."""

    def __init__(self, metric: G2Metric, resolution: int = 32):
        self.metric = metric
        self.resolution = resolution
        self.laplacian = HodgeLaplacian(metric)

    def extract_basis(self, degree: int, num_forms: int) -> HarmonicBasis:
        """Extract orthonormal harmonic forms."""
        # Solve Δω = λω, take λ ≈ 0
        eigenvalues, eigenvectors = self.laplacian.smallest_eigenvalues(
            degree=degree, k=num_forms * 2
        )

        # Filter near-zero eigenvalues
        zero_mask = eigenvalues < self.zero_threshold
        harmonic = eigenvectors[zero_mask]

        # Orthonormalize
        return self._gram_schmidt(harmonic)

    def validate_betti(self) -> Dict[int, int]:
        """Compute and validate Betti numbers."""
        computed = {}
        for p in range(8):
            basis = self.extract_basis(degree=p, num_forms=100)
            computed[p] = len(basis)

        expected = [1, 0, 21, 77, 77, 21, 0, 1]  # GIFT K₇
        assert computed == dict(enumerate(expected))
        return computed
```

#### 4.2 Yukawa Tensor

```python
# core/physics/yukawa_tensor.py

class YukawaTensor:
    """Compute Yukawa couplings from harmonic forms."""

    def __init__(self, basis_2: HarmonicBasis, basis_3: HarmonicBasis):
        self.omega_2 = basis_2  # 21 2-forms
        self.omega_3 = basis_3  # 77 3-forms

    def compute(self) -> Tensor:
        """Y_ijk = ∫_{K₇} ω_i ∧ ω_j ∧ ω_k"""
        n2, n3 = len(self.omega_2), len(self.omega_3)
        Y = torch.zeros(n2, n3, n3)

        for i, omega_i in enumerate(self.omega_2):
            for j, omega_j in enumerate(self.omega_3):
                for k, omega_k in enumerate(self.omega_3):
                    if k >= j:  # Symmetry
                        Y[i,j,k] = self._integrate_wedge(omega_i, omega_j, omega_k)
                        Y[i,k,j] = Y[i,j,k]

        return Y

    def mass_eigenvalues(self) -> Tensor:
        """Extract fermion mass ratios from Yukawa."""
        gram = torch.einsum('ijk,ilk->jl', self.Y, self.Y)
        eigenvalues = torch.linalg.eigvalsh(gram)
        return torch.sqrt(eigenvalues.abs())
```

### Phase 5: Verification & Integration (Week 5-6)

**Goal**: Certified outputs for Lean integration.

#### 5.1 Numerical Certificates

```python
# core/verification/certificate.py

@dataclass
class G2Certificate:
    """Machine-verifiable certificate for G₂ metric."""

    # Computed values with bounds
    det_g: IntervalArithmetic  # e.g., [2.031, 2.032]
    kappa_t: IntervalArithmetic
    betti_2: int
    betti_3: int

    # Expected values
    det_g_expected: Fraction = Fraction(65, 32)
    kappa_t_expected: Fraction = Fraction(1, 61)
    betti_2_expected: int = 21
    betti_3_expected: int = 77

    def verify(self) -> bool:
        """Check all constraints are satisfied."""
        return (
            self.det_g.contains(float(self.det_g_expected)) and
            self.kappa_t.contains(float(self.kappa_t_expected)) and
            self.betti_2 == self.betti_2_expected and
            self.betti_3 == self.betti_3_expected
        )

    def to_lean(self) -> str:
        """Export to Lean 4 format."""
        return f"""
theorem det_g_verified :
    |det_g_computed - (65 : ℚ) / 32| < {self.det_g.radius} := by
  native_decide

theorem betti_3_verified : betti_3_computed = 77 := rfl
"""
```

#### 5.2 Full Pipeline

```python
# core/pipeline/full_pipeline.py

class GIFTPipeline:
    """End-to-end GIFT computation pipeline."""

    def __init__(self, config: PipelineConfig):
        self.config = config
        self.k7 = TCSManifold.from_kovalev()
        self.model = G2PINN()

    def run(self) -> PipelineResult:
        """Execute full pipeline."""

        # Phase 1: Train G₂ metric
        trainer = G2Trainer()
        train_result = trainer.train(self.model, self.config.train)

        # Phase 2: Extract harmonic forms
        extractor = HarmonicExtractor(self.model.metric)
        basis_2 = extractor.extract_basis(degree=2, num_forms=21)
        basis_3 = extractor.extract_basis(degree=3, num_forms=77)

        # Phase 3: Compute Yukawa
        yukawa = YukawaTensor(basis_2, basis_3)
        masses = yukawa.mass_eigenvalues()

        # Phase 4: Generate certificate
        cert = G2Certificate(
            det_g=self.model.certified_det_g(),
            kappa_t=self.model.certified_kappa_t(),
            betti_2=len(basis_2),
            betti_3=len(basis_3)
        )

        return PipelineResult(
            metric=self.model,
            harmonic_basis=(basis_2, basis_3),
            yukawa=yukawa,
            masses=masses,
            certificate=cert
        )
```

---

## Testing Strategy

### Unit Tests

```python
# tests/test_k3.py
def test_k3_betti():
    k3 = KummerK3()
    assert k3.betti == [1, 0, 22, 0, 1]
    assert k3.euler == 24

# tests/test_tcs.py
def test_tcs_betti():
    k7 = TCSManifold.from_kovalev()
    assert k7.betti_numbers()[3] == 77

# tests/test_g2.py
def test_g2_det():
    phi = G2Form.standard()
    assert abs(phi.det_g - 65/32) < 1e-10
```

### Integration Tests

```python
# tests/test_pipeline.py
def test_full_pipeline():
    pipeline = GIFTPipeline(config)
    result = pipeline.run()

    assert result.certificate.verify()
    assert result.certificate.betti_3 == 77
    assert abs(result.certificate.det_g.center - 2.03125) < 0.01
```

---

## My Recommendation

### What I Would Do

1. **Start with Phase 1** - Port the validated Python code from `private` to `core` with proper packaging and tests. This is low-risk and provides immediate value.

2. **Phase 2-3 in parallel** - The G₂ structure and PINN can be developed together since they're interdependent.

3. **Phase 4 depends on 2-3** - Harmonic extraction needs a working metric, so this comes after.

4. **Phase 5 is crucial** - The verification/certificate system is what makes this "beyond Joyce" - machine-verifiable numerical bounds that feed into Lean proofs.

### Key Innovation Opportunities

1. **Certified Numerics**: Use interval arithmetic throughout to get rigorous bounds, not just floating-point approximations.

2. **Differentiable Everything**: Make the entire pipeline differentiable so you can backprop from physics losses (mass errors) to geometric parameters.

3. **Active Learning**: Use the `meta_hodge` curiosity-driven exploration to find interesting regions of moduli space.

4. **Lean Integration**: Every numerical result should come with a Lean-verifiable certificate.

### Timeline

| Week | Phase | Deliverable |
|------|-------|-------------|
| 1-2 | Phase 1 | Core geometry module |
| 2-3 | Phase 2 | G₂ form + constraints |
| 3-4 | Phase 3 | PINN training pipeline |
| 4-5 | Phase 4 | Harmonic forms + Yukawa |
| 5-6 | Phase 5 | Verification + integration |

**Total**: ~6 weeks to production-ready K₇ implementation in core.

---

## Files to Create

```
core/
├── geometry/
│   ├── __init__.py
│   ├── k3_surface.py           # ~200 lines
│   ├── acyl_cy3.py             # ~150 lines
│   ├── tcs_construction.py     # ~300 lines
│   └── k7_metric.py            # ~400 lines
├── g2/
│   ├── __init__.py
│   ├── g2_form.py              # ~350 lines
│   ├── holonomy.py             # ~150 lines
│   ├── torsion.py              # ~200 lines
│   └── constraints.py          # ~150 lines
├── harmonic/
│   ├── __init__.py
│   ├── hodge_laplacian.py      # ~300 lines
│   ├── harmonic_forms.py       # ~250 lines
│   └── betti_validation.py     # ~100 lines
├── physics/
│   ├── __init__.py
│   ├── yukawa_tensor.py        # ~200 lines
│   ├── mass_spectrum.py        # ~150 lines
│   └── coupling_constants.py   # ~100 lines
├── nn/
│   ├── __init__.py
│   ├── g2_pinn.py              # ~200 lines
│   ├── fourier_features.py     # ~50 lines
│   ├── training.py             # ~300 lines
│   └── loss_functions.py       # ~150 lines
├── verification/
│   ├── __init__.py
│   ├── numerical_bounds.py     # ~200 lines
│   ├── lean_export.py          # ~150 lines
│   └── certificate.py          # ~200 lines
└── pipeline/
    ├── __init__.py
    ├── full_pipeline.py        # ~250 lines
    └── config.py               # ~100 lines

Total: ~4,500 lines of Python
Tests: ~1,500 lines additional
```

---

*Plan created: December 2025*
*Ready for implementation in gift-framework/core*
