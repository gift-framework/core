---
usemathjax: true
---

# GIFT: Geometric Information Field Theory

GIFT derives Standard Model parameters from E₈ × E₈ gauge theory compactified on G₂-holonomy manifolds, achieving **0.087% mean deviation** across 18 dimensionless predictions with **180+ machine-verified relations**.

## Quick Links

* [**GIFT Blueprint v3.2**]({{ site.baseurl }}/gift_blueprint.html) - Custom D3.js visualization (70+ nodes, 20 layers)
* [Blueprint (web)]({{ site.baseurl }}/blueprint/) - Lean blueprint with proofs
* [Blueprint (pdf)]({{ site.baseurl }}/blueprint.pdf) - Downloadable PDF
* [Dependency Graph]({{ site.baseurl }}/blueprint/dep_graph_document.html) - Proof dependencies
* [API Documentation]({{ site.baseurl }}/docs/) - Lean code documentation

## Key Results

| Constant | GIFT Value | Measured | Deviation |
|----------|------------|----------|-----------|
| sin²θ_W  | 3/13 ≈ 0.2308 | 0.2312 | 0.17% |
| α_EM⁻¹   | 137.036... | 137.036 | <0.001% |
| n_s      | ζ(11)/ζ(5) ≈ 0.965 | 0.965 | 0.03% |

## Repository Structure

```
gift-framework/core/
├── Lean/           # Lean 4 formal proofs (180+ relations)
├── COQ/            # Coq formal proofs
├── blueprint/      # Mathematical documentation
├── gift_core/      # Python package
└── tests/          # Test suite
```

## Getting Started

```bash
# Clone the repository
git clone https://github.com/gift-framework/core.git
cd core

# Build Lean proofs
cd Lean && lake build

# Run Python tests
python -m pytest tests/ -v
```

## Links

* [GitHub Repository](https://github.com/gift-framework/core)
* [Lean Zulip](https://leanprover.zulipchat.com/) - Lean community chat
