# Contributing

Contributions to the GIFT framework are welcome. This page explains how to contribute.

## Ways to Contribute

### Report Issues

Found a bug or have a question? Open an issue on GitHub:

- [Core repository issues](https://github.com/gift-framework/core/issues)
- [Main framework issues](https://github.com/gift-framework/GIFT/issues)

### Suggest Improvements

Ideas for new features, better documentation, or corrections are welcome. Please open an issue to discuss before starting work.

### Submit Code

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Run tests
5. Submit a pull request

## Development Setup

### Python Package

```bash
git clone https://github.com/gift-framework/core.git
cd core
pip install -e ".[dev]"
pytest
```

### Lean 4 Proofs

```bash
cd Lean
lake build
```

### Coq Proofs

```bash
cd COQ
make
```

## Code Standards

### Python

- Follow PEP 8
- Use type hints
- Write docstrings for public functions
- Add tests for new functionality

```python
def compute_weinberg_angle(b2: int, b3: int, dim_g2: int) -> Fraction:
    """
    Compute the Weinberg angle from Betti numbers.
    
    Args:
        b2: Second Betti number
        b3: Third Betti number
        dim_g2: Dimension of G₂
        
    Returns:
        sin²θ_W as an exact fraction
    """
    return Fraction(b2, b3 + dim_g2)
```

### Lean 4

- Follow Mathlib conventions
- Include docstrings for theorems
- No `sorry` statements in final code

```lean
/-- The Weinberg angle sin²θ_W = b₂/(b₃ + dim G₂) equals 3/13 -/
theorem weinberg_angle_exact : (21 : ℚ) / 91 = 3 / 13 := by
  norm_num
```

### Coq

- Follow standard Coq conventions
- Include comments for complex proofs
- No `Admitted` statements in final code

```coq
(** The Weinberg angle sin²θ_W = b₂/(b₃ + dim G₂) equals 3/13 *)
Theorem weinberg_angle_exact : 21 # 91 == 3 # 13.
Proof. reflexivity. Qed.
```

## Testing

### Python Tests

```bash
pytest tests/
pytest tests/ -v  # verbose
pytest tests/ --cov=gift_core  # with coverage
```

### Proof Verification

For Lean and Coq, successful compilation is the test:

```bash
# Lean
cd Lean && lake build

# Coq
cd COQ && make
```

## Documentation

Documentation uses MkDocs with the Material theme.

### Build Locally

```bash
pip install mkdocs mkdocs-material mkdocstrings[python]
mkdocs serve
```

### Writing Documentation

- Use clear, concise language
- Include code examples
- Use proper mathematical notation with MathJax

## Pull Request Guidelines

1. **One feature per PR**: Keep changes focused
2. **Update tests**: Add tests for new functionality
3. **Update docs**: Document new features
4. **Pass CI**: All checks must pass
5. **Clear description**: Explain what and why

## Review Process

1. Maintainers will review your PR
2. Address any feedback
3. Once approved, your PR will be merged

## Questions?

- Open an issue for technical questions
- Contact [@GIFTheory](https://x.com/GIFTheory) for other inquiries

## License

By contributing, you agree that your contributions will be licensed under the MIT License.
