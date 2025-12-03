# Installation

## From PyPI

The recommended installation method:

```bash
pip install giftpy
```

## From Source

Clone the repository and install in development mode:

```bash
git clone https://github.com/gift-framework/core.git
cd core
pip install -e .
```

## Verify Installation

```python
import gift_core
print(gift_core.__version__)
```

## Dependencies

### Python Package

The core Python package has minimal dependencies:

- Python ≥ 3.8
- No external packages required (uses stdlib `fractions`)

### Formal Proofs (Optional)

To verify or modify the proofs:

**Lean 4:**
```bash
cd Lean
curl -sSf https://get.elan-init.app | sh  # Install elan
lake build
```

**Coq:**
```bash
cd COQ
# Requires Coq 8.17+
make
```

## Platform Support

| Platform | Status |
|----------|--------|
| Linux | ✅ Tested |
| macOS | ✅ Tested |
| Windows | ✅ Tested |

## Troubleshooting

### Import Error

If you encounter:
```
ModuleNotFoundError: No module named 'gift_core'
```

Ensure you installed `giftpy` (the PyPI package name), not `gift_core` (the module name):

```bash
pip install giftpy  # Correct
```

### Version Conflicts

To check your installed version:

```bash
pip show giftpy
```

To upgrade:

```bash
pip install --upgrade giftpy
```
