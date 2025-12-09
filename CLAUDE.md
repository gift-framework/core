# CLAUDE.md - Development Guide for GIFT Core

This file contains development conventions and lessons learned to avoid repeating past mistakes.

## Project Structure

```
gift-framework/core/
├── Lean/                    # Lean 4 formal proofs
│   ├── GIFT.lean           # Main entry point (v2.0.0)
│   ├── GIFT/
│   │   ├── Algebra.lean    # E8, G2, E7, F4, E6 constants
│   │   ├── Topology.lean   # Betti numbers, H*, p2
│   │   ├── Geometry.lean   # K7, J3(O)
│   │   ├── Relations.lean  # Original 13 relations
│   │   ├── Relations/      # Extension modules (11 files)
│   │   ├── Sequences/      # [v2.0] Fibonacci, Lucas, Recurrence
│   │   ├── Primes/         # [v2.0] Prime Atlas (Tier 1-4, Heegner)
│   │   ├── Monster/        # [v2.0] Monster dimension, j-invariant
│   │   ├── McKay/          # [v2.0] McKay correspondence
│   │   └── Certificate.lean # Master theorems (165+ relations)
│   └── lakefile.lean
│
├── COQ/                     # Coq formal proofs
│   ├── _CoqProject         # MUST list all .v files
│   ├── Algebra/
│   ├── Topology/
│   ├── Geometry/
│   ├── Relations/
│   └── Certificate/
│
├── gift_core/              # Python package
│   ├── __init__.py         # Exports (update when adding constants!)
│   ├── _version.py         # Version string (2.0.0)
│   ├── constants.py        # All certified constants
│   ├── sequences/          # [v2.0] Fibonacci, Lucas embeddings
│   ├── primes/             # [v2.0] Prime Atlas functions
│   ├── monster/            # [v2.0] Monster group connections
│   ├── mckay/              # [v2.0] McKay correspondence
│   └── ...
│
├── tests/                  # Python tests
└── .github/workflows/      # CI/CD
    ├── verify.yml          # Lean + Coq verification
    ├── test.yml            # Python tests
    └── publish.yml         # PyPI publish on release
```

---

## Critical Rules

### 1. NO UNICODE IN COQ FILES

**Problem**: Coq's parser chokes on UTF-8 characters in comments.

```coq
(* BAD - will fail *)
(** γ_GIFT = (2×rank(E₈) + 5×H*)/(10×dim(G₂) + 3×dim(E₈)) *)

(* GOOD - ASCII only *)
(** gamma_GIFT = (2*rank(E8) + 5*H_star)/(10*dim(G2) + 3*dim(E8)) *)
```

**Forbidden characters**: `×`, `÷`, `₀₁₂₃₄₅₆₇₈₉`, `⁰¹²³⁴⁵⁶⁷⁸⁹`, `θ`, `α`, `β`, `γ`, `δ`, `λ`, `π`, `φ`, `ζ`, `Ω`, `√`, `≈`, `≤`, `≥`, `∧`, `∨`, `→`, `←`

**Use instead**: `theta`, `alpha`, `sqrt`, `<=`, `>=`, `/\`, `\/`, `->`, `<-`

### 2. Lean 4 Theorem Aliases

**Problem**: Can't use `theorem foo := bar` syntax.

```lean
-- BAD - syntax error
theorem all_relations_certified := all_13_relations_certified

-- GOOD - use abbrev
abbrev all_relations_certified := all_13_relations_certified
```

### 3. Update _CoqProject When Adding Files

**Problem**: New `.v` files won't compile if not listed.

```
# COQ/_CoqProject - MUST include ALL .v files in dependency order
-R . GIFT

Algebra/E8.v
Algebra/G2.v
...
Relations/GaugeSector.v    # Don't forget new files!
Relations/NeutrinoSector.v
...
Certificate/AllProven.v    # This depends on Relations/*
```

### 4. Update Python Exports

When adding new constants to `constants.py`:

1. Add to `gift_core/constants.py`
2. Import in `gift_core/__init__.py`
3. Add to `__all__` list in `gift_core/__init__.py`
4. Bump version in `gift_core/_version.py`

### 5. Version Bumping (SemVer)

- `MAJOR.MINOR.PATCH`
- New relations/features → bump MINOR (1.0.0 → 1.1.0)
- Bug fixes only → bump PATCH (1.0.0 → 1.0.1)
- Breaking changes → bump MAJOR (1.0.0 → 2.0.0)

---

## Proof Tactics

### Lean 4

```lean
-- For definitional equalities (most common)
theorem foo : 14 - 2 = 12 := rfl

-- For computed equalities
theorem bar : 2 * rank_E8 + 5 * H_star = 511 := by native_decide

-- For conjunctions
theorem baz : a = 1 ∧ b = 2 := ⟨rfl, rfl⟩

-- For many conjunctions
theorem qux : ... := by
  repeat (first | constructor | native_decide | rfl)
```

### Coq

```coq
(* For definitional equalities *)
Theorem foo : 14 - 2 = 12.
Proof. reflexivity. Qed.

(* For conjunctions *)
Theorem bar : a = 1 /\ b = 2.
Proof. split; reflexivity. Qed.

(* For many conjunctions *)
Theorem baz : ... .
Proof. repeat split; reflexivity. Qed.
```

---

## CI/CD Workflows

### verify.yml
- Triggers on: push, PR
- Builds Lean 4 proofs (`lake build`)
- Builds Coq proofs (`make`)
- Must pass before merge

### test.yml
- Triggers on: push, PR
- Runs Python tests (`pytest`)
- Tests all certified relations

### publish.yml
- Triggers on: GitHub release published
- Verifies proofs first
- Builds and publishes to PyPI
- Uses trusted publishing (OIDC)

**To publish a new version**:
1. Merge PR to main
2. Create GitHub release with tag `vX.Y.Z`
3. Workflow auto-publishes to PyPI

---

## Testing Locally

```bash
# Lean 4
cd Lean && lake build

# Coq
cd COQ && coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile

# Python
python -m pytest tests/ -v

# Quick verification of constants
python -c "from gift_core import *; print(GAMMA_GIFT)"
```

---

## Adding New Certified Relations

1. **Lean**: Create/update file in `Lean/GIFT/Relations/`
2. **Lean**: Add import to `Lean/GIFT/Certificate.lean`
3. **Lean**: Add to master theorem
4. **Coq**: Create/update file in `COQ/Relations/` (ASCII only!)
5. **Coq**: Add to `COQ/_CoqProject`
6. **Coq**: Add to `COQ/Certificate/AllProven.v`
7. **Python**: Add constants to `gift_core/constants.py`
8. **Python**: Export in `gift_core/__init__.py`
9. **Python**: Add tests in `tests/`
10. **Docs**: Update `README.md`
11. **Version**: Bump in `gift_core/_version.py`

---

## Common Errors & Fixes

| Error | Cause | Fix |
|-------|-------|-----|
| `Syntax error: illegal begin of vernac` | Unicode in Coq | Use ASCII only |
| `unexpected token ':='` | Lean4 theorem alias | Use `abbrev` |
| `No rule to make target 'X.vo'` | Missing from _CoqProject | Add file to list |
| `ImportError` | Missing export | Add to `__init__.py` |
| `native_decide failed` | Computation too complex | Split into smaller lemmas |

---

## Topological Constants Reference

| Constant | Value | Definition |
|----------|-------|------------|
| `dim_E8` | 248 | Dimension of E8 |
| `rank_E8` | 8 | Rank of E8 |
| `dim_G2` | 14 | Dimension of G2 |
| `b2` | 21 | Second Betti number |
| `b3` | 77 | Third Betti number |
| `H_star` | 99 | b2 + b3 + 1 |
| `p2` | 2 | Pontryagin class |
| `dim_J3O` | 27 | Jordan algebra dim |
| `Weyl_factor` | 5 | From Weyl group |
| `D_bulk` | 11 | M-theory dimension |

---

---

## V2.0 New Features

### Sequence Embeddings
- Complete Fibonacci embedding: F_3-F_12 = GIFT constants
- Complete Lucas embedding: L_0-L_9 = GIFT constants
- Recurrence proofs: alpha_sum = rank + Weyl, etc.

### Prime Atlas
- **100% coverage** of all primes < 200
- Three-generator structure (b3, H*, dim_E8)
- All 9 Heegner numbers GIFT-expressible

### Golden Ratio Derivation
- Three independent paths: McKay, Fibonacci, G2 spectrum
- Cosmological phi^2: Omega_DE/Omega_DM = 21/8 ~ phi^2

### Monster & McKay
- Monster dimension: 196883 = 47 x 59 x 71 (all GIFT-expressible)
- j-invariant: 744 = 3 x 248 = N_gen x dim_E8
- McKay correspondence: E8 <-> Icosahedron <-> phi

---

*Last updated: 2025-12-09 - 165+ certified relations (v2.0.0)*
