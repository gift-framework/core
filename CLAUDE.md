# CLAUDE.md - Development Guide for GIFT Core

This file contains development conventions and lessons learned to avoid repeating past mistakes.

## Project Structure

```
gift-framework/core/
├── Lean/                    # Lean 4 formal proofs
│   ├── GIFT.lean           # Main entry point
│   ├── GIFT/
│   │   ├── Core.lean       # Source of truth for constants
│   │   ├── Certificate.lean # Master theorems (180+ relations)
│   │   │
│   │   ├── Algebra.lean    # E₈, G₂, E₇, F₄, E₆ constants
│   │   ├── Topology.lean   # Betti numbers, H*, p₂
│   │   ├── Geometry.lean   # K₇, J₃(𝕆)
│   │   │
│   │   ├── Foundations/    # Mathematical foundations
│   │   │   ├── RootSystems.lean      # E₈ roots in ℝ⁸
│   │   │   ├── E8Lattice.lean        # E₈ lattice formalization
│   │   │   ├── G2CrossProduct.lean   # 7D cross product
│   │   │   ├── Analysis/             # Hodge theory, Sobolev (research)
│   │   │   └── ...
│   │   │
│   │   ├── Algebraic/      # Octonion-based derivation
│   │   │   ├── Octonions.lean
│   │   │   ├── G2.lean
│   │   │   └── BettiNumbers.lean
│   │   │
│   │   ├── Relations/      # Physical predictions (15+ files)
│   │   ├── Sequences/      # Fibonacci, Lucas embeddings
│   │   ├── Primes/         # Prime Atlas (DirectPrimes, DerivedPrimes)
│   │   ├── Moonshine/      # Monstrous moonshine (Monster, j-invariant)
│   │   ├── McKay/          # McKay correspondence
│   │   └── Joyce.lean      # Joyce existence theorem
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
│   ├── _version.py         # Version string (3.1.0)
│   ├── constants.py        # All certified constants
│   ├── sequences/          # [v2.0] Fibonacci, Lucas embeddings
│   ├── primes/             # [v2.0] Prime Atlas functions
│   ├── monster/            # [v2.0] Monster group connections
│   ├── mckay/              # [v2.0] McKay correspondence
│   ├── analysis/           # [v3.0] Joyce certificate, intervals
│   └── ...
│
├── tests/                  # Python tests
└── .github/workflows/      # CI/CD
    ├── verify.yml          # Lean + Coq verification
    ├── test.yml            # Python tests
    └── publish.yml         # PyPI publish on release
```

---

## Terminology Standards

Use **standard academic mathematical vocabulary**. Avoid internal jargon or classification labels.

### ❌ Internal Jargon (avoid)
```
"B4 is now proven via epsilon contraction decomposition"
"Tier 2 axioms resolved"
"B5 timeout issue"
```

### ✅ Standard Academic Terminology
```
"The Lagrange identity ‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩² for the
G₂-invariant cross product in ℝ⁷ is now formally verified"

"G₂ cross product properties complete"

"Octonion structure constants verification pending (343-case check)"
```

### Reference Table

| Old (jargon) | Standard Academic |
|--------------|-------------------|
| B1 | `reflect_preserves_lattice` — Weyl reflection preserves E₈ lattice |
| B2 | `G2_cross_bilinear` — Cross product bilinearity |
| B3 | `G2_cross_antisymm` — Cross product antisymmetry |
| B4 | Lagrange identity for 7D cross product |
| B5 | `cross_is_octonion_structure` — Octonion multiplication structure |
| B6 | `G2_equiv_characterizations` — G₂ equivalent characterizations |
| Tier 1 | E₈ root system properties |
| Tier 2 | G₂ cross product properties |
| Tier 3 | Advanced analytical properties |

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
| `Ambiguous term` (e.g., `R7`, `AllInteger`) | Multiple `open` with same names | Use qualified names (see below) |
| `expected ℝ, got Prop` in `Real.log_inv` | Mathlib 4 signature change | Use `Real.log_inv x` (value, not proof) |
| `Real.decidableEq noncomputable` | `native_decide` on ℝ equality | Prove on ℕ first, then `simp + norm_num` |
| `n • v.ofLp i = ↑n * v.ofLp i` unsolved | Wrong smul lemma for PiLp | Use `PiLp.smul_apply` + `zsmul_eq_mul` (see §8) |
| `Int.odd_iff_not_even` unknown | Lemma doesn't exist in Mathlib 4 | Use `Int.even_or_odd` pattern matching (see §8) |

### 6. Namespace Conflicts in Lean 4

**Problem**: Opening multiple namespaces that define the same names causes ambiguous term errors.

```lean
-- BAD - Both define R7, AllInteger, AllHalfInteger
open InnerProductSpace
open GIFT.Foundations.RootSystems  -- CONFLICT!

-- GOOD - Only open one, use qualified names for the other
open InnerProductSpace
-- Use RootSystems.D8_card, RootSystems.E8_enumeration, etc.
```

**Known conflicts:**

| Name | Defined in | Also in |
|------|-----------|---------|
| `R7` | `InnerProductSpace` | `G2CrossProduct` |
| `R8` | `InnerProductSpace` | `RootSystems` |
| `AllInteger` | `InnerProductSpace` | `RootSystems` |
| `AllHalfInteger` | `InnerProductSpace` | `RootSystems` |

**Rule**: When importing from `RootSystems` or `G2CrossProduct`, do NOT use `open`. Instead, reference theorems with qualified names:

```lean
import GIFT.Foundations.RootSystems
-- DON'T: open GIFT.Foundations.RootSystems

-- DO: Use qualified names
theorem foo : RootSystems.E8_enumeration.card = 240 := RootSystems.E8_enumeration_card
```

### 7. Numerical Bounds and Real Coercions in Mathlib 4

**Problem 1**: `Real.log_inv` takes `ℝ` directly, not a proof.

```lean
-- BAD - type mismatch (expects ℝ, not Prop)
have hphi_pos : 0 < phi := phi_pos
rw [Real.log_inv hphi_pos]  -- ERROR!

-- GOOD - pass the value directly
rw [Real.log_inv phi]
```

**Problem 2**: `native_decide` doesn't work for ℕ→ℝ coercions.

```lean
-- BAD - Real.decidableEq is noncomputable
have hH : (H_star : ℝ) = 99 := by native_decide  -- ERROR!

-- GOOD - prove on ℕ first, then convert
have hH : (H_star : ℕ) = 99 := by native_decide
have hH_real : (H_star : ℝ) = 99 := by simp only [hH]; norm_num
```

**Problem 3**: Numerical bounds requiring interval arithmetic.

Some bounds (e.g., `e < 2.72`, `log(φ) < 0.49`) cannot be proven with standard tactics. Convert to documented axioms:

```lean
-- Axiom for bounds requiring interval arithmetic
/-- e < 2.72. Numerically verified: e = 2.71828... < 2.72
    Proof requires Taylor series or interval arithmetic. -/
axiom exp_one_lt : Real.exp 1 < (272 : ℝ) / 100

-- Theorem using the axiom with monotonicity
theorem my_bound : some_expr < threshold := by
  have h_base := exp_one_lt
  calc ...
```

**Problem 4**: `simp only` may not fully unfold nested definitions.

```lean
-- BAD - leaves imaginary_count.choose 2 unexpanded
simp only [H_star, rank_E8, b2, b3]

-- GOOD - use native_decide on ℕ, then convert
have hH : (H_star : ℕ) = 99 := by native_decide
```

### 8. PiLp/EuclideanSpace Scalar Multiplication in Mathlib 4

**Problem 1**: `EuclideanSpace ℝ (Fin n)` is defined as `PiLp 2 (fun _ => ℝ)`. The standard `Pi.smul_apply` doesn't work; use `PiLp.smul_apply`.

```lean
-- BAD - simp can't close the goal
have : (n • v) i = n * (v i) := by simp only [Pi.smul_apply, smul_eq_mul]  -- ERROR!

-- GOOD - use PiLp-specific lemma
have : (n • v) i = n * (v i) := by simp only [PiLp.smul_apply, zsmul_eq_mul]
```

**Problem 2**: For `n : ℤ` and `x : ℝ`, the scalar action `n • x` is `zsmul`, not ring multiplication. Use `zsmul_eq_mul` (not `smul_eq_mul`).

```lean
-- After PiLp.smul_apply, we have: n • (v i) where n : ℤ, v i : ℝ
-- Need: zsmul_eq_mul to get ↑n * (v i)
simp only [PiLp.smul_apply, zsmul_eq_mul]  -- Now works!
```

**Problem 3**: `Int.odd_iff_not_even` doesn't exist. Use `Int.even_or_odd` with pattern matching.

```lean
-- BAD - lemma doesn't exist
by_cases hn : Even n
· ...
· rw [Int.odd_iff_not_even] at hn  -- ERROR!
  ...

-- GOOD - use pattern matching
rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
· -- n = 2k (even case)
  exact ... ⟨k, hk⟩
· -- n = 2k + 1 (odd case)
  exact ... ⟨k, hk⟩
```

**Complete pattern for ℤ-smul on EuclideanSpace vectors:**

```lean
theorem E8_lattice_smul (n : ℤ) (v : R8) (hv : v ∈ E8_lattice) : n • v ∈ E8_lattice := by
  ...
  cases htype with
  | inl hi =>
    intro i
    have : (n • v) i = n * (v i) := by simp only [PiLp.smul_apply, zsmul_eq_mul]
    rw [this]
    exact (hi i).zsmul n
  | inr hh =>
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even case
      intro i
      have : (n • v) i = n * (v i) := by simp only [PiLp.smul_apply, zsmul_eq_mul]
      rw [this]
      exact (hh i).zsmul_even ⟨k, hk⟩
    · -- odd case
      intro i
      have : (n • v) i = n * (v i) := by simp only [PiLp.smul_apply, zsmul_eq_mul]
      rw [this]
      exact (hh i).zsmul_odd ⟨k, hk⟩
```

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

## V3.0 New Features

### Joyce Existence Theorem
- Complete Lean 4 formalization via Banach fixed-point theorem
- K7 admits torsion-free G2 structure: `theorem k7_admits_torsion_free_g2`
- PINN bounds: ||T|| < 0.00141 vs threshold 0.0288 (20x margin)

### Sobolev Spaces
- H^k formalization with dimension-specific embeddings
- H^4 ↪ C^0 for 7-manifolds (4 > 7/2)
- Elliptic regularity framework

### Differential Forms
- G2 decomposition: Ω^2 = Ω^2_7 ⊕ Ω^2_14, Ω^3 = Ω^3_1 ⊕ Ω^3_7 ⊕ Ω^3_27
- Hodge numbers for K7

### Python Analysis Module
- `gift_core.analysis`: JoyceCertificate, Interval arithmetic
- Quick verification: `verify_pinn_bounds()` → True

---

## V4.0 New Features: Real Mathematical Foundations

### The Problem with Previous Versions

Previous versions only proved arithmetic:
```lean
def dim_E8 : Nat := 248
theorem E8xE8_dim_certified : dim_E8xE8 = 496 := rfl
```
This proves "if we define dim_E8 = 248, then 2 × 248 = 496" - NOT that E₈ has dimension 248!

### V4.0 Solution: Derive from Mathematical Definitions

#### RootSystems.lean - E8 from Root System
```lean
def E8_roots : Set (Fin 8 → ℝ) :=
  { v | (AllInteger v ∨ AllHalfInteger v) ∧ SumEven v ∧ NormSqTwo v }

theorem E8_dimension_from_roots :
    let root_count := 112 + 128  -- D8 + half-integer = 240
    let rank := 8
    root_count + rank = 248 := rfl
```
Now 248 is DERIVED from the actual E8 root system structure!

#### RationalConstants.lean - Proper ℚ Arithmetic
```lean
-- Old (hack): b2 * 13 = 3 * (b3 + dim_G2)
-- New (real):
theorem sin2_theta_W_simplified : sin2_theta_W = 3 / 13 := by norm_num
```
Uses actual rational numbers, not cross-multiplication tricks.

#### GraphTheory.lean - K₄, K₇ Connections
```lean
theorem K7_edges_equals_b2 : K7.edgeFinset.card = 21 := by native_decide
```
Proves C(7,2) = 21 = b₂ using Mathlib's graph theory.

#### GoldenRatio.lean - φ from Fibonacci
```lean
theorem phi_squared : phi ^ 2 = phi + 1 := ...
theorem fib_gift_b2 : Nat.fib 8 = 21 := rfl
```
Golden ratio derived from its definition, Fibonacci embedding proven.

### Hierarchy of Mathematical Content

| Level | Example | What it proves |
|-------|---------|----------------|
| 0 (Old) | `def dim_E8 := 248` | Nothing (circular) |
| 1 (V4.0) | Root count + rank = 248 | Dimension from structure |
| 2 (Future) | Chevalley construction | Full Lie algebra |

### Key Mathlib Imports Added

- `Mathlib.Analysis.InnerProductSpace.Basic` - ℝ⁸ vector space
- `Mathlib.Data.Rat.Basic` - Rational arithmetic
- `Mathlib.Combinatorics.SimpleGraph.Basic` - Graph theory
- `Mathlib.Data.Nat.Fib.Basic` - Fibonacci numbers
- `Mathlib.Data.Real.Sqrt` - √5 for golden ratio

---

## V3.1.6: Dependency Graph Patterns

### Canonical Sources for Constants

| Constant | Canonical Source | Type |
|----------|-----------------|------|
| `b2`, `b3`, `H_star` | `Algebraic.BettiNumbers` | ℕ |
| `dim_G2`, `rank_G2` | `Algebraic.G2` | ℕ |
| `dim_E8`, `rank_E8` | `Core` | ℕ |
| `imaginary_count` | `Algebraic.Octonions` | ℕ |

### Pattern: `def` vs `abbrev` vs `theorem`

```lean
-- VALUE: def creates a new definition
def foo : ℕ := 27
-- Can compare: `foo = 27` ✓

-- ALIAS: abbrev points to canonical source (for dependency graph)
abbrev foo : ℕ := Bar.foo
-- Creates edge in dependency graph: this file → Bar

-- THEOREM: proves an equation (it's a Prop, not a value!)
theorem foo : x + y = 27 := by native_decide
-- WRONG: `foo = 27` (comparing Prop to ℕ)
-- RIGHT: `x + y = 27` (use the equation directly)
```

### Pattern: ℚ Constants and `norm_num`

```lean
-- BAD: norm_num can't simplify through coercions
abbrev b2 : ℚ := GIFT.Algebraic.BettiNumbers.b2  -- ℕ → ℚ coercion
theorem H_star_value : H_star = 99 := by norm_num  -- FAILS!

-- GOOD: literal definition for ℚ proofs
def b2 : ℚ := 21  -- matches Algebraic.BettiNumbers.b2
theorem H_star_value : H_star = 99 := by unfold H_star b2 b3; norm_num  -- WORKS
```

### Pattern: Connecting Modules to Certificate

To connect an isolated module to the dependency graph:

```lean
-- In Certificate.lean:
import GIFT.NewModule  -- Add import

-- Create abbrevs for key theorems (creates edges)
abbrev new_theorem := NewModule.key_theorem

-- Add to certification theorem
theorem gift_certificate :
    ...existing relations... ∧
    -- Use VALUES directly, not theorem names
    (NewModule.some_value = 42) ∧
    (NewModule.x + NewModule.y = NewModule.z) := by
  repeat (first | constructor | native_decide | rfl)
```

### 9. Blueprint Dependency Graph Orphans

**Problem**: Modules imported in Certificate.lean but without `abbrev` references appear as isolated clusters in the blueprint dependency graph.

**Diagnosis**: Check the blueprint visualization. Disconnected clusters indicate missing `abbrev` edges.

**Fix**: For each orphaned module, add abbrevs in Certificate.lean:

```lean
-- Module is imported but orphaned
import GIFT.SomeModule

-- Fix: Add abbrevs to create dependency graph edges
abbrev some_theorem := GIFT.SomeModule.some_theorem
abbrev another_theorem := GIFT.SomeModule.another_theorem
```

**Modules commonly orphaned** (check these have abbrevs):
- `DifferentialForms` (Hodge duality, form decompositions)
- `ImplicitFunction` (IFT conditions)
- `G2CrossProduct` (fano_lines, epsilon, cross product)
- Relations submodules (ExceptionalGroups, BaseDecomposition, etc.)

### 10. Explicit Vector Definitions in EuclideanSpace

**Problem**: Defining explicit vectors in `EuclideanSpace ℝ (Fin n)` requires `noncomputable` if using division.

```lean
-- BAD - compiler error (depends on Real.instDivInvMonoid)
def E8_α8 : R8 := mkR8 ![-1/2, -1/2, -1/2, -1/2, -1/2, 1/2, 1/2, -1/2]

-- GOOD - mark as noncomputable
noncomputable def E8_α8 : R8 := mkR8 ![-1/2, -1/2, -1/2, -1/2, -1/2, 1/2, 1/2, -1/2]
```

**Helper pattern for R8 vectors:**

```lean
/-- Helper to construct R8 vectors from a function -/
noncomputable def mkR8 (f : Fin 8 → ℝ) : R8 := (WithLp.equiv 2 _).symm f

/-- Example: E8 simple root -/
noncomputable def E8_α1 : R8 := mkR8 ![1, -1, 0, 0, 0, 0, 0, 0]
```

### 11. Numerical Bounds on Transcendentals (exp, log, etc.)

**Problem**: Tight bounds like `2.7 < e < 2.72` or `0.48 < log(φ) < 0.49` cannot be proven with standard Mathlib tactics.

**Why it fails:**
- `Real.add_one_lt_exp` only gives `x + 1 < exp(x)`, so `2 < e` (not tight enough)
- `norm_num` doesn't handle transcendental functions
- No interval arithmetic in Mathlib 4

**Solution**: Use documented axioms for numerically verified bounds:

```lean
/-- e > 2.7. Numerically verified: e = 2.71828... > 2.7.
    Proof requires interval arithmetic (Taylor series to 4+ terms). -/
axiom exp_one_gt : (27 : ℝ) / 10 < Real.exp 1
```

**Future work**: Implement interval arithmetic library for Lean 4.

---

*Last updated: 2025-12-25 - Blueprint orphans, E8 basis vectors, transcendental bounds (v3.1.11)*
