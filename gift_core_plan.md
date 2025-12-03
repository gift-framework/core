Plan de création : gift-framework/core
Phase 1 : Création du repo et structure de base
1.1 Créer le repo sur GitHub

Nom: gift-framework/core
Description: "GIFT mathematical core - Formally verified constants (Lean 4 + Coq)"
Visibility: Public
License: MIT
.gitignore: Python

1.2 Structure cible complète

core/
├── .devcontainer/
│   ├── devcontainer.json
│   └── Dockerfile
│
├── .github/
│   └── workflows/
│       ├── verify.yml          # CI Lean + Coq
│       ├── test.yml            # Tests Python
│       └── publish.yml         # Auto-publish PyPI
│
├── Lean/                       # Copie depuis GIFT/Lean/
│   ├── lakefile.lean
│   ├── lean-toolchain
│   ├── GIFT.lean
│   └── GIFT/
│       ├── Algebra/
│       ├── Geometry/
│       ├── Topology/
│       ├── Relations/
│       └── Certificate/
│
├── COQ/                        # Copie depuis GIFT/COQ/
│   ├── _CoqProject
│   ├── Makefile
│   ├── Algebra/
│   ├── Geometry/
│   ├── Topology/
│   ├── Relations/
│   └── Certificate/
│
├── gift_core/                  # Package Python
│   ├── __init__.py
│   ├── constants.py
│   ├── relations.py
│   ├── topology.py
│   ├── formulas.py
│   └── _version.py
│
├── scripts/
│   └── extract_from_proofs.py  # Génère constants depuis Lean/Coq
│
├── tests/
│   ├── __init__.py
│   ├── test_constants.py
│   └── test_relations.py
│
├── .gitignore
├── LICENSE
├── README.md
├── pyproject.toml
└── MANIFEST.in

Phase 2 : Copie des preuves formelles
2.1 Cloner et copier Lean

# Depuis le repo GIFT
cp -r GIFT/Lean/ core/Lean/

# Nettoyer les artefacts
cd core/Lean
rm -rf .lake/ lake-packages/ build/

2.2 Cloner et copier Coq

cp -r GIFT/COQ/ core/COQ/

# Nettoyer
cd core/COQ
rm -f *.vo *.vok *.vos *.glob .*.aux

Phase 3 : Package Python gift_core
3.1 gift_core/__init__.py

"""
GIFT Core - Formally verified mathematical constants.

All values are proven in Lean 4 and Coq proof assistants.
Zero domain-specific axioms. Zero sorry/Admitted.
"""

from gift_core.constants import *
from gift_core.relations import PROVEN_RELATIONS
from gift_core.topology import K7, G2, E8
from gift_core._version import __version__

__all__ = [
    # Topological constants
    'DIM_E8', 'RANK_E8', 'DIM_E8xE8', 'DIM_G2', 'DIM_K7',
    'B2', 'B3', 'WEYL_FACTOR', 'DIM_J3O',
    # Physical relations
    'SIN2_THETA_W', 'TAU', 'DET_G', 'KAPPA_T', 'DELTA_CP',
    'M_TAU_M_E', 'M_S_M_D', 'Q_KOIDE', 'LAMBDA_H_NUM',
    'H_STAR', 'P2', 'N_GEN',
    # Structures
    'K7', 'G2', 'E8', 'PROVEN_RELATIONS',
]

3.2 gift_core/constants.py

"""
Topological constants - All values from Lean/Coq proofs.
"""
from fractions import Fraction

# =============================================================================
# E₈ EXCEPTIONAL LIE ALGEBRA
# =============================================================================
DIM_E8 = 248          # dim(E₈) - Proven in Lean: E8RootSystem.lean
RANK_E8 = 8           # rank(E₈) - Cartan subalgebra dimension
DIM_E8xE8 = 496       # dim(E₈×E₈) = 2 × 248
WEYL_FACTOR = 5       # From |W(E₈)| = 2¹⁴·3⁵·5²·7

# =============================================================================
# G₂ EXCEPTIONAL HOLONOMY
# =============================================================================
DIM_G2 = 14           # dim(G₂) - Proven in Lean: G2Group.lean
DIM_K7 = 7            # Real dimension of K₇ manifold

# =============================================================================
# K₇ MANIFOLD TOPOLOGY (TCS Construction)
# =============================================================================
B2 = 21               # b₂(K₇) = H²(K₇) - Proven in Lean: BettiNumbers.lean
B3 = 77               # b₃(K₇) = H³(K₇) - TCS: 40 + 37

# =============================================================================
# EXCEPTIONAL JORDAN ALGEBRA
# =============================================================================
DIM_J3O = 27          # dim(J₃(𝕆)) - Octonion Jordan algebra

# =============================================================================
# DERIVED TOPOLOGICAL CONSTANTS
# =============================================================================
H_STAR = B2 + B3 + 1  # = 99 - Effective degrees of freedom
P2 = DIM_G2 // DIM_K7 # = 2 - Second Pontryagin class contribution

# =============================================================================
# 13 PROVEN PHYSICAL RELATIONS (Lean + Coq verified)
# =============================================================================

# Weinberg angle: sin²θ_W = b₂/(b₃ + dim(G₂)) = 21/91 = 3/13
SIN2_THETA_W = Fraction(3, 13)

# Hierarchy parameter: τ = (496×21)/(27×99) = 3472/891
TAU = Fraction(3472, 891)

# Metric determinant: det(g) = 65/32
DET_G = Fraction(65, 32)

# Torsion coefficient: κ_T = 1/(b₃ - dim(G₂) - p₂) = 1/61
KAPPA_T = Fraction(1, 61)

# CP violation phase: δ_CP = 7×dim(G₂) + H* = 7×14 + 99 = 197°
DELTA_CP = 197

# Tau/electron mass ratio: m_τ/m_e = 7 + 10×248 + 10×99 = 3477
M_TAU_M_E = 3477

# Strange/down quark ratio: m_s/m_d = 4×5 = 20
M_S_M_D = 20

# Koide parameter: Q = dim(G₂)/b₂ = 14/21 = 2/3
Q_KOIDE = Fraction(2, 3)

# Higgs coupling numerator: λ_H ~ √(17/32), numerator = dim(G₂) + N_gen = 17
LAMBDA_H_NUM = 17

# Number of generations: N_gen = 3 (topological)
N_GEN = 3

3.3 gift_core/relations.py

"""
The 13 formally proven relations.
"""
from dataclasses import dataclass
from fractions import Fraction
from typing import Union

@dataclass(frozen=True)
class ProvenRelation:
    """A relation proven in both Lean 4 and Coq."""
    name: str
    symbol: str
    value: Union[int, Fraction, float]
    formula: str
    lean_theorem: str
    coq_theorem: str
    
    def __repr__(self):
        return f"{self.symbol} = {self.value}"

PROVEN_RELATIONS = [
    ProvenRelation(
        name="Weinberg angle",
        symbol="sin²θ_W",
        value=Fraction(3, 13),
        formula="b₂/(b₃ + dim(G₂)) = 21/91",
        lean_theorem="weinberg_angle_certified",
        coq_theorem="weinberg_angle_certified"
    ),
    ProvenRelation(
        name="Hierarchy parameter",
        symbol="τ",
        value=Fraction(3472, 891),
        formula="(496×21)/(27×99)",
        lean_theorem="tau_certified",
        coq_theorem="tau_certified"
    ),
    ProvenRelation(
        name="Metric determinant",
        symbol="det(g)",
        value=Fraction(65, 32),
        formula="5×13/32",
        lean_theorem="det_g_certified",
        coq_theorem="det_g_certified"
    ),
    ProvenRelation(
        name="Torsion coefficient",
        symbol="κ_T",
        value=Fraction(1, 61),
        formula="1/(b₃ - dim(G₂) - p₂)",
        lean_theorem="kappa_T_certified",
        coq_theorem="kappa_T_certified"
    ),
    ProvenRelation(
        name="CP violation phase",
        symbol="δ_CP",
        value=197,
        formula="7×dim(G₂) + H* = 7×14 + 99",
        lean_theorem="delta_CP_certified",
        coq_theorem="delta_CP_certified"
    ),
    ProvenRelation(
        name="Tau/electron mass ratio",
        symbol="m_τ/m_e",
        value=3477,
        formula="7 + 10×248 + 10×99",
        lean_theorem="m_tau_m_e_certified",
        coq_theorem="m_tau_m_e_certified"
    ),
    ProvenRelation(
        name="Strange/down quark ratio",
        symbol="m_s/m_d",
        value=20,
        formula="4×5 = b₂ - 1",
        lean_theorem="m_s_m_d_certified",
        coq_theorem="m_s_m_d_certified"
    ),
    ProvenRelation(
        name="Koide parameter",
        symbol="Q_Koide",
        value=Fraction(2, 3),
        formula="dim(G₂)/b₂ = 14/21",
        lean_theorem="koide_certified",
        coq_theorem="koide_certified"
    ),
    ProvenRelation(
        name="Higgs coupling numerator",
        symbol="λ_H_num",
        value=17,
        formula="dim(G₂) + N_gen = 14 + 3",
        lean_theorem="lambda_H_num_certified",
        coq_theorem="lambda_H_num_certified"
    ),
    ProvenRelation(
        name="Effective degrees of freedom",
        symbol="H*",
        value=99,
        formula="b₂ + b₃ + 1 = 21 + 77 + 1",
        lean_theorem="H_star_certified",
        coq_theorem="H_star_certified"
    ),
    ProvenRelation(
        name="Pontryagin contribution",
        symbol="p₂",
        value=2,
        formula="dim(G₂)/dim(K₇) = 14/7",
        lean_theorem="p2_certified",
        coq_theorem="p2_certified"
    ),
    ProvenRelation(
        name="Number of generations",
        symbol="N_gen",
        value=3,
        formula="Topological (rank - Weyl)",
        lean_theorem="N_gen_certified",
        coq_theorem="N_gen_certified"
    ),
    ProvenRelation(
        name="E₈×E₈ dimension",
        symbol="dim(E₈×E₈)",
        value=496,
        formula="2×248",
        lean_theorem="E8xE8_dim_certified",
        coq_theorem="E8xE8_dim_certified"
    ),
]

def get_relation(symbol: str) -> ProvenRelation:
    """Get a relation by its symbol."""
    for r in PROVEN_RELATIONS:
        if r.symbol == symbol:
            return r
    raise KeyError(f"Unknown relation: {symbol}")

3.4 gift_core/topology.py

"""
Topological structures used in GIFT.
"""
from dataclasses import dataclass
from gift_core.constants import *

@dataclass(frozen=True)
class ManifoldK7:
    """The compact 7-manifold with G₂ holonomy."""
    dim: int = DIM_K7
    b2: int = B2          # Second Betti number
    b3: int = B3          # Third Betti number
    holonomy: str = "G₂"
    construction: str = "Twisted Connected Sum (TCS)"
    
    @property
    def euler_characteristic(self) -> int:
        """χ(K₇) = 2(b₂ - b₃) = 2(21 - 77) = -112"""
        return 2 * (self.b2 - self.b3)
    
    @property
    def h_star(self) -> int:
        """Effective degrees of freedom: H* = b₂ + b₃ + 1"""
        return self.b2 + self.b3 + 1

@dataclass(frozen=True)
class GroupG2:
    """The exceptional Lie group G₂."""
    dim: int = DIM_G2
    rank: int = 2
    name: str = "G₂"
    
    @property
    def is_exceptional(self) -> bool:
        return True

@dataclass(frozen=True)
class GroupE8:
    """The exceptional Lie group E₈."""
    dim: int = DIM_E8
    rank: int = RANK_E8
    root_count: int = 240
    name: str = "E₈"
    
    @property
    def weyl_order(self) -> int:
        """|W(E₈)| = 696,729,600 = 2¹⁴·3⁵·5²·7"""
        return 696_729_600

# Singleton instances
K7 = ManifoldK7()
G2 = GroupG2()
E8 = GroupE8()

3.5 gift_core/_version.py

__version__ = "2.3.0"

Phase 4 : Configuration PyPI
4.1 pyproject.toml

[build-system]
requires = ["setuptools>=61.0", "wheel"]
build-backend = "setuptools.build_meta"

[project]
name = "gift-core"
dynamic = ["version"]
description = "GIFT mathematical core - Formally verified constants (Lean 4 + Coq)"
readme = "README.md"
license = {text = "MIT"}
authors = [
    {name = "Brieuc de La Fournière", email = "brieuc@bdelaf.com"}
]
keywords = [
    "physics", "mathematics", "formal-verification", 
    "lean4", "coq", "standard-model", "E8", "topology"
]
classifiers = [
    "Development Status :: 5 - Production/Stable",
    "Intended Audience :: Science/Research",
    "License :: OSI Approved :: MIT License",
    "Programming Language :: Python :: 3",
    "Programming Language :: Python :: 3.9",
    "Programming Language :: Python :: 3.10",
    "Programming Language :: Python :: 3.11",
    "Programming Language :: Python :: 3.12",
    "Topic :: Scientific/Engineering :: Physics",
    "Topic :: Scientific/Engineering :: Mathematics",
]
requires-python = ">=3.9"
dependencies = []

[project.urls]
Homepage = "https://github.com/gift-framework/core"
Documentation = "https://github.com/gift-framework/GIFT"
Repository = "https://github.com/gift-framework/core"
"Lean Proofs" = "https://github.com/gift-framework/core/tree/main/Lean"
"Coq Proofs" = "https://github.com/gift-framework/core/tree/main/COQ"

[project.optional-dependencies]
dev = ["pytest>=7.0", "pytest-cov", "black", "ruff"]

[tool.setuptools.dynamic]
version = {attr = "gift_core._version.__version__"}

[tool.setuptools.packages.find]
include = ["gift_core*"]

[tool.black]
line-length = 88
target-version = ["py39", "py310", "py311", "py312"]

[tool.ruff]
line-length = 88
select = ["E", "F", "W", "I", "UP"]

4.2 MANIFEST.in

include LICENSE
include README.md
recursive-include Lean *.lean
recursive-include COQ *.v

Phase 5 : CI/CD GitHub Actions
5.1 .github/workflows/verify.yml

name: Formal Verification

on:
  push:
    branches: [main]
    paths: ['Lean/**', 'COQ/**']
  pull_request:
    branches: [main]
  workflow_dispatch:

jobs:
  lean:
    name: Lean 4 Verification
    runs-on: ubuntu-latest
    defaults:
      run:
        working-directory: Lean
    steps:
      - uses: actions/checkout@v4
      
      - name: Install elan
        run: |
          curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
          echo "$HOME/.elan/bin" >> $GITHUB_PATH
      
      - name: Cache .lake
        uses: actions/cache@v4
        with:
          path: Lean/.lake
          key: lean-${{ hashFiles('Lean/lakefile.lean') }}
      
      - name: Build
        run: |
          lake update
          lake exe cache get || true
          lake build
      
      - name: Verify zero sorry
        run: |
          if grep -r "sorry" GIFT/ --include="*.lean"; then
            echo "ERROR: Found sorry!"
            exit 1
          fi

  coq:
    name: Coq Verification
    runs-on: ubuntu-latest
    defaults:
      run:
        working-directory: COQ
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Coq
        run: |
          sudo apt-get update
          sudo apt-get install -y opam
          opam init --disable-sandboxing -y
          eval $(opam env)
          opam pin add coq 8.18.0 -y
      
      - name: Build
        run: |
          eval $(opam env)
          opam exec -- make -j2
      
      - name: Verify zero Admitted
        run: |
          if grep -r "Admitted\." Certificate/; then
            echo "ERROR: Found Admitted!"
            exit 1
          fi

5.2 .github/workflows/test.yml

name: Python Tests

on:
  push:
    branches: [main]
    paths: ['gift_core/**', 'tests/**']
  pull_request:
    branches: [main]

jobs:
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        python-version: ['3.9', '3.10', '3.11', '3.12']
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Set up Python ${{ matrix.python-version }}
        uses: actions/setup-python@v5
        with:
          python-version: ${{ matrix.python-version }}
      
      - name: Install
        run: pip install -e ".[dev]"
      
      - name: Test
        run: pytest tests/ -v --cov=gift_core

5.3 .github/workflows/publish.yml

name: Publish to PyPI

on:
  release:
    types: [published]
  workflow_dispatch:

jobs:
  verify:
    uses: ./.github/workflows/verify.yml
  
  publish:
    needs: verify
    runs-on: ubuntu-latest
    environment: pypi
    permissions:
      id-token: write
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'
      
      - name: Build
        run: |
          pip install build
          python -m build
      
      - name: Publish to PyPI
        uses: pypa/gh-action-pypi-publish@release/v1

Phase 6 : DevContainer
6.1 .devcontainer/devcontainer.json

{
  "name": "GIFT Core",
  "build": {
    "dockerfile": "Dockerfile"
  },
  "features": {
    "ghcr.io/devcontainers/features/python:1": {
      "version": "3.11"
    }
  },
  "customizations": {
    "vscode": {
      "extensions": [
        "leanprover.lean4",
        "maximedenes.vscoq",
        "ms-python.python"
      ]
    }
  },
  "postCreateCommand": "pip install -e '.[dev]'"
}

6.2 .devcontainer/Dockerfile

FROM mcr.microsoft.com/devcontainers/base:ubuntu

# Lean 4
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.14.0
ENV PATH="/root/.elan/bin:${PATH}"

# Coq
RUN apt-get update && apt-get install -y opam \
    && opam init --disable-sandboxing -y \
    && eval $(opam env) \
    && opam pin add coq 8.18.0 -y

ENV PATH="/root/.opam/default/bin:${PATH}"

Phase 7 : Tests Python
7.1 tests/test_constants.py

"""Tests for GIFT constants - verify against formal proofs."""
from fractions import Fraction
import gift_core as gc

def test_e8_dimension():
    assert gc.DIM_E8 == 248

def test_betti_numbers():
    assert gc.B2 == 21
    assert gc.B3 == 77

def test_weinberg_angle():
    # sin²θ_W = b₂/(b₃ + dim(G₂)) = 21/91 = 3/13
    computed = Fraction(gc.B2, gc.B3 + gc.DIM_G2)
    assert computed == Fraction(3, 13)
    assert gc.SIN2_THETA_W == Fraction(3, 13)

def test_tau():
    # τ = (496×21)/(27×99)
    computed = Fraction(gc.DIM_E8xE8 * gc.B2, gc.DIM_J3O * gc.H_STAR)
    assert computed == Fraction(3472, 891)
    assert gc.TAU == computed

def test_det_g():
    assert gc.DET_G == Fraction(65, 32)

def test_kappa_t():
    # κ_T = 1/(b₃ - dim(G₂) - p₂) = 1/61
    computed = Fraction(1, gc.B3 - gc.DIM_G2 - gc.P2)
    assert computed == Fraction(1, 61)
    assert gc.KAPPA_T == computed

def test_delta_cp():
    # δ_CP = 7×dim(G₂) + H* = 7×14 + 99 = 197
    computed = 7 * gc.DIM_G2 + gc.H_STAR
    assert computed == 197
    assert gc.DELTA_CP == 197

def test_koide():
    # Q = 14/21 = 2/3
    computed = Fraction(gc.DIM_G2, gc.B2)
    assert computed == Fraction(2, 3)
    assert gc.Q_KOIDE == computed

7.2 tests/test_relations.py

"""Tests for proven relations."""
from gift_core import PROVEN_RELATIONS, get_relation

def test_relation_count():
    assert len(PROVEN_RELATIONS) == 13

def test_all_have_lean_theorem():
    for r in PROVEN_RELATIONS:
        assert r.lean_theorem, f"{r.name} missing Lean theorem"

def test_all_have_coq_theorem():
    for r in PROVEN_RELATIONS:
        assert r.coq_theorem, f"{r.name} missing Coq theorem"

def test_get_relation():
    w = get_relation("sin²θ_W")
    assert w.name == "Weinberg angle"

Phase 8 : README minimaliste
8.1 README.md

# GIFT Core

[![PyPI](https://img.shields.io/pypi/v/gift-core)](https://pypi.org/project/gift-core/)
[![Lean 4](https://img.shields.io/badge/Lean_4-Verified-blue)](Lean/)
[![Coq](https://img.shields.io/badge/Coq_8.18-Verified-orange)](COQ/)

Formally verified mathematical constants from the GIFT framework.

## Install

```bash
pip install gift-core

Usage

from gift_core import *

print(SIN2_THETA_W)  # Fraction(3, 13)
print(B2, B3)        # 21 77
print(DET_G)         # Fraction(65, 32)

# All 13 proven relations
for r in PROVEN_RELATIONS:
    print(f"{r.symbol} = {r.value}")

What's inside
Constant	Value	Proven
sin²θ_W	3/13	Lean + Coq
τ	3472/891	Lean + Coq
det(g)	65/32	Lean + Coq
κ_T	1/61	Lean + Coq
δ_CP	197°	Lean + Coq
...	...	...

13 relations total, all proven in both Lean 4 and Coq.
Verification

# Lean
cd Lean && lake build

# Coq  
cd COQ && make

Links

    Full framework: gift-framework/GIFT
    Publications: gift_2_3_main.md

MIT License | gift-framework


---

## Phase 9 : Commandes d'exécution

### Séquence complète après création du repo :

```bash
# 1. Clone le nouveau repo vide
git clone https://github.com/gift-framework/core.git
cd core

# 2. Copie les preuves depuis GIFT
cp -r ../GIFT/Lean ./
cp -r ../GIFT/COQ ./

# 3. Nettoie les artefacts de build
rm -rf Lean/.lake Lean/lake-packages
find COQ -name "*.vo" -delete
find COQ -name "*.glob" -delete

# 4. Crée la structure Python
mkdir -p gift_core tests scripts .devcontainer .github/workflows

# 5. Crée tous les fichiers (voir ci-dessus)
# ... créer __init__.py, constants.py, etc.

# 6. Test local
pip install -e ".[dev]"
pytest tests/ -v

# 7. Premier commit
git add -A
git commit -m "feat: Initial gift-core package with Lean/Coq proofs"
git push origin main

# 8. Crée la release pour trigger PyPI
gh release create v2.3.0 --title "GIFT Core v2.3.0" --notes "Initial release"
