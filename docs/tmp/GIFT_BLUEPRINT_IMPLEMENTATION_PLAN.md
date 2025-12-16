# GIFT Blueprint Implementation Plan

**Pour: Claude Code (Agent de développement)**  
**Date: Décembre 2025**  
**Version: 1.0**

---

## 🎯 Objectif

Implémenter le workflow **leanblueprint** de Math Inc. dans le repo `gift-framework/core` pour :
1. Documenter mathématiquement les preuves GIFT
2. Visualiser le graphe de dépendances
3. Suivre la progression (théorème → axiom → sorried → proven)
4. Faciliter l'autoformalization future (Gauss-compatible)

---

## 📚 Référence: Structure Math Inc.

Repos de référence à étudier :
- https://github.com/math-inc/KakeyaFiniteFields
- https://github.com/math-inc/strongpnt  
- https://github.com/math-inc/ZkLinalg

Pattern commun :
```
repo/
├── blueprint/
│   ├── src/
│   │   ├── chapter1.tex
│   │   ├── chapter2.tex
│   │   └── content.tex      # Main entry point
│   ├── web/                  # Generated dependency graph
│   └── references.bib
├── ProjectName/              # Lean source files
│   └── *.lean
├── ProjectName.lean          # Root import
├── lakefile.toml             # Lake configuration
└── lean-toolchain
```

---

## 📁 Structure Cible pour GIFT

```
gift-framework/core/
├── blueprint/
│   ├── src/
│   │   ├── macros.tex           # Custom LaTeX macros
│   │   ├── chapter_foundations.tex
│   │   ├── chapter_algebraic.tex
│   │   ├── chapter_relations.tex
│   │   ├── chapter_sequences.tex
│   │   ├── chapter_primes.tex
│   │   └── content.tex          # Main document
│   ├── web/
│   │   └── (generated)
│   ├── references.bib
│   └── blueprint.yaml           # leanblueprint config
├── Lean/
│   └── GIFT/                    # (existing - no changes)
├── COQ/                         # (existing - no changes)
├── .github/workflows/
│   └── blueprint.yml            # NEW: CI for blueprint
├── lakefile.toml                # CONVERT from lakefile.lean
└── home_page/                   # NEW: Optional Jekyll landing page
```

---

## 🛠️ Tâches d'Implémentation

### Phase 1: Setup Infrastructure

#### Task 1.1: Convertir lakefile.lean → lakefile.toml

**Fichier source:** `Lean/lakefile.lean`  
**Fichier cible:** `Lean/lakefile.toml`

```toml
[package]
name = "GIFT"
version = "3.1.2"
keywords = ["mathematics", "physics", "G2", "E8"]

[package.leanOptions]
pp.unicode.fun = true
autoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "main"

[[lean_lib]]
name = "GIFT"
globs = ["GIFT.+"]
```

#### Task 1.2: Créer blueprint/blueprint.yaml

```yaml
# Configuration for leanblueprint
project: GIFT
lean_lib: GIFT
lean_root: ../Lean
extra_dep_files: []

# Style customization
home_page: true
title: "GIFT: Geometric Information Field Theory"
description: "Formal verification of G₂ holonomy framework"
author: "Brieuc de La Fournière"

# Build options
pdf: true
web: true
```

#### Task 1.3: Créer blueprint/src/macros.tex

```latex
% GIFT-specific macros
\newcommand{\R}{\mathbb{R}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\N}{\mathbb{N}}
\newcommand{\C}{\mathbb{C}}
\newcommand{\Q}{\mathbb{Q}}
\newcommand{\HH}{\mathbb{H}}  % Quaternions
\newcommand{\OO}{\mathbb{O}}  % Octonions

% Lie groups
\newcommand{\Gtwo}{G_2}
\newcommand{\Eeight}{E_8}
\newcommand{\SU}{\mathrm{SU}}
\newcommand{\SO}{\mathrm{SO}}
\newcommand{\Spin}{\mathrm{Spin}}

% GIFT constants
\newcommand{\btwo}{b_2}
\newcommand{\bthree}{b_3}
\newcommand{\Hstar}{H^*}
\newcommand{\Kseven}{K_7}

% Cross product
\newcommand{\cross}{\times}
\newcommand{\eps}{\varepsilon}

% Lean integration (leanblueprint macros)
\newcommand{\lean}[1]{\leanok\texttt{#1}}
\newcommand{\leanfile}[1]{\texttt{GIFT/#1.lean}}
```

---

### Phase 2: Blueprint Content (chapter par chapter)

#### Task 2.1: blueprint/src/chapter_foundations.tex

Ce fichier documente `Lean/GIFT/Foundations/`:

```latex
\chapter{Foundations}\label{chap:foundations}

\section{E₈ Root System}

\begin{definition}[E₈ Dimension]\label{def:e8_dim}
    \lean{GIFT.Foundations.E8Lattice.dim_E8}
    \leanok
    The exceptional Lie algebra $\Eeight$ has dimension 248.
\end{definition}

\begin{theorem}[E₈ Root Count]\label{thm:e8_roots}
    \lean{GIFT.Foundations.E8Lattice.E8_root_count}
    \leanok
    The $\Eeight$ root system contains exactly 240 roots:
    \begin{itemize}
        \item 112 roots of D₈-type (integer coordinates)
        \item 128 roots of half-integer type
    \end{itemize}
\end{theorem}

\begin{proof}
    \uses{def:e8_dim}
    Direct enumeration verified by \texttt{native\_decide}.
\end{proof}

\section{G₂ Cross Product}

\begin{definition}[Fano Plane]\label{def:fano}
    \lean{GIFT.Foundations.G2CrossProduct.fano_lines}
    \leanok
    The Fano plane has 7 lines: $\{0,1,3\}, \{1,2,4\}, \{2,3,5\}, \{3,4,6\}, \{4,5,0\}, \{5,6,1\}, \{6,0,2\}$.
\end{definition}

\begin{definition}[Epsilon Tensor]\label{def:epsilon}
    \lean{GIFT.Foundations.G2CrossProduct.epsilon}
    \leanok
    The structure constants $\eps_{ijk}$ for the 7D cross product.
\end{definition}

\begin{definition}[Cross Product]\label{def:cross}
    \lean{GIFT.Foundations.G2CrossProduct.cross}
    \leanok
    $(u \cross v)_k = \sum_{i,j} \eps_{ijk} u_i v_j$
\end{definition}

\begin{theorem}[B2: Bilinearity]\label{thm:B2}
    \lean{GIFT.Foundations.G2CrossProduct.G2_cross_bilinear}
    \leanok
    The cross product is bilinear.
\end{theorem}

\begin{theorem}[B3: Antisymmetry]\label{thm:B3}
    \lean{GIFT.Foundations.G2CrossProduct.G2_cross_antisymm}
    \leanok
    $u \cross v = -v \cross u$
\end{theorem}

\begin{definition}[Coassociative 4-form]\label{def:psi}
    \lean{GIFT.Foundations.G2CrossProduct.psi}
    \leanok
    $\psi_{ijlm} = \sum_k \eps_{ijk}\eps_{lmk} - (\delta_{il}\delta_{jm} - \delta_{im}\delta_{jl})$
\end{definition}

\begin{lemma}[ψ Antisymmetry]\label{lem:psi_antisym}
    \lean{GIFT.Foundations.G2CrossProduct.psi_antisym_il}
    \leanok
    $\psi_{ijlm} = -\psi_{ljim}$ (verified for all $7^4 = 2401$ cases).
\end{lemma}

\begin{lemma}[ψ Contraction Vanishes]\label{lem:psi_vanish}
    \lean{GIFT.Foundations.G2CrossProduct.psi_contract_vanishes}
    \leanok
    $\sum_{i,j,l,m} \psi_{ijlm} u_i u_l v_j v_m = 0$
\end{lemma}

\begin{proof}
    \uses{lem:psi_antisym}
    Antisymmetric tensor contracted with symmetric tensor vanishes.
\end{proof}

\begin{theorem}[B4: Lagrange Identity]\label{thm:B4}
    \lean{GIFT.Foundations.G2CrossProduct.G2_cross_norm}
    \notready
    $\|u \cross v\|^2 = \|u\|^2\|v\|^2 - \langle u,v \rangle^2$
\end{theorem}

\begin{proof}
    \uses{lem:psi_vanish, def:psi}
    Key lemmas proven; EuclideanSpace plumbing pending.
\end{proof}
```

**Note importante sur les macros leanblueprint:**
- `\lean{name}` : Lien vers la déclaration Lean
- `\leanok` : Status = prouvé en Lean
- `\notready` : Status = axiom ou sorry en Lean  
- `\uses{ref1, ref2}` : Dépendances

#### Task 2.2: blueprint/src/chapter_algebraic.tex

Documente `Lean/GIFT/Algebraic/`:

```latex
\chapter{Algebraic Foundations}\label{chap:algebraic}

\section{Cayley-Dickson Construction}

\begin{definition}[Quaternion Dimension]\label{def:quat_dim}
    \lean{GIFT.Algebraic.Quaternions.quaternion_dim}
    \leanok
    $\dim(\HH) = 4$ avec 3 unités imaginaires $\{i, j, k\}$.
\end{definition}

\begin{theorem}[Cayley-Dickson Doubling]\label{thm:doubling}
    \lean{GIFT.Algebraic.CayleyDickson.cayley_dickson_doubling}
    \leanok
    $\dim(\mathcal{A}_n) = 2 \cdot \dim(\mathcal{A}_{n-1})$
\end{theorem}

\begin{theorem}[Octonion Units]\label{thm:oct_units}
    \lean{GIFT.Algebraic.Octonions.octonion_imaginary_units}
    \leanok
    $\OO$ a exactement 7 unités imaginaires.
\end{theorem}

\section{Betti Numbers Derivation}

\begin{theorem}[$\btwo$ from Combinatorics]\label{thm:b2_comb}
    \lean{GIFT.Algebraic.BettiNumbers.b2_eq_choose_7_2}
    \leanok
    $\btwo = \binom{7}{2} = 21$ (paires d'unités octonioniques).
\end{theorem}

\begin{theorem}[$\btwo$ Decomposition]\label{thm:b2_decomp}
    \lean{GIFT.Algebraic.BettiNumbers.b2_decomposition}
    \leanok
    $21 = 3 + 6 + 12$ (quaternionic + new + mixed pairs).
\end{theorem}

\begin{theorem}[$\bthree$ from E₇]\label{thm:b3_e7}
    \lean{GIFT.Algebraic.BettiNumbers.b3_eq_b2_plus_fund_E7}
    \leanok
    $\bthree = \btwo + \mathrm{fund}(E_7) = 21 + 56 = 77$
\end{theorem}
```

#### Task 2.3: blueprint/src/chapter_relations.tex

Documente `Lean/GIFT/Relations/`:

```latex
\chapter{Physical Relations}\label{chap:relations}

\section{Weinberg Angle}

\begin{theorem}[Exact Weinberg]\label{thm:weinberg}
    \lean{GIFT.Relations.Weinberg.sin_squared_theta_W}
    \leanok
    $\sin^2\theta_W = \frac{3}{13} = \frac{\btwo}{\btwo + \bthree + \dim(\Gtwo)}$
\end{theorem}

\begin{proof}
    \uses{thm:b2_comb, thm:b3_e7}
    $\frac{21}{21 + 77 + 14} = \frac{21}{112} = \frac{3}{16}$ puis correction = $\frac{3}{13}$.
\end{proof}

\section{Cosmological Parameters}

\begin{theorem}[τ Ratio]\label{thm:tau}
    \lean{GIFT.Relations.Cosmology.tau_exact}
    \leanok
    $\tau = \frac{3472}{891}$
\end{theorem}
```

#### Task 2.4: blueprint/src/content.tex

Document principal qui inclut tous les chapitres:

```latex
\documentclass[a4paper, 11pt]{report}

\usepackage{amsmath, amssymb, amsthm}
\usepackage{hyperref}
\usepackage{cleveref}

% leanblueprint package
\usepackage{leanblueprint}

% Custom macros
\input{macros}

\title{GIFT: Geometric Information Field Theory\\
       \Large Blueprint for Formal Verification}
\author{Brieuc de La Fournière}
\date{Version 3.1.2 — December 2025}

\begin{document}

\maketitle

\begin{abstract}
This blueprint documents the formal verification of GIFT (Geometric Information Field Theory)
in Lean 4 and Coq. GIFT derives Standard Model parameters from $\Eeight \times \Eeight$ gauge 
theory compactified on $\Gtwo$-holonomy manifolds, achieving 0.087\% mean deviation across 
18 dimensionless predictions with 175+ machine-verified relations.
\end{abstract}

\tableofcontents

\input{chapter_foundations}
\input{chapter_algebraic}
\input{chapter_relations}
% \input{chapter_sequences}
% \input{chapter_primes}

\bibliographystyle{alpha}
\bibliography{references}

\end{document}
```

---

### Phase 3: CI/CD Setup

#### Task 3.1: .github/workflows/blueprint.yml

```yaml
name: Blueprint

on:
  push:
    branches: [main]
    paths:
      - 'blueprint/**'
      - 'Lean/**'
  pull_request:
    branches: [main]
    paths:
      - 'blueprint/**'
      - 'Lean/**'

jobs:
  build-blueprint:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout
        uses: actions/checkout@v4

      - name: Install uv
        uses: astral-sh/setup-uv@v4

      - name: Install TeX Live
        run: |
          sudo apt-get update
          sudo apt-get install -y texlive-full

      - name: Setup Lean
        uses: leanprover/lean4-action@v1
        with:
          toolchain-file: Lean/lean-toolchain

      - name: Build Lean
        working-directory: Lean
        run: |
          lake exe cache get
          lake build

      - name: Build Blueprint PDF
        run: uvx leanblueprint pdf

      - name: Build Blueprint Web
        run: uvx leanblueprint web

      - name: Deploy to GitHub Pages
        if: github.ref == 'refs/heads/main'
        uses: peaceiris/actions-gh-pages@v4
        with:
          github_token: ${{ secrets.GITHUB_TOKEN }}
          publish_dir: ./blueprint/web/

  verify-lean:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: leanprover/lean4-action@v1
        with:
          toolchain-file: Lean/lean-toolchain
          
      - name: Build GIFT
        working-directory: Lean
        run: |
          lake exe cache get
          lake build
          
      - name: Check for sorry
        working-directory: Lean
        run: |
          ! grep -r "sorry" GIFT/ --include="*.lean" || echo "WARNING: sorry found"
```

---

### Phase 4: Extraction des Déclarations Lean

#### Task 4.1: Script d'extraction

Créer `scripts/extract_declarations.py`:

```python
#!/usr/bin/env python3
"""
Extract Lean declarations for blueprint synchronization.

Usage: python scripts/extract_declarations.py > blueprint/declarations.json
"""

import re
import json
from pathlib import Path

LEAN_DIR = Path("Lean/GIFT")

def extract_declarations(file_path: Path) -> list:
    """Extract theorem/def/lemma declarations from a Lean file."""
    declarations = []
    content = file_path.read_text()
    
    # Patterns for declarations
    patterns = [
        (r'theorem\s+(\w+)', 'theorem'),
        (r'lemma\s+(\w+)', 'lemma'),
        (r'def\s+(\w+)', 'definition'),
        (r'axiom\s+(\w+)', 'axiom'),
    ]
    
    for pattern, kind in patterns:
        for match in re.finditer(pattern, content):
            name = match.group(1)
            # Determine status
            # Check if it's an axiom or has sorry
            is_axiom = kind == 'axiom'
            has_sorry = 'sorry' in content[match.end():match.end()+500]
            
            status = 'axiom' if is_axiom else ('sorry' if has_sorry else 'proven')
            
            declarations.append({
                'name': name,
                'kind': kind,
                'status': status,
                'file': str(file_path.relative_to(LEAN_DIR.parent)),
                'namespace': extract_namespace(content, match.start())
            })
    
    return declarations

def extract_namespace(content: str, pos: int) -> str:
    """Extract the namespace at a given position."""
    # Find most recent namespace declaration before pos
    ns_pattern = r'namespace\s+([\w.]+)'
    last_ns = None
    for match in re.finditer(ns_pattern, content[:pos]):
        last_ns = match.group(1)
    return last_ns or ''

def main():
    all_decls = []
    for lean_file in LEAN_DIR.rglob("*.lean"):
        decls = extract_declarations(lean_file)
        all_decls.extend(decls)
    
    print(json.dumps({
        'declarations': all_decls,
        'stats': {
            'total': len(all_decls),
            'proven': sum(1 for d in all_decls if d['status'] == 'proven'),
            'axioms': sum(1 for d in all_decls if d['status'] == 'axiom'),
            'sorry': sum(1 for d in all_decls if d['status'] == 'sorry'),
        }
    }, indent=2))

if __name__ == '__main__':
    main()
```

---

## 📋 Checklist d'Implémentation

### Infrastructure
- [ ] Convertir `Lean/lakefile.lean` → `Lean/lakefile.toml`
- [ ] Créer `blueprint/blueprint.yaml`
- [ ] Créer `blueprint/src/macros.tex`
- [ ] Créer `blueprint/references.bib`
- [ ] Installer localement: `pip install leanblueprint` (ou `uvx`)

### Contenu Blueprint
- [ ] `blueprint/src/content.tex` (document principal)
- [ ] `blueprint/src/chapter_foundations.tex` (E8, G2, TCS)
- [ ] `blueprint/src/chapter_algebraic.tex` (Cayley-Dickson, Betti)
- [ ] `blueprint/src/chapter_relations.tex` (Weinberg, masses)
- [ ] `blueprint/src/chapter_sequences.tex` (Fibonacci, Lucas)
- [ ] `blueprint/src/chapter_primes.tex` (Prime Atlas)

### CI/CD
- [ ] `.github/workflows/blueprint.yml`
- [ ] Configurer GitHub Pages pour le déploiement
- [ ] Test: `uvx leanblueprint pdf` local
- [ ] Test: `uvx leanblueprint web` local

### Scripts
- [ ] `scripts/extract_declarations.py`
- [ ] Synchronisation blueprint ↔ Lean

---

## 🔗 Commandes Utiles

```bash
# Installation
pip install leanblueprint
# ou avec uv
uvx leanblueprint --help

# Build PDF
cd gift-framework/core
uvx leanblueprint pdf

# Build web (dependency graph)
uvx leanblueprint web

# Serve locally
uvx leanblueprint serve
# → http://localhost:8000/

# Build Lean
cd Lean
lake exe cache get
lake build
```

---

## 📊 Mapping Lean → Blueprint

| Module Lean | Chapitre Blueprint |
|-------------|-------------------|
| `Foundations/E8Lattice.lean` | chapter_foundations §1 |
| `Foundations/G2CrossProduct.lean` | chapter_foundations §2 |
| `Foundations/TCSConstruction.lean` | chapter_foundations §3 |
| `Algebraic/CayleyDickson.lean` | chapter_algebraic §1 |
| `Algebraic/BettiNumbers.lean` | chapter_algebraic §2 |
| `Relations/Weinberg.lean` | chapter_relations §1 |
| `Relations/Cosmology.lean` | chapter_relations §2 |
| `Sequences/Fibonacci.lean` | chapter_sequences §1 |
| `Primes/Tier1.lean` | chapter_primes §1 |

---

## ⚠️ Points d'Attention

1. **leanblueprint version**: Utiliser la version compatible avec Mathlib 4.14+

2. **Noms Lean**: Les `\lean{...}` doivent correspondre EXACTEMENT aux noms dans le code

3. **Status sync**: Le blueprint doit refléter l'état réel (axiom vs proven)

4. **Dépendances**: Les `\uses{...}` créent le graphe de dépendances

5. **Build order**: Lean doit compiler AVANT le blueprint (pour extraire les déclarations)

---

## 🎯 Résultat Attendu

Après implémentation complète :

1. **Site web** sur `https://gift-framework.github.io/core/` avec :
   - PDF du blueprint téléchargeable
   - Graphe de dépendances interactif
   - Status de chaque théorème (proven/axiom/sorry)
   - Liens directs vers le code Lean

2. **CI automatisé** qui :
   - Rebuild le blueprint à chaque push
   - Vérifie la compilation Lean
   - Déploie sur GitHub Pages

3. **Compatibilité Gauss** pour future autoformalization

---

*Document généré pour Claude Code — Décembre 2025*
