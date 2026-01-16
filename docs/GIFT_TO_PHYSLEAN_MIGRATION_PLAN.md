# 🔄 GIFT → PhysLean Migration Plan
## Plan de Conversion Complet et Rigoureux

**Date:** 2026-01-16  
**Version GIFT actuelle:** 3.3.6  
**Cible:** PhysLean-ready repository  
**Auteur:** Brieuc (avec assistance Claude)

---

## 📊 État des Lieux

### Statistiques du Repo GIFT

| Métrique | Valeur | Évaluation |
|----------|--------|------------|
| Fichiers Lean | 104 | ✅ Gérable |
| Lignes totales | 20,912 | ✅ Gérable |
| Doc-strings | 2,213 / 2,606 (85%) | ⚠️ À compléter |
| Lignes > 100 chars | 55 | ✅ Facile à fixer |
| `sorry` | 0 | ✅ Parfait |
| `axiom` | 17 (dans 4 fichiers) | ⚠️ À documenter |

### Fichiers avec Axiomes (à traiter avec soin)

1. `GIFT/Foundations/Analysis/HarmonicForms.lean` (10 axioms)
2. `GIFT/Foundations/Analysis/HodgeTheory.lean` (3 axioms)
3. `GIFT/Foundations/Analysis/G2TensorForm.lean` (2 axioms)
4. `GIFT/Foundations/GoldenRatioPowers.lean` (2 axioms)

---

## 🎯 Objectifs de la Migration

### Changements Requis (Style PhysLean)

1. **Headers de fichiers** - Ajouter copyright Apache 2.0
2. **Doc-strings** - 100% sur toutes les définitions
3. **theorem → lemma** - Pour les résultats non-majeurs
4. **Linting Mathlib** - Lignes ≤100 chars, espacement
5. **Namespace** - `GIFT.*` → `PhysLean.GIFT.*` ou catégorie appropriée
6. **Imports alphabétiques** - Ordre standard

### Structure Cible

```
PhysLean/
├── GIFT/
│   ├── Foundations/
│   │   ├── G2CrossProduct.lean      ← Mathématiques pures
│   │   ├── E8Lattice.lean           ← Mathématiques pures
│   │   ├── RootSystems.lean         ← Mathématiques pures
│   │   └── ...
│   ├── Observables/
│   │   ├── WeakMixingAngle.lean     ← Physique
│   │   ├── PMNS.lean                ← Physique
│   │   └── ...
│   └── Relations/
│       └── ...
```

---

## 📋 Plan de Migration en 5 Phases

### Phase 0: Préparation (1 jour)
**Objectif:** Setup et outils

- [ ] Fork PhysLean sur GitHub
- [ ] Clone local + setup environnement
- [ ] Créer branche `feat/brieuc/gift-infrastructure`
- [ ] Créer script de conversion automatique

### Phase 1: Fichiers Pilotes (2-3 jours)
**Objectif:** Valider le process avec Joseph

**Fichiers sélectionnés (critère: autonomes, mathématiques pures, utiles):**

| # | Fichier | Lignes | Dépendances GIFT | Priorité |
|---|---------|--------|------------------|----------|
| 1 | `Foundations/G2CrossProduct.lean` | 639 | 0 | ⭐⭐⭐ |
| 2 | `Foundations/RootSystems.lean` | 450 | 0 | ⭐⭐⭐ |
| 3 | `Foundations/E8Lattice.lean` | 631 | 0 | ⭐⭐⭐ |
| 4 | `Geometry/Exterior.lean` | 281 | 0 | ⭐⭐ |

**Conversion de chaque fichier:**
1. Copier dans `/PhysLean/GIFT/`
2. Ajouter header copyright
3. Changer namespace
4. Compléter doc-strings manquantes
5. `theorem` → `lemma` (sauf résultats majeurs)
6. Fixer lignes > 100 chars
7. Tester compilation
8. Run linters

**Premier PR:** G2CrossProduct.lean uniquement

### Phase 2: Infrastructure Mathématique (1 semaine)
**Objectif:** Toutes les fondations mathématiques pures

**Groupe A - Algèbre (sans dépendances GIFT):**
| # | Fichier | Lignes | Status |
|---|---------|--------|--------|
| 5 | `Foundations/RationalConstants.lean` | 312 | |
| 6 | `Foundations/GoldenRatio.lean` | 214 | |
| 7 | `Foundations/GraphTheory.lean` | ~100 | |
| 8 | `Algebraic/Octonions.lean` | 254 | |
| 9 | `Algebraic/Quaternions.lean` | ~150 | |
| 10 | `Algebraic/CayleyDickson.lean` | 195 | |

**Groupe B - Géométrie (dépend Groupe A):**
| # | Fichier | Lignes | Status |
|---|---------|--------|--------|
| 11 | `Geometry/DifferentialFormsR7.lean` | 245 | |
| 12 | `Geometry/HodgeStarR7.lean` | ~200 | |
| 13 | `Geometry/HodgeStarCompute.lean` | 337 | |
| 14 | `Foundations/G2Holonomy.lean` | 272 | |

**Groupe C - Analyse (contient axiomes):**
| # | Fichier | Lignes | Axioms | Status |
|---|---------|--------|--------|--------|
| 15 | `Foundations/Analysis/InnerProductSpace.lean` | 222 | 0 | |
| 16 | `Foundations/Analysis/ExteriorAlgebra.lean` | ~150 | 0 | |
| 17 | `Foundations/Analysis/HodgeTheory.lean` | ~200 | 3 | |
| 18 | `Foundations/Analysis/HarmonicForms.lean` | ~200 | 10 | |
| 19 | `Foundations/Analysis/G2TensorForm.lean` | ~150 | 2 | |

### Phase 3: Core GIFT (1 semaine)
**Objectif:** Le cœur du framework

**Groupe D - Core et Relations de base:**
| # | Fichier | Lignes | Dépendances | Status |
|---|---------|--------|-------------|--------|
| 20 | `Core.lean` | 270 | Foundations | |
| 21 | `Relations/Structural.lean` | 236 | Core | |
| 22 | `Relations/ExceptionalGroups.lean` | ~200 | Core | |
| 23 | `Relations/ExceptionalChain.lean` | 221 | Core | |
| 24 | `Relations/BaseDecomposition.lean` | 238 | Core | |
| 25 | `Relations/GoldenRatio.lean` | 191 | Core | |

**Groupe E - Relations Physiques:**
| # | Fichier | Lignes | Status |
|---|---------|--------|--------|
| 26 | `Relations/GaugeSector.lean` | ~150 | |
| 27 | `Relations/LeptonSector.lean` | ~150 | |
| 28 | `Relations/NeutrinoSector.lean` | ~150 | |
| 29 | `Relations/QuarkSector.lean` | ~150 | |
| 30 | `Relations/MassFactorization.lean` | 200 | |
| 31 | `Relations/Cosmology.lean` | ~150 | |

### Phase 4: Observables et Extensions (1 semaine)
**Objectif:** Prédictions physiques

**Groupe F - Observables:**
| # | Fichier | Lignes | Status |
|---|---------|--------|--------|
| 32 | `Observables/WeakMixingAngle.lean` | ~100 | |
| 33 | `Observables/PMNS.lean` | ~150 | |
| 34 | `Observables/CKM.lean` | ~150 | |
| 35 | `Observables/QuarkMasses.lean` | ~150 | |
| 36 | `Observables/BosonMasses.lean` | ~150 | |
| 37 | `Observables/Cosmology.lean` | ~150 | |

**Groupe G - Extensions:**
| # | Fichier | Lignes | Status |
|---|---------|--------|--------|
| 38 | `Sequences/Fibonacci.lean` | ~100 | |
| 39 | `Sequences/Lucas.lean` | ~100 | |
| 40 | `Primes/*.lean` (5 fichiers) | ~600 | |
| 41 | `McKay/*.lean` (2 fichiers) | ~300 | |
| 42 | `Moonshine/*.lean` (2 fichiers) | ~300 | |

### Phase 5: Hiérarchie et Certification (3-4 jours)
**Objectif:** Compléter la migration

**Groupe H - Hiérarchie:**
| # | Fichier | Lignes | Status |
|---|---------|--------|--------|
| 43 | `Hierarchy/DimensionalGap.lean` | 256 | |
| 44 | `Hierarchy/E6Cascade.lean` | 223 | |
| 45 | `Hierarchy/VacuumStructure.lean` | ~150 | |
| 46 | `Hierarchy/AbsoluteMasses.lean` | 209 | |

**Groupe I - Fichiers d'agrégation:**
| # | Fichier | Status |
|---|---------|--------|
| 47 | `Foundations.lean` (imports) | |
| 48 | `Relations.lean` (imports) | |
| 49 | `Algebraic.lean` (imports) | |
| 50 | `Certificate.lean` | |
| 51 | `GIFT.lean` (main) | |

---

## 🔧 Script de Conversion Automatique

```bash
#!/bin/bash
# convert_to_physlean.sh

FILE=$1
AUTHOR="Brieuc Lehmann"

# 1. Ajouter header copyright
HEADER="/-
Copyright (c) 2025 $AUTHOR. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: $AUTHOR
-/"

# 2. Remplacer namespace
sed -i 's/namespace GIFT\./namespace PhysLean.GIFT./g' "$FILE"

# 3. theorem → lemma (sauf mots-clés spécifiques)
# (À faire manuellement pour préserver les théorèmes majeurs)

# 4. Fixer lignes > 100 chars
# (Nécessite intervention manuelle)

echo "Converted: $FILE"
```

---

## 📝 Template de Fichier PhysLean

```lean
/-
Copyright (c) 2025 Brieuc Lehmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brieuc Lehmann
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

/-!
# G₂ Cross Product

This file defines the 7-dimensional cross product arising from the Fano plane
structure constants, which is intimately connected to G₂ holonomy and octonion
multiplication.

## Main definitions

* `R7` - The 7-dimensional Euclidean space (imaginary octonions)
* `cross` - The 7-dimensional cross product
* `phi0` - The associative 3-form

## Main results

* `G2_cross_bilinear` - The cross product is bilinear
* `G2_cross_antisymm` - The cross product is antisymmetric
* `G2_cross_norm` - Lagrange identity: ‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩²

## References

* Harvey & Lawson, "Calibrated Geometries"
* Bryant, "Metrics with exceptional holonomy"
-/

namespace PhysLean.GIFT.G2CrossProduct

/-- The 7-dimensional Euclidean space (imaginary octonions). -/
abbrev R7 := EuclideanSpace ℝ (Fin 7)

/-- Fano plane lines encoding octonion multiplication. -/
def fano_lines : List (Fin 7 × Fin 7 × Fin 7) :=
  [(0,1,3), (1,2,4), (2,3,5), (3,4,6), (4,5,0), (5,6,1), (6,0,2)]

-- ... etc

end PhysLean.GIFT.G2CrossProduct
```

---

## ✅ Checklist de Conversion par Fichier

Pour chaque fichier, vérifier:

- [ ] Header copyright ajouté
- [ ] Module docstring ajouté (avec ## Main definitions, ## Main results)
- [ ] Namespace changé vers `PhysLean.GIFT.*`
- [ ] Toutes définitions ont des doc-strings `/-- ... -/`
- [ ] `theorem` → `lemma` pour résultats non-majeurs
- [ ] Lignes ≤ 100 caractères
- [ ] Imports ordonnés alphabétiquement
- [ ] Pas de `sorry`
- [ ] Axiomes documentés explicitement
- [ ] Compilation réussie (`lake build`)
- [ ] Linting passé (`lake exe lint_all`)

---

## 🚀 Timeline Estimée

| Phase | Durée | Livrable |
|-------|-------|----------|
| Phase 0 | 1 jour | Setup complet |
| Phase 1 | 2-3 jours | Premier PR (G2CrossProduct) |
| Phase 2 | 1 semaine | Infrastructure math |
| Phase 3 | 1 semaine | Core GIFT |
| Phase 4 | 1 semaine | Observables |
| Phase 5 | 3-4 jours | Certification |
| **Total** | **~4-5 semaines** | **Migration complète** |

---

## 📞 Points de Contact avec Joseph

### PR 1 (Phase 1): G2CrossProduct
- Objectif: Valider le style et l'approche
- Questions à poser:
  - Namespace préféré? `PhysLean.GIFT.*` ou `PhysLean.G2.*`?
  - Les axiomes dans l'analyse sont-ils acceptables?
  - Feedback sur le code style?

### PR 2+ (Phase 2+): Itérations
- Incorporer feedback
- PRs petits et réguliers (1-3 fichiers)

---

## 🔴 Risques et Mitigations

| Risque | Impact | Mitigation |
|--------|--------|------------|
| Rejet de style | Moyen | Premier PR petit, feedback early |
| Conflits de namespace | Faible | Préfixer tout avec `GIFT` |
| Axiomes non acceptés | Moyen | Les convertir en `informal_lemma` |
| Dépendances circulaires | Faible | Vérifier graphe avant migration |
| Temps de review long | Moyen | PRs petits, communication régulière |

---

## 📎 Annexes

### A. Graphe de Dépendances (simplifié)

```
GIFT.lean
├── Core.lean ← Foundations.lean
├── Relations.lean ← Core.lean
├── Certificate.lean ← Relations.lean
├── Algebraic.lean ← Core.lean
├── Sequences.lean ← Relations.lean
├── Primes.lean ← Core.lean
├── Moonshine.lean ← Core.lean
├── McKay.lean ← Core.lean
├── Hierarchy.lean ← Relations.lean
├── Observables.lean ← Core.lean
└── Geometry.lean ← Foundations.lean
```

### B. Fichiers 100% Autonomes (aucune dépendance GIFT)

Ces fichiers peuvent être migrés indépendamment:
1. `Foundations/G2CrossProduct.lean`
2. `Foundations/RootSystems.lean`
3. `Foundations/E8Lattice.lean`
4. `Foundations/RationalConstants.lean`
5. `Foundations/GoldenRatio.lean`
6. `Geometry/Exterior.lean`
7. `Algebraic/Octonions.lean`
8. `Algebraic/Quaternions.lean`
9. `Foundations/Analysis/InnerProductSpace.lean`

### C. Commandes Utiles

```bash
# Vérifier compilation
lake build

# Linting
lake exe lint_all
./scripts/lint-style.sh

# Chercher les définitions sans doc-string
grep -B1 "^def \|^theorem \|^lemma " *.lean | grep -v "/--"

# Compter lignes trop longues
awk 'length > 100' *.lean | wc -l
```

---

**Prochaine étape:** Commencer Phase 0 (fork + setup), puis Phase 1 avec G2CrossProduct.lean

**Tu veux que je commence la conversion de G2CrossProduct.lean maintenant?**
