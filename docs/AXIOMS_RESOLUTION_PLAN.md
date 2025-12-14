# Plan de Résolution des Axiomes GIFT

## Vue d'Ensemble

Ce document détaille la stratégie pour convertir les 58 axiomes actuels en théorèmes prouvés dans Lean 4 avec Mathlib. Les axiomes sont classés par difficulté et domaine mathématique.

---

## Classification des Axiomes

### Tier 1 : Énumération Finie (12 axiomes) — FAISABLE
Axiomes réductibles à du calcul explicite sur des ensembles finis.

### Tier 2 : Algèbre Linéaire (8 axiomes) — ACCESSIBLE
Axiomes découlant de propriétés standard des espaces vectoriels.

### Tier 3 : Algèbre Extérieure (7 axiomes) — MODÉRÉ
Axiomes sur le produit wedge et l'anticommutativité graduée.

### Tier 4 : Structures G2 (9 axiomes) — DIFFICILE
Axiomes sur le groupe G2, produit croisé, octonions.

### Tier 5 : Analyse Fonctionnelle (12 axiomes) — TRÈS DIFFICILE
Espaces de Sobolev, opérateurs de Hodge, théorie spectrale.

### Tier 6 : Théorèmes d'Existence (10 axiomes) — RECHERCHE OUVERTE
Théorème de Joyce, décomposition de Hodge, structures torsion-free.

---

## Tier 1 : Énumération Finie

### A1. `D8_roots_card : D8_roots.ncard = 112`

**Énoncé** : L'ensemble des racines D8 contient exactement 112 éléments.

**Stratégie** :
1. Définir explicitement D8_roots comme ensemble fini dans `Fin 112 → R8`
2. Construire une bijection entre l'index et les paires `(i,j,σ)` où :
   - `i,j ∈ Fin 8` avec `i < j` (28 choix = C(8,2))
   - `σ ∈ Fin 4` pour les 4 signes `(±1, ±1)`
3. Prouver `28 × 4 = 112` par `native_decide`

**Dépendances** : Aucune

**Code esquisse** :
```lean
def D8_roots_explicit : Fin 112 → R8 :=
  fun k =>
    let (pair_idx, sign_idx) := k.val.divMod 4
    let (i, j) := pair_from_index pair_idx  -- bijection avec paires
    let (si, sj) := sign_from_index sign_idx
    stdBasis i * si + stdBasis j * sj

theorem D8_roots_card : D8_roots.ncard = 112 := by
  rw [show D8_roots = Set.range D8_roots_explicit from ...]
  exact Fintype.card_fin 112
```

---

### A2. `HalfInt_roots_card : HalfInt_roots.ncard = 128`

**Énoncé** : L'ensemble des racines demi-entières contient 128 éléments.

**Stratégie** :
1. Paramétrer par `σ : Fin 8 → Bool` (256 choix de signes)
2. Filtrer pour `∑ σᵢ ≡ 0 [2]` (somme paire)
3. Exactement la moitié satisfait la contrainte : `256 / 2 = 128`

**Dépendances** : Aucune

**Code esquisse** :
```lean
def HalfInt_explicit (σ : Fin 8 → Bool) : R8 :=
  fun i => if σ i then 1/2 else -1/2

def even_sign_sum (σ : Fin 8 → Bool) : Prop :=
  (Finset.univ.filter σ).card % 2 = 0

theorem HalfInt_roots_card : HalfInt_roots.ncard = 128 := by
  -- Bijection avec { σ | even_sign_sum σ }
  -- Card = 2^8 / 2 = 128
  native_decide
```

---

### A3. `E8_roots_decomposition : E8_roots = D8_roots ∪ HalfInt_roots`

**Énoncé** : Les racines E8 sont l'union disjointe de D8 et HalfInt.

**Stratégie** :
1. Montrer `D8_roots ⊆ E8_roots` (toutes entières, norme² = 2)
2. Montrer `HalfInt_roots ⊆ E8_roots` (toutes ±1/2, somme paire, norme² = 2)
3. Montrer exhaustivité : tout vecteur de norme² = 2 dans le réseau est de l'un des deux types

**Dépendances** : A1, A2

---

### A4. `D8_HalfInt_disjoint : D8_roots ∩ HalfInt_roots = ∅`

**Énoncé** : Les racines D8 et HalfInt sont disjointes.

**Stratégie** :
Preuve directe : D8 a coordonnées entières, HalfInt a coordonnées demi-entières.
Un vecteur ne peut pas être les deux simultanément.

```lean
theorem D8_HalfInt_disjoint : D8_roots ∩ HalfInt_roots = ∅ := by
  ext v
  simp [D8_roots, HalfInt_roots, AllInteger, AllHalfInteger]
  intro h_int h_half
  obtain ⟨i, hi⟩ := h_half 0  -- coordonnée 0 est demi-entière
  obtain ⟨n, hn⟩ := h_int 0   -- coordonnée 0 est entière
  -- Contradiction : n = n + 1/2 impossible
  linarith
```

**Dépendances** : Aucune

---

### A5. `E8_roots_card : E8_roots.ncard = 240`

**Énoncé** : |E8 roots| = 240

**Stratégie** :
Conséquence directe de A1-A4 :
```
|E8| = |D8 ∪ HalfInt| = |D8| + |HalfInt| - |D8 ∩ HalfInt|
     = 112 + 128 - 0 = 240
```

**Dépendances** : A1, A2, A3, A4

---

### A6-A8. Propriétés du réseau E8

**A6. `E8_inner_integral`** : ⟨v,w⟩ ∈ ℤ pour v,w ∈ E8

**Stratégie** : Calcul direct sur les deux types de vecteurs :
- Entier · Entier → Entier
- Demi-entier · Demi-entier → somme de 8 termes ±1/4, nombre pair → Entier
- Entier · Demi-entier → somme de termes ±1/2 en nombre pair → Entier

**A7. `E8_even`** : ‖v‖² ∈ 2ℤ pour v ∈ E8

**Stratégie** : Similaire, par cas sur le type de vecteur.

**A8. `E8_basis_generates`** : Tout vecteur est combinaison ℤ-linéaire de la base

**Stratégie** : Définir la base simple de E8, montrer qu'elle engendre.

---

### A9-A12. Propriétés des bases

**A9. `stdBasis_orthonormal`** : ⟨eᵢ, eⱼ⟩ = δᵢⱼ

**Stratégie** : Utiliser `EuclideanSpace.single` de Mathlib et `PiLp.inner_apply`.

```lean
theorem stdBasis_orthonormal (i j : Fin n) :
    innerRn (stdBasis i) (stdBasis j) = if i = j then 1 else 0 := by
  simp [innerRn, stdBasis, EuclideanSpace.single, inner, PiLp.inner_apply]
  split_ifs <;> simp
```

**A10. `stdBasis_norm`** : ‖eᵢ‖ = 1

**Stratégie** : Conséquence de A9 avec i = j.

**A11. `normSq_eq_sum`** : ‖v‖² = ∑ᵢ vᵢ²

**Stratégie** : Définition de la norme dans `PiLp`.

**A12. `inner_eq_sum`** : ⟨v,w⟩ = ∑ᵢ vᵢwᵢ

**Stratégie** : Définition du produit scalaire dans `PiLp`.

---

## Tier 2 : Algèbre Linéaire

### B1. `reflect_preserves_lattice`

**Énoncé** : La réflexion par une racine préserve le réseau E8.

**Stratégie** :
1. Réflexion : `s_α(v) = v - 2⟨v,α⟩/⟨α,α⟩ · α = v - ⟨v,α⟩ · α` (car ⟨α,α⟩ = 2)
2. Montrer que ⟨v,α⟩ ∈ ℤ (par A6)
3. Donc s_α(v) = v - n·α avec n ∈ ℤ, reste dans le réseau

**Dépendances** : A6

---

### B2-B5. Propriétés du produit croisé G2

**B2. `G2_cross_bilinear`** : Bilinéarité

**Stratégie** : Définir via les coefficients de structure de φ₀, la bilinéarité découle.

**B3. `G2_cross_antisymm`** : u × v = -v × u

**Stratégie** : Antisymétrie de φ₀ (3-forme).

**B4. `G2_cross_norm`** : |u × v|² = |u|²|v|² - ⟨u,v⟩²

**Stratégie** : Identité de Lagrange généralisée. Preuve par calcul sur φ₀.

**B5. `cross_is_octonion`** : Lien avec multiplication octonionique

**Stratégie** : Définir la multiplication des octonions purs, vérifier l'égalité.

---

## Tier 3 : Algèbre Extérieure

### C1. `wedge_anticomm_graded`

**Énoncé** : ω ∧ η = (-1)^{kl} η ∧ ω pour ω ∈ Λᵏ, η ∈ Λˡ

**Stratégie** :
1. Utiliser `ExteriorAlgebra.ι_mul_ι_swap` de Mathlib
2. Généraliser par récurrence sur les degrés
3. La signature vient des permutations de Koszul

**Dépendances** : Mathlib `ExteriorAlgebra`

---

### C2. `wedge_anticomm_1forms`

**Énoncé** : v ∧ w = -w ∧ v pour des 1-formes

**Stratégie** : Cas particulier de C1 avec k = l = 1, donc (-1)^{1·1} = -1.

Alternativement, preuve directe :
```lean
-- De ι(v)² = 0 pour tout v, on développe (ι(v+w))² = 0
-- → ι(v)ι(w) + ι(w)ι(v) = 0
-- → ι(v)ι(w) = -ι(w)ι(v)
```

**Dépendances** : Mathlib `ExteriorAlgebra.ι_sq_zero`

---

### C3-C5. Intégration

**C3. `integral_7`** : Intégration sur 7-variétés

**Stratégie** : Axiome fondamental de géométrie différentielle. Peut rester axiome ou utiliser théorie de la mesure.

**C4. `integral_linear`** : Linéarité de l'intégrale

**Stratégie** : Propriété standard. Peut être déduite si C3 est construit via mesure.

**C5. `stokes`** : ∫_M dω = 0 pour M fermée

**Stratégie** : Théorème de Stokes. Profond, peut rester axiome.

---

## Tier 4 : Structures G2

### D1. `gl7_action`

**Énoncé** : Action de GL(7) sur les 3-formes

**Stratégie** :
1. Définir le pullback : `(g · ω)(v₁,v₂,v₃) = ω(g⁻¹v₁, g⁻¹v₂, g⁻¹v₃)`
2. Ou en composantes : `(g · ω)_{ijk} = g^a_i g^b_j g^c_k ω_{abc}`

**Dépendances** : Structure de 3-forme

---

### D2. `g2_lie_algebra`

**Énoncé** : Type de l'algèbre de Lie G2

**Stratégie** :
1. Définir comme sous-algèbre de gl(7) : `{ X | X · φ₀ = 0 }`
2. Calculer que c'est 14-dimensionnel
3. Ou utiliser la construction via racines

---

### D3. `G2_dimension_14`

**Énoncé** : dim(G2) = 14

**Stratégie** :
1. **Via stabilisateur** : dim(GL(7)) - dim(orbite de φ₀) = 49 - 35 = 14
2. **Via racines** : 12 racines + rang 2 = 14 (déjà prouvé arithmétiquement)
3. **Via construction explicite** : Exhiber 14 générateurs linéairement indépendants

---

### D4-D6. Structures sur variétés

**D4. `G2Structures`** : Espace des structures G2

**Stratégie** : Définir comme sections du fibré Λ³(T*M) satisfaisant positivité.

**D5. `G2_open`** : Structures G2 forment un ouvert

**Stratégie** : Condition de positivité est ouverte (inégalités strictes).

**D6. `Torsion`** : Fonction torsion

**Stratégie** : Définir via dφ et d*φ.

---

## Tier 5 : Analyse Fonctionnelle

### E1-E4. Espaces de Sobolev

**E1. `Sobolev`** : Type H^k(M)

**Stratégie** :
- Utiliser `MeasureTheory.Lp` de Mathlib comme point de départ
- Définir les dérivées faibles
- Complétion de C^∞ sous norme de Sobolev

**E2. `Sobolev_banach`** : H^k est Banach

**Stratégie** : Théorème standard d'analyse fonctionnelle.

**E3. `sobolev_norm`** : Norme de Sobolev

**Stratégie** : ‖u‖_{H^k} = (∑_{|α|≤k} ‖D^α u‖_{L²}²)^{1/2}

**E4. `sobolev_embedding`** : H^k ↪ C^{k-n/2}

**Stratégie** : Théorème de plongement de Sobolev. Preuve technique.

---

### E5-E8. Opérateurs de Hodge

**E5. `K7_hodge_data`** : Structure de Hodge sur K7

**Stratégie** : Construction via métrique induite par G2.

**E6. `K7_laplacian`** : Laplacien de Hodge sur K7

**Stratégie** : Δ = dd* + d*d, bien défini une fois d et d* construits.

**E7. `hodge_theorem_K7`** : dim(ker Δₖ) = bₖ

**Stratégie** : Théorème de Hodge. Preuve via théorie spectrale des opérateurs elliptiques.

**E8. `hodge_decomposition_exists`** : Décomposition de Hodge

**Stratégie** : Ωᵏ = ℋᵏ ⊕ dΩᵏ⁻¹ ⊕ d*Ωᵏ⁺¹

---

### E9-E12. Bases harmoniques

**E9. `omega2_basis`** : Base de ℋ²(K7)

**Stratégie** : Existence garantie par théorie de Hodge + dim = 21.

**E10. `omega3_basis`** : Base de ℋ³(K7)

**Stratégie** : Similaire, dim = 77.

**E11. `omega2_basis_harmonic`** : Éléments de base sont harmoniques

**Stratégie** : Par construction de E9.

**E12. `omega3_basis_harmonic`** : Éléments de base sont harmoniques

**Stratégie** : Par construction de E10.

---

## Tier 6 : Théorèmes d'Existence

### F1-F4. Théorie de Joyce

**F1. `JoyceOp`** : Opérateur de Joyce

**Stratégie** : Construction technique via équations EDP non-linéaires.

**F2. `JoyceOp_smooth`** : Régularité C^∞

**Stratégie** : Théorie de régularité elliptique.

**F3. `JoyceLinearization`** : Linéarisation

**Stratégie** : Différentielle de Fréchet de l'opérateur.

**F4. `linearization_fredholm`** : Opérateur Fredholm d'indice 0

**Stratégie** : Analyse fonctionnelle sur espaces de Sobolev.

---

### F5-F8. Existence

**F5. `epsilon_joyce`** : Seuil de petite torsion

**Stratégie** : Constante dépendant de la géométrie.

**F6. `epsilon_pos`** : ε > 0

**Stratégie** : Conséquence de la construction.

**F7. `joyce_existence`** : THÉORÈME PRINCIPAL

**Énoncé** : Si torsion < ε, alors ∃ structure torsion-free.

**Stratégie** :
1. Théorème de fonction implicite en dimension infinie
2. Contrôle des bornes a priori
3. Bootstrap de régularité

**Difficulté** : C'est un théorème de niveau recherche (thèse de Joyce, 1996).

**F8. `K7_torsion_bound`** : Torsion de K7 < ε

**Stratégie** : Estimation numérique vérifiée par PINN (déjà fait).

---

### F9-F10. Moduli et cohomologie

**F9. `moduli_smooth`** : Espace des modules lisse

**Stratégie** : Conséquence du théorème de fonction implicite.

**F10. `hodge_isomorphism`** : ℋᵏ ≅ Hᵏ_dR

**Stratégie** : Isomorphisme de Hodge-de Rham.

---

## Graphe de Dépendances

```
                    ┌─────────────────────────────────────────┐
                    │           Tier 6: Existence             │
                    │  joyce_existence, hodge_isomorphism     │
                    └────────────────────┬────────────────────┘
                                         │
                    ┌────────────────────▼────────────────────┐
                    │       Tier 5: Analyse Fonctionnelle     │
                    │    Sobolev, Hodge, bases harmoniques    │
                    └────────────────────┬────────────────────┘
                                         │
                    ┌────────────────────▼────────────────────┐
                    │          Tier 4: Structures G2          │
                    │   gl7_action, G2_dimension, torsion     │
                    └────────────────────┬────────────────────┘
                                         │
          ┌──────────────────────────────┼──────────────────────────────┐
          │                              │                              │
┌─────────▼─────────┐        ┌───────────▼───────────┐       ┌─────────▼─────────┐
│ Tier 3: Extérieur │        │  Tier 2: Alg. Lin.    │       │ Tier 1: Fini      │
│ wedge_anticomm    │        │  reflect_preserves    │       │ E8_roots_card     │
└─────────┬─────────┘        └───────────┬───────────┘       └─────────┬─────────┘
          │                              │                              │
          └──────────────────────────────┼──────────────────────────────┘
                                         │
                              ┌──────────▼──────────┐
                              │   Mathlib Core      │
                              │ EuclideanSpace, Lp  │
                              │ ExteriorAlgebra     │
                              └─────────────────────┘
```

---

## Plan d'Implémentation Recommandé

### Phase 1 : Fondations (1-2 semaines)

**Objectif** : Prouver tous les axiomes Tier 1

1. `stdBasis_orthonormal`, `stdBasis_norm`
2. `normSq_eq_sum`, `inner_eq_sum`
3. `D8_roots_card`, `HalfInt_roots_card`
4. `D8_HalfInt_disjoint`, `E8_roots_decomposition`
5. `E8_roots_card`
6. `E8_inner_integral`, `E8_even`

**Livrables** : Module `E8LatticeProved.lean`

---

### Phase 2 : Algèbre (2-3 semaines)

**Objectif** : Prouver Tier 2 et Tier 3

1. `reflect_preserves_lattice`
2. `E8_basis_generates`
3. `wedge_anticomm_1forms`, `wedge_anticomm_graded`
4. `G2_cross_bilinear`, `G2_cross_antisymm`, `G2_cross_norm`

**Livrables** : Modules `WeylGroupProved.lean`, `WedgeProved.lean`

---

### Phase 3 : Géométrie G2 (3-4 semaines)

**Objectif** : Prouver Tier 4

1. `gl7_action` (définition explicite)
2. `G2_dimension_14` (via calcul de stabilisateur)
3. `g2_lie_algebra` (construction)
4. `cross_is_octonion` (via table de multiplication)

**Livrables** : Module `G2GeometryProved.lean`

---

### Phase 4 : Analyse (temps indéterminé)

**Objectif** : Avancer sur Tier 5

1. Explorer `MeasureTheory.Lp` pour Sobolev
2. Formaliser opérateur de Hodge abstrait
3. Construire bases harmoniques (si possible)

**Note** : Cette phase peut nécessiter des contributions à Mathlib.

---

### Phase 5 : Recherche (long terme)

**Objectif** : Tier 6

Ces axiomes encodent des théorèmes profonds qui sont à la frontière de ce qui est formalisable aujourd'hui. Stratégies possibles :

1. **Accepter comme axiomes** : Documenter les références (Joyce 1996, etc.)
2. **Collaboration** : Travailler avec la communauté Mathlib
3. **Recherche** : Contribuer à la formalisation de géométrie différentielle

---

## Résumé Quantitatif

| Tier | Axiomes | Difficulté | Temps estimé |
|------|---------|------------|--------------|
| 1    | 12      | Faisable   | 1-2 semaines |
| 2    | 8       | Accessible | 2-3 semaines |
| 3    | 7       | Modéré     | 2-3 semaines |
| 4    | 9       | Difficile  | 3-4 semaines |
| 5    | 12      | Très diff. | Indéterminé  |
| 6    | 10      | Recherche  | Long terme   |

**Total** : 58 axiomes
- **Résolvables à court terme** : ~27 (Tiers 1-3)
- **Résolvables à moyen terme** : ~9 (Tier 4)
- **Nécessitent travail de fond** : ~22 (Tiers 5-6)

---

## Références

1. **E8 Lattice** : Conway & Sloane, "Sphere Packings, Lattices and Groups"
2. **G2 Holonomy** : Joyce, "Compact Manifolds with Special Holonomy" (2000)
3. **Hodge Theory** : Warner, "Foundations of Differentiable Manifolds and Lie Groups"
4. **Mathlib** : https://leanprover-community.github.io/mathlib4_docs/
5. **ExteriorAlgebra** : `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`
6. **EuclideanSpace** : `Mathlib.Analysis.InnerProductSpace.PiL2`
