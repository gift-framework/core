# 🎯 GIFT Spectral Gap — Plan pour Claude Code

## Contexte

**Problème découvert** : Les méthodes graph Laplacian (k-NN, diffusion maps) ne fonctionnent PAS.
- Test calibration : λ₁(S⁷)/λ₁(S¹) = 468 au lieu de 7 → **ARTEFACT**
- Cause : Ces méthodes ignorent la métrique Riemannienne

**Solution identifiée** : Utiliser le PINN qui connaît g(x) pour calculer le vrai Laplacien.

---

## 📋 Plan en 5 Phases

### Phase 1 : Calibration PINN Spectral (Priorité 1)

**Objectif** : Valider la méthode sur des variétés où λ₁ est connu

**Tâches** :
```
1.1 Implémenter PINN spectral sur S¹ (cercle)
    - λ₁ analytique = 1
    - Laplacien = -d²/dθ²
    - Test : retrouver λ₁ = 1.0 ± 10%

1.2 Étendre à S² (sphère 2D)  
    - λ₁ analytique = 2
    - Laplacien en coordonnées sphériques
    
1.3 Étendre à S⁷
    - λ₁ analytique = 7
    - Si ça marche → méthode validée
```

**Packages nécessaires** :
```bash
pip install torch numpy scipy matplotlib
```

**Critère de succès** : Ratios λ₁(S⁷)/λ₁(S¹) ≈ 7 (±20%)

---

### Phase 2 : PINN Spectral sur K₇

**Objectif** : Calculer λ₁(K₇) avec la métrique GIFT

**Tâches** :
```
2.1 Charger/entraîner le PINN métrique GIFT
    - g_{ij}(x) sur K₇
    - det(g) ≈ 65/32
    - Torsion < Joyce threshold

2.2 Implémenter le Laplacien de Hodge
    Δψ = (1/√g) ∂ᵢ(√g gⁱʲ ∂ⱼψ)
    
2.3 Réseau pour fonction propre ψ(x)
    - Contrainte : ∫ψ√g dx = 0 (orthogonal aux constantes)
    - Contrainte : ∫ψ²√g dx = 1 (normalisé)

2.4 Optimiser (λ, ψ) conjointement
    Loss = ||Δψ - λψ||² + α||∫ψ||² + β(||∫ψ²|| - 1)²
```

**Fichiers du repo GIFT à utiliser** :
- `gift_core/nn/g2_pinn.py` — Architecture PINN existante
- `data/analytical_g2_metric.json` — Coefficients métriques
- `gift_core/analysis/joyce_certificate.py` — Validation

---

### Phase 3 : Méthode Variationnelle (Rayleigh-Ritz)

**Objectif** : Obtenir des BORNES rigoureuses sur λ₁

**Principe** :
```
λ₁ = min_{ψ⊥1} R[ψ]  où  R[ψ] = ∫|∇ψ|²√g / ∫ψ²√g
```

**Tâches** :
```
3.1 Construire base de fonctions test
    - Harmoniques sur S³×S³ (structure TCS)
    - Modes du "neck" TCS
    
3.2 Évaluer quotient de Rayleigh pour chaque fonction
    
3.3 Le minimum donne borne supérieure sur λ₁
```

**Avantage** : Donne λ₁ ≤ X (rigoureux, pas d'approximation)

---

### Phase 4 : Bornes Analytiques (Lean/Mathlib)

**Objectif** : Prouver des inégalités en Lean

**Théorèmes à formaliser** :

```lean
-- Cheeger : λ₁ ≥ h²/4
theorem cheeger_bound (M : CompactRiemannian) :
  spectral_gap M ≥ (cheeger_constant M)^2 / 4

-- Lichnerowicz : Si Ric ≥ (n-1)K alors λ₁ ≥ nK  
theorem lichnerowicz (M : CompactRiemannian) (K : ℝ) 
  (h : ricci_lower_bound M K) :
  spectral_gap M ≥ dim M * K

-- Cheng : λ₁ ≤ C(n)/diam²
theorem cheng_upper (M : CompactRiemannian) :
  spectral_gap M ≤ C * dim M / diameter M ^ 2
```

**Si on prouve** : 0.10 ≤ λ₁ ≤ 0.20, alors 14/99 ≈ 0.1414 est DEDANS.

---

### Phase 5 : Synthèse et Publication

**Objectif** : Croiser les résultats, établir confiance

**Tableau cible** :

| Méthode | λ₁ | Incertitude | Type |
|---------|-----|-------------|------|
| PINN Spectral | ? | ±5% | Numérique |
| Rayleigh-Ritz | ≤ ? | Rigoureux | Borne sup |
| Cheeger | ≥ ? | Rigoureux | Borne inf |
| GIFT prédit | 0.1414 | Exact | Algébrique |

**Critère final** : Si toutes les méthodes convergent vers ~0.14, c'est validé.

---

## 📁 Structure Fichiers Proposée

```
gift-spectral/
├── README.md
├── requirements.txt
│
├── calibration/
│   ├── pinn_circle.py      # S¹, λ₁=1
│   ├── pinn_sphere.py      # S², λ₁=2
│   ├── pinn_s7.py          # S⁷, λ₁=7
│   └── validate.py         # Check ratios
│
├── k7/
│   ├── load_metric.py      # Charger PINN GIFT
│   ├── laplacian.py        # Δ sur K₇
│   ├── spectral_solve.py   # Trouver λ₁
│   └── eigenfunction.py    # Visualiser ψ₁
│
├── variational/
│   ├── test_functions.py   # Base de fonctions
│   ├── rayleigh.py         # Quotient R[ψ]
│   └── bounds.py           # Borne supérieure
│
├── lean/
│   ├── Cheeger.lean
│   ├── Lichnerowicz.lean
│   └── SpectralBounds.lean
│
└── results/
    ├── calibration.json
    ├── k7_spectral.json
    └── synthesis.md
```

---

## 🚀 Commandes Claude Code

### Démarrage
```
Crée le repo gift-spectral avec la structure ci-dessus.
Installe torch, numpy, scipy, matplotlib.
```

### Phase 1
```
Implémente pinn_circle.py : PINN pour trouver λ₁ sur S¹.
Le Laplacien est -d²/dθ². On cherche λ tel que -ψ'' = λψ avec ψ(0)=ψ(2π).
Vérifie que λ₁ ≈ 1.0.
```

### Phase 2
```
Charge le PINN métrique depuis gift_core.
Implémente le Laplacien Δψ = (1/√g) ∂ᵢ(√g gⁱʲ ∂ⱼψ) via autodiff.
Entraîne pour trouver λ₁(K₇).
Compare à 14/99.
```

### Phase 3
```
Construis des fonctions test sur K₇ (harmoniques S³, modes TCS).
Calcule le quotient de Rayleigh pour chacune.
Le minimum est une borne sup sur λ₁.
```

---

## ⚠️ Points Critiques

1. **Calibration OBLIGATOIRE** — Ne pas passer à K₇ avant que S⁷ marche
2. **Métrique GIFT** — Utiliser le vrai PINN, pas une approximation
3. **Convergence** — Vérifier que λ ne dépend pas de l'initialisation
4. **Bornes** — Au moins une borne rigoureuse (Rayleigh ou Cheeger)

---

## 📊 Résultat Attendu

**Si λ₁(K₇) ≈ 0.14 ± 0.02** par méthodes indépendantes :
- GIFT prédit 14/99 = 0.1414...
- La conjecture spectrale est **CONFIRMÉE**
- Publiable avec confiance

**Si λ₁(K₇) ≠ 0.14** :
- Soit la méthode est encore fausse
- Soit GIFT doit être révisé
- Dans les deux cas, c'est de l'information utile

---

*Plan v1.0 — Janvier 2026*
*Pour exécution via Claude Code*
