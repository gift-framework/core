# GIFT v3.0 - ML Exploration

This directory contains the ML exploration modules for GIFT (Geometric Information Field Theory) v3.0, implementing a comprehensive framework for exploring torsional physics through machine learning.

## Overview

The exploration follows a 4-phase plan:

1. **Phase 1: Consolidation** - Synthesize and formalize static patterns
2. **Phase 2: Lean Formalization** - Axiomatize conjectures in Lean 4
3. **Phase 3: PINN Exploration** - Dynamic ML simulation of torsional flows
4. **Phase 4: Global Simulations** - Generate testable predictions

## Files

| File | Description |
|------|-------------|
| `GIFT_Core_v3.py` | Core patterns: 3477=3×19×61, T₆₁ manifold, triade 9-18-34 |
| `GIFT_v3_Conjectures.lean` | Lean 4 formalization of theorems and conjectures |
| `Torsion_PINN.py` | Physics-Informed Neural Network for torsion flows |
| `Global_Sims.py` | Running masses, Hubble constant, predictions |
| `GIFT_v3_Final_Report.md` | Complete report with all predictions |

## Key Discoveries

### The 3477 Factorization
```
m_τ/m_e = 3477 = 3 × 19 × 61
         = N_gen × prime(rank_E8) × κ_T⁻¹
```

### T₆₁ Manifold Structure
- Dimension: 61 = κ_T⁻¹
- Effective moduli: W₁+W₇+W₁₄+W₂₇ = 1+7+14+27 = 49
- Residue: 61-49 = 12 = dim(G₂) - p₂

### Triade 9-18-34 (Fibonacci/Lucas)
- 9 = H*/D_bulk = 99/11 (impedance)
- 18 = L₆ (duality gap)
- 34 = F₉ (hidden dimension)

## Generated Predictions

| # | Prediction | Value | Confidence |
|---|------------|-------|------------|
| 1 | Sterile neutrino | ~9.7 MeV | Speculative |
| 2 | Hidden scalar | 18 GeV | Speculative |
| 3 | Spectral index | 0.9649 | Moderate |
| 4 | Dark energy Ω_DE | 0.686 | Moderate |
| 5 | Hubble H₀ | 70 km/s/Mpc | High |
| 6 | α⁻¹ | 137.033 | High |
| 7 | α_s(M_Z) | 0.1179 | High |
| 8 | θ₁₃ | 8.57° | High |
| 9 | δ_CP | 197° | High |
| 10 | Hidden states | 44 | Speculative |

## Usage

```bash
# Run Phase 1 consolidation
python GIFT_Core_v3.py

# Run Phase 3 PINN and Monte Carlo (requires PyTorch optional)
python Torsion_PINN.py

# Run Phase 4 global simulations (generates plots and report)
python Global_Sims.py
```

## Dependencies

- NumPy (required)
- SymPy (required for Phase 1)
- SciPy (optional, for ODE integration)
- Matplotlib (optional, for plots)
- PyTorch (optional, for GPU-accelerated PINN)

## Plots

Three visualization files are generated:
- `running_masses.png` - Lepton mass evolution
- `hubble_resolution.png` - Hubble tension analysis
- `predictions_summary.png` - Confidence levels for all predictions

## References

This work builds on the GIFT framework documented in:
- `gift_core/constants.py` - Proven topological relations
- `gift_core/relations.py` - 13 certified Lean/Coq theorems
- Lean proofs in `gift-framework/core/Lean/`
