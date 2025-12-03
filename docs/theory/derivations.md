# Derivations

This page shows how each of the 13 exact relations is derived from topological invariants.

## Input Constants

All derivations use only these fixed topological integers:

| Symbol | Value | Origin |
|--------|-------|--------|
| dim(E₈) | 248 | E₈ Lie algebra dimension |
| rank(E₈) | 8 | Cartan subalgebra dimension |
| dim(E₈×E₈) | 496 | Product group: 2 × 248 |
| Weyl | 5 | From |W(E₈)| = 2¹⁴ × 3⁵ × 5² × 7 |
| b₂ | 21 | Second Betti number of K₇ |
| b₃ | 77 | Third Betti number of K₇ |
| dim(G₂) | 14 | G₂ Lie group dimension |
| dim(K₇) | 7 | Manifold dimension |
| dim(J₃(𝕆)) | 27 | Exceptional Jordan algebra |

---

## 1. Weinberg Angle

$$\sin^2\theta_W = \frac{b_2}{b_3 + \dim(G_2)}$$

### Calculation

$$\sin^2\theta_W = \frac{21}{77 + 14} = \frac{21}{91}$$

### Simplification

$$\frac{21}{91} = \frac{3 \times 7}{7 \times 13} = \frac{3}{13}$$

### Result

$$\sin^2\theta_W = \frac{3}{13} \approx 0.2308$$

**Experimental value**: 0.23122 ± 0.00003  
**Deviation**: 0.19%

---

## 2. Hierarchy Parameter τ

$$\tau = \frac{\dim(E_8 \times E_8) \cdot b_2}{\dim(J_3(\mathbb{O})) \cdot H^*}$$

where H* = b₂ + b₃ + 1 = 99.

### Calculation

$$\tau = \frac{496 \times 21}{27 \times 99} = \frac{10416}{2673}$$

### Simplification

$$\gcd(10416, 2673) = 3$$

$$\tau = \frac{10416/3}{2673/3} = \frac{3472}{891}$$

### Result

$$\tau = \frac{3472}{891} \approx 3.897$$

---

## 3. Metric Determinant

$$\det(g) = \frac{\text{Weyl} \times 13}{32}$$

### Calculation

$$\det(g) = \frac{5 \times 13}{32} = \frac{65}{32}$$

### Result

$$\det(g) = \frac{65}{32} \approx 2.031$$

---

## 4. Torsion Magnitude

$$\kappa_T = \frac{1}{b_3 - \dim(G_2) - 2}$$

### Calculation

$$\kappa_T = \frac{1}{77 - 14 - 2} = \frac{1}{61}$$

### Result

$$\kappa_T = \frac{1}{61} \approx 0.0164$$

Note: 61 is the 18th prime number.

---

## 5. CP Violation Phase

$$\delta_{CP} = 7 \cdot \dim(G_2) + H^*$$

### Calculation

$$\delta_{CP} = 7 \times 14 + 99 = 98 + 99 = 197$$

### Result

$$\delta_{CP} = 197°$$

**Experimental value**: 197° ± 24° (T2K/NOvA combined)  
**DUNE sensitivity**: ±5° by 2030

---

## 6. Tau-Electron Mass Ratio

$$\frac{m_\tau}{m_e} = \dim(K_7) + 10 \cdot \dim(E_8) + 10 \cdot H^*$$

### Calculation

$$\frac{m_\tau}{m_e} = 7 + 10 \times 248 + 10 \times 99$$
$$= 7 + 2480 + 990 = 3477$$

### Result

$$\frac{m_\tau}{m_e} = 3477$$

**Experimental value**: 3477.23 ± 0.23  
**Deviation**: 0.007%

---

## 7. Strange-Down Mass Ratio

$$\frac{m_s}{m_d} = 4 \times \text{Weyl} = b_2 - 1$$

### Calculation

$$\frac{m_s}{m_d} = 4 \times 5 = 20$$

Or equivalently:

$$\frac{m_s}{m_d} = 21 - 1 = 20$$

### Result

$$\frac{m_s}{m_d} = 20$$

**Experimental value**: 20.2 ± 1.5  
**Deviation**: 1.0%

---

## 8. Koide Parameter

$$Q = \frac{\dim(G_2)}{b_2}$$

### Calculation

$$Q = \frac{14}{21} = \frac{2}{3}$$

### Result

$$Q = \frac{2}{3} \approx 0.6667$$

**Koide's original formula**: Q = (m_e + m_μ + m_τ) / (√m_e + √m_μ + √m_τ)² = 0.6666...

---

## 9. Higgs Coupling Numerator

$$\lambda_H = \sqrt{\frac{\dim(G_2) + N_{gen}}{2^{\text{Weyl}}}}$$

### Numerator

$$\text{numerator} = \dim(G_2) + N_{gen} = 14 + 3 = 17$$

### Denominator

$$\text{denominator} = 2^{\text{Weyl}} = 2^5 = 32$$

### Result

$$\lambda_H = \sqrt{\frac{17}{32}} \approx 0.729$$

---

## 10. Cohomological Dimension H*

$$H^* = b_2 + b_3 + 1$$

### Calculation

$$H^* = 21 + 77 + 1 = 99$$

### Result

$$H^* = 99 = 9 \times 11 = 3^2 \times 11$$

---

## 11. Binary Duality p₂

$$p_2 = \frac{\dim(G_2)}{\dim(K_7)}$$

### Calculation

$$p_2 = \frac{14}{7} = 2$$

### Result

$$p_2 = 2$$

---

## 12. Generation Number

N_gen is the unique positive integer satisfying:

$$(\text{rank}(E_8) + N) \times b_2 = N \times b_3$$

### Derivation

$$(8 + N) \times 21 = N \times 77$$
$$168 + 21N = 77N$$
$$168 = 56N$$
$$N = 3$$

### Result

$$N_{gen} = 3$$

---

## 13. E₈×E₈ Dimension

$$\dim(E_8 \times E_8) = 2 \times \dim(E_8)$$

### Calculation

$$\dim(E_8 \times E_8) = 2 \times 248 = 496$$

### Result

$$\dim(E_8 \times E_8) = 496$$

---

## Summary

All 13 relations are arithmetic identities involving only the topological integers. No continuous parameters are adjusted.

| Relation | Formula | Value |
|----------|---------|-------|
| sin²θ_W | b₂/(b₃ + dim G₂) | 3/13 |
| τ | (496×21)/(27×99) | 3472/891 |
| det(g) | 5×13/32 | 65/32 |
| κ_T | 1/(77-14-2) | 1/61 |
| δ_CP | 7×14 + 99 | 197 |
| m_τ/m_e | 7 + 2480 + 990 | 3477 |
| m_s/m_d | 4×5 | 20 |
| Q_Koide | 14/21 | 2/3 |
| λ_H | √(17/32) | √17/√32 |
| H* | 21 + 77 + 1 | 99 |
| p₂ | 14/7 | 2 |
| N_gen | constraint solution | 3 |
| dim(E₈×E₈) | 2×248 | 496 |
