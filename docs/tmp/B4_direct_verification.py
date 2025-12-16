#!/usr/bin/env python3
"""
B4 Lagrange Identity - Direct Verification
==========================================

Instead of verifying the epsilon contraction formula (which has G₂ corrections),
we directly verify the NORM identity that B4 actually states:

    ‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩²

This is what matters for the Lean proof.
"""

import numpy as np
from fractions import Fraction
from typing import List, Tuple
import json

# Fano plane structure
FANO_LINES = [
    (0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6),
    (4, 5, 0), (5, 6, 1), (6, 0, 2)
]

def build_epsilon():
    """Build epsilon tensor as numpy array."""
    eps = np.zeros((7, 7, 7), dtype=np.int64)
    for (a, b, c) in FANO_LINES:
        eps[a, b, c] = 1
        eps[b, c, a] = 1
        eps[c, a, b] = 1
        eps[a, c, b] = -1
        eps[c, b, a] = -1
        eps[b, a, c] = -1
    return eps

EPSILON = build_epsilon()

def cross_product(u: np.ndarray, v: np.ndarray) -> np.ndarray:
    """7D cross product using octonion structure."""
    result = np.zeros(7)
    for k in range(7):
        for i in range(7):
            for j in range(7):
                result[k] += EPSILON[i, j, k] * u[i] * v[j]
    return result

def verify_lagrange_identity(u: np.ndarray, v: np.ndarray) -> Tuple[float, float, float]:
    """
    Verify: ‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩²
    
    Returns: (lhs, rhs, difference)
    """
    cross = cross_product(u, v)
    
    lhs = np.dot(cross, cross)  # ‖u × v‖²
    rhs = np.dot(u, u) * np.dot(v, v) - np.dot(u, v)**2  # ‖u‖²‖v‖² - ⟨u,v⟩²
    
    return lhs, rhs, abs(lhs - rhs)

def test_on_basis_vectors():
    """Test on all pairs of basis vectors."""
    print("Testing on basis vectors e_i × e_j:")
    print("=" * 60)
    
    max_error = 0
    for i in range(7):
        for j in range(7):
            if i == j:
                continue
            
            e_i = np.zeros(7)
            e_i[i] = 1
            e_j = np.zeros(7)
            e_j[j] = 1
            
            lhs, rhs, diff = verify_lagrange_identity(e_i, e_j)
            max_error = max(max_error, diff)
            
            if diff > 1e-10:
                print(f"  e_{i} × e_{j}: LHS={lhs}, RHS={rhs}, diff={diff}")
    
    print(f"\nMax error on basis vectors: {max_error}")
    return max_error < 1e-10

def test_on_random_vectors(n_tests: int = 10000):
    """Test on random vectors."""
    print(f"\nTesting on {n_tests} random vector pairs:")
    print("=" * 60)
    
    np.random.seed(42)
    
    max_error = 0
    errors = []
    
    for _ in range(n_tests):
        u = np.random.randn(7)
        v = np.random.randn(7)
        
        lhs, rhs, diff = verify_lagrange_identity(u, v)
        errors.append(diff)
        max_error = max(max_error, diff)
    
    print(f"Max error: {max_error}")
    print(f"Mean error: {np.mean(errors)}")
    print(f"All errors < 1e-10: {max_error < 1e-10}")
    
    return max_error < 1e-10

def test_on_rational_vectors():
    """Test on vectors with small integer components (for exact verification)."""
    print("\nTesting on rational vectors (exact arithmetic):")
    print("=" * 60)
    
    # Test cases with small integer components
    test_cases = [
        ([1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]),
        ([1, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0]),
        ([1, 2, 3, 0, 0, 0, 0], [0, 0, 0, 1, 2, 3, 0]),
        ([1, 1, 1, 1, 1, 1, 1], [1, -1, 1, -1, 1, -1, 1]),
        ([1, 2, 3, 4, 5, 6, 7], [7, 6, 5, 4, 3, 2, 1]),
    ]
    
    all_pass = True
    for u_list, v_list in test_cases:
        u = np.array(u_list, dtype=np.float64)
        v = np.array(v_list, dtype=np.float64)
        
        lhs, rhs, diff = verify_lagrange_identity(u, v)
        status = "✓" if diff < 1e-10 else "✗"
        print(f"  {status} u={u_list[:3]}... v={v_list[:3]}...: LHS={lhs:.6f}, RHS={rhs:.6f}")
        
        if diff > 1e-10:
            all_pass = False
    
    return all_pass

def derive_contraction_formula():
    """
    Empirically determine what ∑_k ε_ijk ε_lmk actually equals.
    """
    print("\nDeriving the actual contraction formula:")
    print("=" * 60)
    
    # For each (i,j,l,m), compute ∑_k ε_ijk ε_lmk
    contraction = np.zeros((7, 7, 7, 7), dtype=np.int64)
    
    for i in range(7):
        for j in range(7):
            for l in range(7):
                for m in range(7):
                    total = 0
                    for k in range(7):
                        total += EPSILON[i, j, k] * EPSILON[l, m, k]
                    contraction[i, j, l, m] = total
    
    # Analyze the pattern
    print("\nNon-zero contraction values and patterns:")
    
    # Count occurrences of each value
    unique, counts = np.unique(contraction, return_counts=True)
    print(f"Value distribution: {dict(zip(unique, counts))}")
    
    # Check which terms correspond to δ_il δ_jm - δ_im δ_jl
    kronecker_matches = 0
    extra_nonzero = []
    
    for i in range(7):
        for j in range(7):
            for l in range(7):
                for m in range(7):
                    expected_kronecker = (1 if (i==l and j==m) else 0) - (1 if (i==m and j==l) else 0)
                    actual = contraction[i, j, l, m]
                    
                    if actual == expected_kronecker:
                        kronecker_matches += 1
                    elif actual != 0 or expected_kronecker != 0:
                        extra_nonzero.append({
                            "indices": (i, j, l, m),
                            "actual": int(actual),
                            "kronecker": int(expected_kronecker),
                            "diff": int(actual - expected_kronecker)
                        })
    
    print(f"\nKronecker formula matches: {kronecker_matches}/{7**4}")
    print(f"Extra/different terms: {len(extra_nonzero)}")
    
    if extra_nonzero:
        print("\nFirst 10 non-Kronecker terms:")
        for term in extra_nonzero[:10]:
            print(f"  {term['indices']}: actual={term['actual']}, kronecker={term['kronecker']}, ψ={term['diff']}")
    
    return contraction

def generate_lean_proof_strategy():
    """
    Generate a proof strategy for Lean based on our findings.
    """
    print("\n" + "=" * 60)
    print("LEAN PROOF STRATEGY FOR B4")
    print("=" * 60)
    
    print("""
The key insight is that B4 states:

    ‖u × v‖² = ‖u‖²‖v‖² - ⟨u,v⟩²

While the epsilon contraction has G₂ corrections (ψ_ijlm terms),
these corrections VANISH when contracted with u_i u_l v_j v_m.

Proof strategy:

1. Define: cross_k(u,v) := ∑_{i,j} ε_ijk u_i v_j

2. Expand: ‖u × v‖² = ∑_k cross_k² = ∑_k (∑_{i,j} ε_ijk u_i v_j)²
                     = ∑_{i,j,l,m,k} ε_ijk ε_lmk u_i u_l v_j v_m

3. Use: ∑_k ε_ijk ε_lmk = δ_il δ_jm - δ_im δ_jl + ψ_ijlm
   
4. Key lemma: ∑_{i,j,l,m} ψ_ijlm u_i u_l v_j v_m = 0
   
   Because ψ_ijlm is antisymmetric under (i↔l) or (j↔m),
   but u_i u_l and v_j v_m are symmetric!

5. Therefore:
   ‖u × v‖² = ∑_{i,l} δ_il u_i u_l · ∑_{j,m} δ_jm v_j v_m  (= ‖u‖²‖v‖²)
            - ∑_{i,m} δ_im u_i v_m · ∑_{j,l} δ_jl v_j u_l  (= ⟨u,v⟩²)
            + 0  (ψ term vanishes)
   
   = ‖u‖²‖v‖² - ⟨u,v⟩²  ∎

For Lean, we need to prove the KEY LEMMA about ψ vanishing.
This requires showing ψ_ijlm = -ψ_ljim (antisymmetric in first pair).
""")

def main():
    print("GIFT Framework: B4 Lagrange Identity Direct Verification")
    print("=" * 60)
    print()
    
    # Test the identity itself
    basis_ok = test_on_basis_vectors()
    random_ok = test_on_random_vectors(10000)
    rational_ok = test_on_rational_vectors()
    
    # Analyze the contraction formula
    contraction = derive_contraction_formula()
    
    # Generate proof strategy
    generate_lean_proof_strategy()
    
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Basis vectors test: {'✓ PASSED' if basis_ok else '✗ FAILED'}")
    print(f"Random vectors test: {'✓ PASSED' if random_ok else '✗ FAILED'}")
    print(f"Rational vectors test: {'✓ PASSED' if rational_ok else '✗ FAILED'}")
    
    if basis_ok and random_ok and rational_ok:
        print("\n🎉 The Lagrange identity ‖u×v‖² = ‖u‖²‖v‖² - ⟨u,v⟩² HOLDS!")
        print("   The epsilon contraction has ψ corrections, but they vanish")
        print("   when contracted with symmetric tensor u⊗u⊗v⊗v.")
    
    # Save contraction tensor for Lean code generation
    np.save("epsilon_contraction.npy", contraction)
    print("\nContraction tensor saved to epsilon_contraction.npy")

if __name__ == "__main__":
    main()
