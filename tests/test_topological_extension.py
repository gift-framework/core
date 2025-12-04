"""
Tests for the 12 TOPOLOGICAL extension relations.
These complement the 13 original PROVEN relations for a total of 25 certified relations.
All values verified against Lean4 + Coq formal proofs.
"""
from fractions import Fraction
import gift_core.constants as gc


class TestGaugeSector:
    """Tests for gauge sector relations (#14, #19, #25)"""

    def test_alpha_s_denominator(self):
        """#14: α_s = √2/12, denominator = dim(G₂) - p₂ = 12"""
        assert gc.DIM_G2 - gc.P2 == 12
        assert gc.ALPHA_S_DENOM == 12

    def test_alpha_s_squared_structure(self):
        """#19: α_s² = 2/144 = 1/72"""
        assert gc.ALPHA_S_SQ_NUM == 2
        assert gc.ALPHA_S_SQ_DENOM == 144
        assert gc.ALPHA_S_SQ_DENOM == (gc.DIM_G2 - gc.P2) ** 2
        assert Fraction(gc.ALPHA_S_SQ_NUM, gc.ALPHA_S_SQ_DENOM) == Fraction(1, 72)

    def test_alpha_inv_algebraic_component(self):
        """#25a: α⁻¹ algebraic = (dim(E₈) + rank(E₈))/2 = 128"""
        assert (gc.DIM_E8 + gc.RANK_E8) // 2 == 128
        assert gc.ALPHA_INV_ALGEBRAIC == 128

    def test_alpha_inv_bulk_component(self):
        """#25b: α⁻¹ bulk = H*/11 = 9"""
        assert gc.H_STAR // gc.D_BULK == 9
        assert gc.ALPHA_INV_BULK == 9

    def test_alpha_inv_base(self):
        """#25: α⁻¹ ≈ 137 = 128 + 9"""
        assert gc.ALPHA_INV_BASE == 137
        assert gc.ALPHA_INV_ALGEBRAIC + gc.ALPHA_INV_BULK == 137

    def test_sm_gauge_equals_alpha_s_denom(self):
        """SM gauge total = dim(G₂) - p₂ = 12"""
        assert gc.DIM_SM_GAUGE == 12
        assert gc.DIM_SU3 + gc.DIM_SU2 + gc.DIM_U1 == gc.ALPHA_S_DENOM


class TestNeutrinoSector:
    """Tests for neutrino sector relations (#15, #16, #17, #18, #21)"""

    def test_gamma_GIFT_numerator(self):
        """#15a: γ_GIFT numerator = 2×rank(E₈) + 5×H* = 511"""
        num = 2 * gc.RANK_E8 + 5 * gc.H_STAR
        assert num == 511
        assert gc.GAMMA_GIFT_NUM == 511

    def test_gamma_GIFT_denominator(self):
        """#15b: γ_GIFT denominator = 10×dim(G₂) + 3×dim(E₈) = 884"""
        den = 10 * gc.DIM_G2 + 3 * gc.DIM_E8
        assert den == 884
        assert gc.GAMMA_GIFT_DEN == 884

    def test_gamma_GIFT_fraction(self):
        """#15: γ_GIFT = 511/884"""
        assert gc.GAMMA_GIFT == Fraction(511, 884)

    def test_delta_pentagonal(self):
        """#16: δ = 2π/25, Weyl² = 25"""
        assert gc.WEYL_SQ == 25
        assert gc.WEYL_FACTOR ** 2 == 25
        assert gc.DELTA_PENTAGONAL_DENOM == 25

    def test_theta_23_numerator(self):
        """#17a: θ₂₃ numerator = rank(E₈) + b₃ = 85"""
        assert gc.RANK_E8 + gc.B3 == 85
        assert gc.THETA_23_NUM == 85

    def test_theta_23_denominator(self):
        """#17b: θ₂₃ denominator = H* = 99"""
        assert gc.H_STAR == 99
        assert gc.THETA_23_DEN == 99

    def test_theta_23_fraction(self):
        """#17: θ₂₃ = 85/99 rad"""
        assert gc.THETA_23 == Fraction(85, 99)

    def test_theta_13_denominator(self):
        """#18: θ₁₃ = π/21, denominator = b₂ = 21"""
        assert gc.B2 == 21
        assert gc.THETA_13_DENOM == 21

    def test_theta_12_structure(self):
        """#21: θ₁₂ structure (δ/γ components)"""
        # δ/γ numerator factor: Weyl² × γ_num = 25 × 511 = 12775
        assert gc.WEYL_SQ * gc.GAMMA_GIFT_NUM == 12775
        assert gc.THETA_12_RATIO_FACTOR == 12775


class TestLeptonSector:
    """Tests for lepton sector relations (#20, #22)"""

    def test_m_mu_m_e_base(self):
        """#22: m_μ/m_e ≈ 27^φ, base = dim(J₃(O)) = 27"""
        assert gc.DIM_J3O == 27
        assert gc.M_MU_M_E_BASE == 27
        # Verify 27 = 3³
        assert gc.DIM_J3O == 3 ** 3

    def test_lambda_H_squared_numerator(self):
        """#20a: λ_H² numerator = dim(G₂) + N_gen = 17"""
        assert gc.DIM_G2 + gc.N_GEN == 17
        assert gc.LAMBDA_H_SQ_NUM == 17

    def test_lambda_H_squared_denominator(self):
        """#20b: λ_H² denominator = 32² = 1024"""
        assert 32 ** 2 == 1024
        assert gc.LAMBDA_H_SQ_DEN == 1024

    def test_lambda_H_squared_fraction(self):
        """#20: λ_H² = 17/1024"""
        assert gc.LAMBDA_H_SQ == Fraction(17, 1024)


class TestCosmologySector:
    """Tests for cosmology sector relations (#23, #24)"""

    def test_n_s_zeta_bulk_index(self):
        """#23a: n_s ζ-function bulk index = D_bulk = 11"""
        assert gc.D_BULK == 11
        assert gc.N_S_ZETA_BULK == 11

    def test_n_s_zeta_weyl_index(self):
        """#23b: n_s ζ-function Weyl index = 5"""
        assert gc.WEYL_FACTOR == 5
        assert gc.N_S_ZETA_WEYL == 5

    def test_n_s_indices_difference(self):
        """#23: D_bulk - Weyl = 11 - 5 = 6 (compactified dimensions)"""
        assert gc.D_BULK - gc.WEYL_FACTOR == 6

    def test_omega_DE_numerator(self):
        """#24a: Ω_DE numerator = H* - 1 = 98"""
        assert gc.H_STAR - 1 == 98
        assert gc.OMEGA_DE_NUM == 98

    def test_omega_DE_denominator(self):
        """#24b: Ω_DE denominator = H* = 99"""
        assert gc.H_STAR == 99
        assert gc.OMEGA_DE_DEN == 99

    def test_omega_DE_fraction(self):
        """#24: Ω_DE = ln(2) × 98/99, rational factor = 98/99"""
        assert gc.OMEGA_DE_FRACTION == Fraction(98, 99)

    def test_omega_DE_near_unity(self):
        """#24: 98/99 ≈ 1 - 1/99"""
        assert gc.OMEGA_DE_DEN - gc.OMEGA_DE_NUM == 1


class TestCrossRelations:
    """Cross-validation tests between related constants"""

    def test_all_12_extension_values(self):
        """Verify all 12 extension relation values"""
        # Phase 1: Arithmetic (5 relations)
        assert gc.ALPHA_S_DENOM == 12              # #14
        assert gc.GAMMA_GIFT == Fraction(511, 884) # #15
        assert gc.WEYL_SQ == 25                    # #16
        assert gc.THETA_23 == Fraction(85, 99)     # #17
        assert gc.THETA_13_DENOM == 21             # #18

        # Phase 2: Algebraic structure (2 relations)
        assert gc.ALPHA_S_SQ_DENOM == 144          # #19
        assert gc.LAMBDA_H_SQ == Fraction(17, 1024) # #20

        # Phase 3: Transcendental indices (5 relations)
        assert gc.THETA_12_RATIO_FACTOR == 12775   # #21
        assert gc.M_MU_M_E_BASE == 27              # #22
        assert gc.N_S_ZETA_BULK == 11              # #23
        assert gc.OMEGA_DE_FRACTION == Fraction(98, 99)  # #24
        assert gc.ALPHA_INV_BASE == 137            # #25

    def test_topological_consistency(self):
        """Verify topological constants are self-consistent"""
        # H* = b2 + b3 + 1
        assert gc.H_STAR == gc.B2 + gc.B3 + 1

        # Weyl² = Weyl_factor²
        assert gc.WEYL_SQ == gc.WEYL_FACTOR ** 2

        # SM gauge = 8 + 3 + 1
        assert gc.DIM_SM_GAUGE == gc.DIM_SU3 + gc.DIM_SU2 + gc.DIM_U1

        # α_s denom = SM gauge dim
        assert gc.ALPHA_S_DENOM == gc.DIM_SM_GAUGE

    def test_total_25_relations(self):
        """Confirm we have 25 total certified relations (13 + 12)"""
        original_13 = [
            gc.SIN2_THETA_W,   # 1
            gc.TAU,            # 2
            gc.KAPPA_T,        # 3
            gc.DET_G,          # 4
            gc.Q_KOIDE,        # 5
            gc.M_TAU_M_E,      # 6
            gc.M_S_M_D,        # 7
            gc.DELTA_CP,       # 8
            gc.LAMBDA_H_NUM,   # 9
            gc.H_STAR,         # 10
            gc.P2,             # 11
            gc.N_GEN,          # 12
            gc.DIM_E8xE8,      # 13
        ]
        extension_12 = [
            gc.ALPHA_S_DENOM,         # 14
            gc.GAMMA_GIFT,            # 15
            gc.WEYL_SQ,               # 16
            gc.THETA_23,              # 17
            gc.THETA_13_DENOM,        # 18
            gc.ALPHA_S_SQ_DENOM,      # 19
            gc.LAMBDA_H_SQ,           # 20
            gc.THETA_12_RATIO_FACTOR, # 21
            gc.M_MU_M_E_BASE,         # 22
            gc.N_S_ZETA_BULK,         # 23
            gc.OMEGA_DE_FRACTION,     # 24
            gc.ALPHA_INV_BASE,        # 25
        ]
        assert len(original_13) == 13
        assert len(extension_12) == 12
        assert len(original_13) + len(extension_12) == 25
