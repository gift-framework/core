"""
Tests for Monte Carlo simulation module.
"""
import pytest
from fractions import Fraction

from gift_core.constants import KAPPA_T, SIN2_THETA_W, B2, B3, DIM_G2, P2
from gift_core.scales import (
    M_PLANCK, M_STRING_DEFAULT, M_STRING_MIN, M_STRING_MAX,
    ScaleHierarchy, S7Parameters, string_scale_from_volume
)
from gift_core.experimental import (
    Measurement, Comparison, GIFT_COMPARISONS,
    SIN2_THETA_W_EXP, DELTA_CP_EXP
)
from gift_core.monte_carlo import (
    Observable, OBSERVABLES,
    MonteCarloEngine, KappaTRobustness, MCResult,
    compute_kappa_t, compute_sin2_theta_w,
    run_quick_mc, run_kappa_analysis, compare_predictions_to_experiment,
    planck_string_perturbation
)


class TestScales:
    """Test physical scale definitions."""

    def test_planck_scale(self):
        """Planck mass should be ~1.22e19 GeV."""
        assert 1e19 < M_PLANCK < 2e19

    def test_string_scale_bounds(self):
        """String scale should be between limits."""
        assert M_STRING_MIN < M_STRING_DEFAULT < M_STRING_MAX
        assert M_STRING_MAX == M_PLANCK

    def test_scale_hierarchy(self):
        """Test ScaleHierarchy class."""
        h = ScaleHierarchy()
        assert h.m_planck == M_PLANCK
        assert 0 < h.ratio_string_planck < 1
        assert h.hierarchy_ew_planck < 1e-16  # Huge hierarchy

    def test_s7_parameters(self):
        """Test S7 geometry parameters."""
        s7 = S7Parameters()
        assert s7.kappa == float(KAPPA_T)
        assert s7.volume_s7 > 0
        assert s7.volume_k7 > 0

    def test_string_scale_from_volume(self):
        """Test string scale computation."""
        m_s = string_scale_from_volume(v_k7=1.0, g_s=0.1)
        assert m_s > 0
        assert m_s < M_PLANCK


class TestExperimentalData:
    """Test experimental data structures."""

    def test_measurement_class(self):
        """Test Measurement dataclass."""
        m = Measurement(value=0.23, error_plus=0.01)
        assert m.error == 0.01
        assert m.relative_error == pytest.approx(0.01 / 0.23)

    def test_asymmetric_error(self):
        """Test asymmetric error handling."""
        m = Measurement(value=100.0, error_plus=5.0, error_minus=-3.0)
        assert m.error == 4.0  # Average

    def test_range(self):
        """Test measurement range."""
        m = Measurement(value=10.0, error_plus=1.0)
        low, high = m.range()
        assert low == 9.0
        assert high == 11.0

    def test_contains(self):
        """Test if prediction is within sigma."""
        m = Measurement(value=0.23, error_plus=0.01)
        assert m.contains(0.23)
        assert m.contains(0.235)  # Within 1 sigma
        assert not m.contains(0.25)  # Outside 1 sigma

    def test_sin2_theta_w_exp(self):
        """Test PDG value for Weinberg angle."""
        assert SIN2_THETA_W_EXP.value == pytest.approx(0.23122, rel=1e-4)
        assert SIN2_THETA_W_EXP.source == "PDG 2024"

    def test_comparison_class(self):
        """Test Comparison class."""
        c = GIFT_COMPARISONS[0]  # Weinberg angle
        assert c.symbol == "sin²θ_W"
        assert abs(c.deviation) < 100  # Reasonable deviation


class TestObservables:
    """Test observable computations."""

    def test_kappa_t_nominal(self):
        """Test κ_T at nominal parameters."""
        params = {'b3': float(B3), 'dim_g2': float(DIM_G2), 'p2': float(P2)}
        kappa = compute_kappa_t(params)
        assert kappa == pytest.approx(float(KAPPA_T), rel=1e-10)

    def test_sin2_theta_w_nominal(self):
        """Test sin²θ_W at nominal parameters."""
        params = {'b2': float(B2), 'b3': float(B3), 'dim_g2': float(DIM_G2)}
        sin2 = compute_sin2_theta_w(params)
        assert sin2 == pytest.approx(float(SIN2_THETA_W), rel=1e-10)

    def test_observables_list(self):
        """Test that all observables are defined."""
        assert len(OBSERVABLES) >= 7
        symbols = [o.symbol for o in OBSERVABLES]
        assert "κ_T" in symbols
        assert "sin²θ_W" in symbols

    def test_observable_compute(self):
        """Test observable compute functions."""
        for obs in OBSERVABLES:
            # Should work with empty params (uses defaults)
            value = obs.compute({})
            assert value == pytest.approx(obs.nominal_value, rel=0.1)


class TestPerturbation:
    """Test scale perturbation models."""

    def test_planck_string_perturbation(self):
        """Test perturbation from string scale."""
        # At Planck scale, perturbation is maximal
        pert_planck = planck_string_perturbation(M_PLANCK)
        assert pert_planck.delta_b2 > 0
        assert pert_planck.delta_b3 > 0

        # At low string scale, perturbation is minimal
        pert_low = planck_string_perturbation(M_STRING_MIN)
        assert pert_low.delta_b2 < pert_planck.delta_b2
        assert pert_low.delta_b3 < pert_planck.delta_b3

    def test_perturbation_apply(self):
        """Test applying perturbation to params."""
        pert = planck_string_perturbation(M_STRING_DEFAULT)
        base = {'b2': 21.0, 'b3': 77.0, 'dim_g2': 14.0, 'p2': 2.0}
        perturbed = pert.apply(base)

        # Should be close to nominal
        assert perturbed['b2'] == pytest.approx(21.0, rel=0.1)
        assert perturbed['b3'] == pytest.approx(77.0, rel=0.1)


class TestMonteCarloEngine:
    """Test Monte Carlo engine."""

    def test_engine_init(self):
        """Test engine initialization."""
        engine = MonteCarloEngine(n_samples=100, seed=42)
        assert engine.n_samples == 100
        assert engine.seed == 42

    def test_sample_string_scale(self):
        """Test string scale sampling."""
        engine = MonteCarloEngine(seed=42)
        for _ in range(100):
            m_s = engine.sample_string_scale()
            assert M_STRING_MIN <= m_s <= M_STRING_MAX

    def test_run_simulation(self):
        """Test running simulation."""
        engine = MonteCarloEngine(n_samples=100, seed=42)
        results = engine.run()

        assert len(results) == len(OBSERVABLES)
        for symbol, result in results.items():
            assert len(result.samples) == 100
            assert result.mean > 0

    def test_reproducibility(self):
        """Test that same seed gives same results."""
        engine1 = MonteCarloEngine(n_samples=50, seed=123)
        engine2 = MonteCarloEngine(n_samples=50, seed=123)

        results1 = engine1.run()
        results2 = engine2.run()

        for symbol in results1:
            assert results1[symbol].mean == results2[symbol].mean

    def test_summary(self):
        """Test summary generation."""
        engine = MonteCarloEngine(n_samples=50, seed=42)
        engine.run()
        summary = engine.summary()

        assert "Monte Carlo" in summary
        assert "κ_T" in summary
        assert "sin²θ_W" in summary


class TestMCResult:
    """Test MCResult dataclass."""

    def test_statistics(self):
        """Test statistical calculations."""
        obs = OBSERVABLES[0]
        result = MCResult(observable=obs)
        result.samples = [1.0, 2.0, 3.0, 4.0, 5.0]

        assert result.mean == 3.0
        assert result.min_val == 1.0
        assert result.max_val == 5.0
        assert result.std > 0

    def test_percentile(self):
        """Test percentile calculation."""
        obs = OBSERVABLES[0]
        result = MCResult(observable=obs)
        result.samples = list(range(100))

        assert result.percentile(50) == pytest.approx(50, abs=1)
        assert result.percentile(0) == 0
        assert result.percentile(100) == 99

    def test_robustness(self):
        """Test robustness score."""
        obs = OBSERVABLES[0]
        result = MCResult(observable=obs)

        # Very consistent samples
        result.samples = [1.0, 1.0, 1.0, 1.0, 1.0]
        assert result.robustness == 1.0

        # Variable samples
        result.samples = [0.5, 1.0, 1.5, 2.0, 2.5]
        assert 0 < result.robustness < 1


class TestKappaTRobustness:
    """Test κ_T robustness analysis."""

    def test_init(self):
        """Test initialization."""
        analysis = KappaTRobustness(n_samples=100, seed=42)
        assert analysis.n_samples == 100

    def test_scale_scan(self):
        """Test scale scan."""
        analysis = KappaTRobustness()
        results = analysis.run_scale_scan(n_points=10)

        assert len(results['m_string']) == 10
        assert len(results['kappa_t']) == 10
        assert all(k > 0 for k in results['kappa_t'])

    def test_monte_carlo(self):
        """Test Monte Carlo run."""
        analysis = KappaTRobustness(n_samples=100, seed=42)
        analysis.run_monte_carlo()

        assert len(analysis.results['kappa_t']) == 100
        assert len(analysis.results['m_string']) == 100

        # κ_T should be close to 1/61
        mean_kappa = sum(analysis.results['kappa_t']) / 100
        assert mean_kappa == pytest.approx(float(KAPPA_T), rel=0.1)

    def test_summary(self):
        """Test summary generation."""
        analysis = KappaTRobustness(n_samples=50, seed=42)
        analysis.run_monte_carlo()
        summary = analysis.summary()

        assert "κ_T" in summary
        assert "Robustness" in summary


class TestConvenienceFunctions:
    """Test convenience functions."""

    def test_run_quick_mc(self):
        """Test quick MC function."""
        engine = run_quick_mc(n_samples=50, seed=42)
        assert len(engine.results) > 0
        assert all(len(r.samples) == 50 for r in engine.results.values())

    def test_run_kappa_analysis(self):
        """Test κ_T analysis function."""
        analysis = run_kappa_analysis(n_samples=50, seed=42)
        assert len(analysis.results['kappa_t']) == 50

    def test_compare_predictions(self):
        """Test comparison function."""
        output = compare_predictions_to_experiment()
        assert "GIFT" in output
        assert "Exp" in output
        assert "sin²θ_W" in output


class TestKappaTStability:
    """Test κ_T stability across scale variations."""

    def test_kappa_t_is_stable(self):
        """
        κ_T should be robust: mean close to 1/61,
        with small relative standard deviation.
        """
        analysis = KappaTRobustness(n_samples=1000, seed=42)
        analysis.run_monte_carlo()

        kappa_values = analysis.results['kappa_t']
        mean = sum(kappa_values) / len(kappa_values)
        nominal = float(KAPPA_T)

        # Mean should be within 5% of nominal
        assert abs(mean - nominal) / nominal < 0.05

        # Robustness should be high (>90%)
        std = (sum((x - mean) ** 2 for x in kappa_values) / len(kappa_values)) ** 0.5
        robustness = 1 - std / abs(mean)
        assert robustness > 0.90
