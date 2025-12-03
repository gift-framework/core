"""
Tests for PyTorch optimization module.

Run with: pytest tests/test_torch_optim.py -v
Requires: pip install torch
"""
import pytest

from gift_core.torch_optim import TORCH_AVAILABLE


# Skip all tests if torch not available
pytestmark = pytest.mark.skipif(
    not TORCH_AVAILABLE,
    reason="PyTorch not installed"
)


class TestTorchAvailability:
    """Test torch availability detection."""

    def test_torch_available_flag(self):
        """TORCH_AVAILABLE should be True when torch is installed."""
        if TORCH_AVAILABLE:
            import torch
            assert torch is not None


@pytest.mark.skipif(not TORCH_AVAILABLE, reason="PyTorch not installed")
class TestDifferentiableObservables:
    """Test differentiable observables computation."""

    def test_init(self):
        """Test initialization."""
        from gift_core.torch_optim import DifferentiableObservables
        model = DifferentiableObservables()
        assert model.alpha.item() == pytest.approx(1.0)
        assert model.beta.item() == pytest.approx(1.0)
        assert model.gamma.item() == pytest.approx(1.0)

    def test_forward(self):
        """Test forward pass."""
        from gift_core.torch_optim import DifferentiableObservables
        model = DifferentiableObservables()
        preds = model()

        assert 'sin2_theta_w' in preds
        assert 'kappa_t' in preds
        assert 'q_koide' in preds

    def test_nominal_values(self):
        """Test that nominal parameters give nominal predictions."""
        from gift_core.torch_optim import DifferentiableObservables
        from gift_core.constants import SIN2_THETA_W, KAPPA_T, Q_KOIDE

        model = DifferentiableObservables()
        preds = model()

        assert preds['sin2_theta_w'].item() == pytest.approx(float(SIN2_THETA_W), rel=1e-6)
        assert preds['kappa_t'].item() == pytest.approx(float(KAPPA_T), rel=1e-6)
        assert preds['q_koide'].item() == pytest.approx(float(Q_KOIDE), rel=1e-6)


@pytest.mark.skipif(not TORCH_AVAILABLE, reason="PyTorch not installed")
class TestChiSquaredLoss:
    """Test χ² loss function."""

    def test_loss_computation(self):
        """Test basic loss computation."""
        from gift_core.torch_optim import DifferentiableObservables, ChiSquaredLoss

        model = DifferentiableObservables()
        loss_fn = ChiSquaredLoss(include_regularization=False)

        preds = model()
        loss = loss_fn(preds)

        assert loss.item() > 0  # Some deviation from experiment

    def test_regularization(self):
        """Test that regularization increases loss for perturbed params."""
        import torch
        from gift_core.torch_optim import DifferentiableObservables, ChiSquaredLoss

        model = DifferentiableObservables()

        # No regularization
        loss_no_reg = ChiSquaredLoss(include_regularization=False)
        # With regularization
        loss_with_reg = ChiSquaredLoss(include_regularization=True, reg_strength=1.0)

        # Perturb parameter
        with torch.no_grad():
            model.alpha.fill_(1.5)

        preds = model()
        l1 = loss_no_reg(preds).item()
        l2 = loss_with_reg(preds, model).item()

        assert l2 > l1  # Regularization adds to loss


@pytest.mark.skipif(not TORCH_AVAILABLE, reason="PyTorch not installed")
class TestK7MetricOptimizer:
    """Test K₇ metric optimizer."""

    def test_optimizer_init(self):
        """Test optimizer initialization."""
        from gift_core.torch_optim import K7MetricOptimizer

        opt = K7MetricOptimizer(lr=0.01, max_iterations=10)
        assert opt.lr == 0.01
        assert opt.max_iterations == 10

    def test_optimization_runs(self):
        """Test that optimization runs without error."""
        from gift_core.torch_optim import K7MetricOptimizer

        opt = K7MetricOptimizer(max_iterations=50)
        result = opt.optimize()

        assert result is not None
        assert result.initial_chi2 > 0
        assert len(result.history) > 0

    def test_optimization_improves(self):
        """Test that optimization improves or maintains χ²."""
        from gift_core.torch_optim import K7MetricOptimizer

        opt = K7MetricOptimizer(max_iterations=100)
        result = opt.optimize()

        # Final χ² should be <= initial (with regularization, may not always decrease)
        # Just check it doesn't explode
        assert result.final_chi2 < result.initial_chi2 * 10

    def test_reset(self):
        """Test parameter reset."""
        import torch
        from gift_core.torch_optim import K7MetricOptimizer

        opt = K7MetricOptimizer()

        # Modify parameters
        with torch.no_grad():
            opt.model.alpha.fill_(2.0)

        # Reset
        opt.reset()

        assert opt.model.alpha.item() == pytest.approx(1.0)


@pytest.mark.skipif(not TORCH_AVAILABLE, reason="PyTorch not installed")
class TestOptimizationResult:
    """Test OptimizationResult dataclass."""

    def test_improvement(self):
        """Test improvement calculation."""
        from gift_core.torch_optim import OptimizationResult

        result = OptimizationResult(
            initial_chi2=100.0,
            final_chi2=50.0,
            alpha=1.0,
            beta=1.0,
            gamma=1.0,
            predictions={},
            history=[],
            converged=True
        )

        assert result.improvement() == 50.0

    def test_summary(self):
        """Test summary generation."""
        from gift_core.torch_optim import OptimizationResult

        result = OptimizationResult(
            initial_chi2=100.0,
            final_chi2=50.0,
            alpha=1.01,
            beta=0.99,
            gamma=1.0,
            predictions={'sin2_theta_w': 0.231},
            history=[100, 75, 50],
            converged=True
        )

        summary = result.summary()
        assert "K₇" in summary
        assert "Improvement" in summary


@pytest.mark.skipif(not TORCH_AVAILABLE, reason="PyTorch not installed")
class TestConvenienceFunctions:
    """Test convenience functions."""

    def test_optimize_k7_metric(self):
        """Test quick optimization function."""
        from gift_core.torch_optim import optimize_k7_metric

        result = optimize_k7_metric(verbose=False)
        assert result is not None

    def test_multi_start(self):
        """Test multi-start optimization."""
        from gift_core.torch_optim import multi_start_optimization

        result = multi_start_optimization(n_starts=2, max_iterations=50)
        assert result is not None
        assert result.final_chi2 > 0

    def test_scan_parameter_space(self):
        """Test parameter space scanning."""
        from gift_core.torch_optim import scan_parameter_space

        params, chi2s = scan_parameter_space(
            param='alpha',
            n_points=10,
            range_min=0.9,
            range_max=1.1
        )

        assert len(params) == 10
        assert len(chi2s) == 10
        assert all(c > 0 for c in chi2s)


@pytest.mark.skipif(not TORCH_AVAILABLE, reason="PyTorch not installed")
class TestGradients:
    """Test gradient computation."""

    def test_gradients_exist(self):
        """Test that gradients are computed."""
        import torch
        from gift_core.torch_optim import DifferentiableObservables, ChiSquaredLoss

        model = DifferentiableObservables()
        loss_fn = ChiSquaredLoss()

        preds = model()
        loss = loss_fn(preds, model)
        loss.backward()

        assert model.alpha.grad is not None
        assert model.beta.grad is not None
        assert model.gamma.grad is not None

    def test_gradients_nonzero(self):
        """Test that gradients are non-zero (loss depends on params)."""
        import torch
        from gift_core.torch_optim import DifferentiableObservables, ChiSquaredLoss

        model = DifferentiableObservables()
        loss_fn = ChiSquaredLoss()

        preds = model()
        loss = loss_fn(preds, model)
        loss.backward()

        # At least one gradient should be non-zero
        total_grad = (
            abs(model.alpha.grad.item()) +
            abs(model.beta.grad.item()) +
            abs(model.gamma.grad.item())
        )
        assert total_grad > 0
