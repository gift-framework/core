#!/usr/bin/env python3
"""
GIFT-Native PINN Training Script.

Train a Physics-Informed Neural Network with GIFT structure to learn
the G2 metric on K7 satisfying:
- Torsion-free: dphi = 0, d*phi = 0
- det(g) = 65/32 (exact)
- kappa_T = 1/61

Usage:
    python scripts/train_gift_pinn.py --epochs 5000 --device cuda
    python scripts/train_gift_pinn.py --config config.json
    python scripts/train_gift_pinn.py --resume checkpoint.pt
"""

import argparse
import json
import os
import sys
from datetime import datetime
from pathlib import Path

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

try:
    import torch
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False
    print("ERROR: PyTorch required. Install with: pip install torch")
    sys.exit(1)

from gift_core.nn.gift_native_pinn import (
    GIFTNativePINN,
    GIFTTrainConfig,
    train_gift_native_pinn,
    create_gift_native_pinn,
    export_analytical_form,
    DET_G_TARGET_FLOAT,
    TORSION_THRESHOLD,
)


def parse_args():
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Train GIFT-Native PINN for G2 metric learning"
    )

    # Training parameters
    parser.add_argument(
        '--epochs', type=int, default=5000,
        help='Number of training epochs (default: 5000)'
    )
    parser.add_argument(
        '--batch-size', type=int, default=1024,
        help='Batch size (default: 1024)'
    )
    parser.add_argument(
        '--lr', type=float, default=1e-3,
        help='Learning rate (default: 1e-3)'
    )
    parser.add_argument(
        '--device', type=str, default='auto',
        choices=['auto', 'cpu', 'cuda', 'mps'],
        help='Device to use (default: auto)'
    )

    # Architecture parameters
    parser.add_argument(
        '--num-frequencies', type=int, default=32,
        help='Number of Fourier frequencies (default: 32)'
    )
    parser.add_argument(
        '--hidden-dims', type=str, default='128,128,128',
        help='Hidden layer dimensions (default: 128,128,128)'
    )
    parser.add_argument(
        '--perturbation-scale', type=float, default=0.01,
        help='Scale of perturbations around phi0 (default: 0.01)'
    )

    # Loss weights
    parser.add_argument(
        '--det-weight', type=float, default=100.0,
        help='Weight for determinant loss (default: 100.0)'
    )
    parser.add_argument(
        '--torsion-weight', type=float, default=1.0,
        help='Weight for torsion loss (default: 1.0)'
    )

    # Target criteria
    parser.add_argument(
        '--target-torsion', type=float, default=0.001,
        help='Target torsion norm for early stopping (default: 0.001)'
    )
    parser.add_argument(
        '--target-det-error', type=float, default=1e-6,
        help='Target det(g) error for early stopping (default: 1e-6)'
    )

    # I/O
    parser.add_argument(
        '--output-dir', type=str, default='outputs',
        help='Output directory (default: outputs)'
    )
    parser.add_argument(
        '--checkpoint-freq', type=int, default=500,
        help='Checkpoint frequency in epochs (default: 500)'
    )
    parser.add_argument(
        '--resume', type=str, default=None,
        help='Resume from checkpoint file'
    )
    parser.add_argument(
        '--config', type=str, default=None,
        help='Load configuration from JSON file'
    )

    # Misc
    parser.add_argument(
        '--seed', type=int, default=42,
        help='Random seed (default: 42)'
    )
    parser.add_argument(
        '--quiet', action='store_true',
        help='Reduce output verbosity'
    )

    return parser.parse_args()


def get_device(device_str: str) -> str:
    """Determine the best device to use."""
    if device_str == 'auto':
        if torch.cuda.is_available():
            return 'cuda'
        elif hasattr(torch.backends, 'mps') and torch.backends.mps.is_available():
            return 'mps'
        else:
            return 'cpu'
    return device_str


def setup_output_dir(output_dir: str) -> Path:
    """Create output directory with timestamp."""
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    run_dir = Path(output_dir) / f'gift_pinn_{timestamp}'
    run_dir.mkdir(parents=True, exist_ok=True)
    return run_dir


def save_config(config: GIFTTrainConfig, path: Path):
    """Save configuration to JSON."""
    config_dict = {
        'epochs': config.epochs,
        'batch_size': config.batch_size,
        'learning_rate': config.learning_rate,
        'det_weight': config.det_weight,
        'torsion_weight': config.torsion_weight,
        'topo_weight': config.topo_weight,
        'sparse_weight': config.sparse_weight,
        'target_torsion': config.target_torsion,
        'target_det_error': config.target_det_error,
        'device': config.device,
    }
    with open(path, 'w') as f:
        json.dump(config_dict, f, indent=2)


def save_checkpoint(model, result, config, path: Path):
    """Save model checkpoint."""
    torch.save({
        'model_state_dict': model.state_dict(),
        'config': {
            'num_frequencies': model.fourier.num_frequencies,
            'perturbation_scale': model.perturbation_scale,
        },
        'training_result': {
            'final_torsion': result.final_torsion,
            'final_det_error': result.final_det_error,
            'epochs_trained': result.epochs_trained,
            'converged': result.converged,
        },
        'best_state_dict': result.best_state_dict,
        'best_epoch': result.best_epoch,
    }, path)


def save_training_history(result, path: Path):
    """Save training history to JSON."""
    history = {
        'loss': result.loss_history,
        'torsion': result.torsion_history,
        'det_error': result.det_error_history,
        'epochs_trained': result.epochs_trained,
        'converged': result.converged,
        'best_epoch': result.best_epoch,
    }
    with open(path, 'w') as f:
        json.dump(history, f, indent=2)


def print_banner():
    """Print training banner."""
    print("=" * 60)
    print("  GIFT-Native PINN Training")
    print("  G2 Metric Learning with Built-in Algebraic Structure")
    print("=" * 60)
    print()
    print("Target constraints:")
    print(f"  - det(g) = 65/32 = {DET_G_TARGET_FLOAT:.6f}")
    print(f"  - ||T|| < {TORSION_THRESHOLD:.4f} (Joyce threshold)")
    print(f"  - Target: ||T|| < 0.001 (20x margin)")
    print()


def print_summary(result, elapsed_time: float):
    """Print training summary."""
    print()
    print("=" * 60)
    print("  Training Summary")
    print("=" * 60)
    print(f"  Epochs trained: {result.epochs_trained}")
    print(f"  Best epoch: {result.best_epoch}")
    print(f"  Converged: {result.converged}")
    print()
    print("  Final metrics:")
    print(f"    Torsion norm: {result.final_torsion:.6f}")
    print(f"    Det(g) error: {result.final_det_error:.8f}")
    print(f"    Total loss: {result.final_loss:.6f}")
    print()
    print(f"  Training time: {elapsed_time:.1f} seconds")
    print("=" * 60)


def main():
    """Main training function."""
    args = parse_args()

    # Load config from file if provided
    if args.config:
        with open(args.config, 'r') as f:
            config_dict = json.load(f)
        for key, value in config_dict.items():
            if hasattr(args, key):
                setattr(args, key, value)

    # Set random seed
    torch.manual_seed(args.seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed(args.seed)

    # Determine device
    device = get_device(args.device)

    if not args.quiet:
        print_banner()
        print(f"Using device: {device}")
        print()

    # Parse hidden dimensions
    hidden_dims = [int(d) for d in args.hidden_dims.split(',')]

    # Create model
    model = create_gift_native_pinn(
        num_frequencies=args.num_frequencies,
        hidden_dims=hidden_dims,
        perturbation_scale=args.perturbation_scale,
    )

    # Resume from checkpoint if provided
    if args.resume:
        print(f"Resuming from {args.resume}")
        checkpoint = torch.load(args.resume, map_location=device)
        model.load_state_dict(checkpoint['model_state_dict'])

    # Create training config
    config = GIFTTrainConfig(
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.lr,
        det_weight=args.det_weight,
        torsion_weight=args.torsion_weight,
        target_torsion=args.target_torsion,
        target_det_error=args.target_det_error,
        checkpoint_freq=args.checkpoint_freq,
        device=device,
    )

    # Setup output directory
    output_dir = setup_output_dir(args.output_dir)
    print(f"Output directory: {output_dir}")

    # Save config
    save_config(config, output_dir / 'config.json')

    # Train
    print()
    print("Starting training...")
    print("-" * 40)

    import time
    start_time = time.time()

    result = train_gift_native_pinn(
        model=model,
        config=config,
        verbose=not args.quiet,
    )

    elapsed_time = time.time() - start_time

    # Save results
    save_checkpoint(model, result, config, output_dir / 'final_model.pt')
    save_checkpoint(model, result, config, output_dir / 'best_model.pt')
    save_training_history(result, output_dir / 'history.json')

    # Load best model and save it
    if result.best_state_dict:
        model.load_state_dict(result.best_state_dict)
        torch.save(model.state_dict(), output_dir / 'best_model_state.pt')

    # Export analytical form
    print()
    print("Extracting analytical form...")
    export_analytical_form(
        model,
        str(output_dir / 'phi_analytical_coefficients.json'),
        grid_resolution=32,
    )

    if not args.quiet:
        print_summary(result, elapsed_time)

    # Print output paths
    print()
    print("Output files:")
    print(f"  - Config: {output_dir / 'config.json'}")
    print(f"  - Final model: {output_dir / 'final_model.pt'}")
    print(f"  - Best model: {output_dir / 'best_model.pt'}")
    print(f"  - History: {output_dir / 'history.json'}")
    print(f"  - Analytical: {output_dir / 'phi_analytical_coefficients.json'}")

    # Return exit code based on convergence
    sys.exit(0 if result.converged else 1)


if __name__ == '__main__':
    main()
