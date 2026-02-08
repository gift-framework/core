"""
Geodesic solver for K7 metric — tests prime-geodesic correspondence.

Given a trained PINN model g(x) on K7, this module:
1. Computes Christoffel symbols via torch.autograd
2. Integrates the geodesic ODE: d²xᵏ/dt² = -Γᵏᵢⱼ dxⁱ/dt dxʲ/dt
3. Detects closed geodesics (periodic boundary conditions on [0, L]^7)
4. Extracts primitive geodesic lengths
5. Tests correlation with C·log(p) for primes p

Usage on A100 Colab:
    from gift_core.nn.geodesics import GeodesicSolver, prime_geodesic_test
    solver = GeodesicSolver(model, device='cuda', coord_range=10.0)
    results = prime_geodesic_test(solver, n_init=10000)
"""

import math
from typing import Optional, Tuple, List, Dict

import numpy as np

try:
    import torch
    import torch.nn as nn
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False

# First 77 primes (matching K7 b3 = 77 moduli dimensions)
PRIMES_77 = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
    127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197,
    199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
    283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
    383, 389
]


if HAS_TORCH:

    class CheckpointPINNAdapter(nn.Module):
        """
        Adapter for PINN v3.2 checkpoint (Cholesky parameterization).

        The v3.2 checkpoint uses a different architecture than GIFTNativePINN:
        - 8D input (7 coords + 1 extra), 48 Fourier frequencies
        - backbone: 96→256→256→256→128 (SiLU)
        - 3 output heads: metric (28), local/phi (35), global (42)
        - Cholesky: g = (L0 + delta_L) @ (L0 + delta_L)^T

        This adapter loads the raw state_dict and exposes .metric(x)
        compatible with the GeodesicSolver.

        Usage:
            state_dict = torch.load('k7_pinn_step5_final.pt', map_location='cpu')
            model = CheckpointPINNAdapter(state_dict)
            solver = GeodesicSolver(model, device='cpu')
        """

        def __init__(self, state_dict: dict, pad_8d: bool = True):
            super().__init__()
            self.pad_8d = pad_8d
            self.input_dim = state_dict['fourier.B'].shape[1]  # 8

            # Fourier features
            B = state_dict['fourier.B']
            self.register_buffer('fourier_B', B.clone())
            self.fourier_out = 2 * B.shape[0]

            # Backbone
            self.backbone = nn.Sequential(
                nn.Linear(self.fourier_out, 256),
                nn.SiLU(),
                nn.Linear(256, 256),
                nn.SiLU(),
                nn.Linear(256, 256),
                nn.SiLU(),
                nn.Linear(256, 128),
                nn.SiLU(),
            )

            # Heads
            self.metric_head = nn.Linear(128, 28)

            # Buffers
            self.register_buffer('L0_flat', state_dict['L0_flat'].clone())
            self.register_buffer('tril_row', state_dict['tril_row'].clone())
            self.register_buffer('tril_col', state_dict['tril_col'].clone())

            # Match checkpoint dtype and load weights
            self.to(state_dict['L0_flat'].dtype)
            self.load_state_dict(state_dict, strict=False)

        def _fourier(self, x: torch.Tensor) -> torch.Tensor:
            proj = 2 * math.pi * torch.matmul(x, self.fourier_B.T)
            return torch.cat([torch.cos(proj), torch.sin(proj)], dim=-1)

        def _pad_input(self, x: torch.Tensor) -> torch.Tensor:
            """Pad 7D input to 8D if needed (set 8th coord to 0)."""
            if self.pad_8d and x.shape[-1] == 7:
                zeros = torch.zeros(*x.shape[:-1], 1,
                                    device=x.device, dtype=x.dtype)
                x = torch.cat([x, zeros], dim=-1)
            return x

        def metric(self, x: torch.Tensor) -> torch.Tensor:
            """
            Compute metric g(x) = L(x) @ L(x)^T.

            Args:
                x: (N, 7) or (N, 8) coordinates
            Returns:
                g: (N, 7, 7) metric tensor, guaranteed positive definite
            """
            x = self._pad_input(x)
            N = x.shape[0]
            h = self._fourier(x)
            h = self.backbone(h)
            delta_L = self.metric_head(h)  # (N, 28)

            # Build lower triangular matrix
            L = torch.zeros(N, 7, 7, device=x.device, dtype=x.dtype)
            for i in range(28):
                L[:, self.tril_row[i], self.tril_col[i]] = (
                    self.L0_flat[i] + delta_L[:, i]
                )

            # G = L @ L^T (guaranteed positive definite)
            return torch.bmm(L, L.transpose(1, 2))

    class GeodesicSolver:
        """
        Geodesic ODE solver on K7 using a trained PINN metric.

        The metric g(x) comes from the PINN model. Christoffel symbols
        are computed via torch.autograd differentiation of g.

        Args:
            model: Trained PINN with a .metric(x) method returning (N, 7, 7)
            device: 'cuda' or 'cpu'
            coord_range: Coordinate domain is [0, coord_range]^7
            use_periodic_bc: Wrap coordinates modulo coord_range
        """

        def __init__(self, model: nn.Module, device: str = 'cuda',
                     coord_range: float = 10.0, use_periodic_bc: bool = True):
            self.model = model
            self.device = torch.device(device)
            self.model.to(self.device)
            self.model.eval()
            self.L = coord_range
            self.periodic = use_periodic_bc
            self.dim = 7

        def _wrap(self, x: torch.Tensor) -> torch.Tensor:
            """Apply periodic boundary conditions."""
            if self.periodic:
                return x % self.L
            return x

        def metric_at(self, x: torch.Tensor) -> torch.Tensor:
            """
            Evaluate metric at point(s) x.

            Args:
                x: (N, 7) or (7,) coordinates
            Returns:
                g: (N, 7, 7) metric tensor
            """
            if x.dim() == 1:
                x = x.unsqueeze(0)
            x = self._wrap(x)
            with torch.no_grad():
                g = self.model.metric(x)
            return g

        def christoffel(self, x: torch.Tensor) -> torch.Tensor:
            """
            Compute Christoffel symbols Γᵏᵢⱼ at point x via autograd.

            Γᵏᵢⱼ = (1/2) gᵏˡ (∂gₗⱼ/∂xⁱ + ∂gₗᵢ/∂xʲ - ∂gᵢⱼ/∂xˡ)

            Args:
                x: (7,) single point (requires_grad will be set)
            Returns:
                gamma: (7, 7, 7) tensor where gamma[k,i,j] = Γᵏᵢⱼ
            """
            x = self._wrap(x.detach().clone())
            x.requires_grad_(True)

            # Get metric (1, 7, 7)
            g = self.model.metric(x.unsqueeze(0)).squeeze(0)  # (7, 7)

            # Compute ∂g_ab/∂x^c for all a,b,c
            dg = torch.zeros(self.dim, self.dim, self.dim,
                             device=self.device, dtype=x.dtype)

            for a in range(self.dim):
                for b in range(a, self.dim):
                    grad = torch.autograd.grad(
                        g[a, b], x, create_graph=False, retain_graph=True
                    )[0]  # (7,)
                    dg[a, b, :] = grad
                    if a != b:
                        dg[b, a, :] = grad  # symmetry of g

            # Metric inverse
            g_inv = torch.linalg.inv(g)  # (7, 7)

            # Γᵏᵢⱼ = (1/2) gᵏˡ (∂gₗⱼ/∂xⁱ + ∂gₗᵢ/∂xʲ - ∂gᵢⱼ/∂xˡ)
            # dg[a,b,c] = ∂g_ab/∂x^c
            gamma = torch.zeros(self.dim, self.dim, self.dim,
                                device=self.device, dtype=x.dtype)

            for k in range(self.dim):
                for i in range(self.dim):
                    for j in range(i, self.dim):
                        val = 0.0
                        for l in range(self.dim):
                            val += g_inv[k, l] * (
                                dg[l, j, i] + dg[l, i, j] - dg[i, j, l]
                            )
                        gamma[k, i, j] = 0.5 * val
                        if i != j:
                            gamma[k, j, i] = gamma[k, i, j]  # symmetry in ij

            return gamma.detach()

        def christoffel_fd(self, x: torch.Tensor, eps: float = 1e-4) -> torch.Tensor:
            """
            Christoffel symbols via finite differences (faster, less accurate).
            """
            x = self._wrap(x.detach())
            g0 = self.metric_at(x).squeeze(0)  # (7, 7)
            g_inv = torch.linalg.inv(g0)

            # ∂g_ab/∂x^c via central differences
            dg = torch.zeros(self.dim, self.dim, self.dim,
                             device=self.device, dtype=x.dtype)

            for c in range(self.dim):
                dx = torch.zeros(self.dim, device=self.device, dtype=x.dtype)
                dx[c] = eps
                g_plus = self.metric_at(x + dx).squeeze(0)
                g_minus = self.metric_at(x - dx).squeeze(0)
                dg[:, :, c] = (g_plus - g_minus) / (2 * eps)

            gamma = torch.zeros(self.dim, self.dim, self.dim,
                                device=self.device, dtype=x.dtype)
            for k in range(self.dim):
                for i in range(self.dim):
                    for j in range(i, self.dim):
                        val = 0.0
                        for l in range(self.dim):
                            val += g_inv[k, l] * (
                                dg[l, j, i] + dg[l, i, j] - dg[i, j, l]
                            )
                        gamma[k, i, j] = 0.5 * val
                        if i != j:
                            gamma[k, j, i] = gamma[k, i, j]
            return gamma

        def geodesic_acceleration(self, x: torch.Tensor, v: torch.Tensor,
                                  use_fd: bool = True) -> torch.Tensor:
            """
            Compute geodesic acceleration: a^k = -Γ^k_ij v^i v^j

            Args:
                x: (7,) position
                v: (7,) velocity
                use_fd: use finite differences (True) or autograd (False)
            Returns:
                a: (7,) acceleration
            """
            if use_fd:
                gamma = self.christoffel_fd(x)
            else:
                gamma = self.christoffel(x)

            # a^k = -Γ^k_ij v^i v^j
            a = -torch.einsum('kij,i,j->k', gamma, v, v)
            return a

        def integrate_geodesic(self, x0: torch.Tensor, v0: torch.Tensor,
                               dt: float = 0.01, n_steps: int = 1000,
                               use_fd: bool = True) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
            """
            Integrate geodesic from (x0, v0) using Störmer-Verlet (symplectic).

            Args:
                x0: (7,) initial position
                v0: (7,) initial velocity (unit speed recommended)
                dt: time step
                n_steps: number of steps
                use_fd: finite differences for Christoffel
            Returns:
                xs: (n_steps+1, 7) positions along geodesic
                vs: (n_steps+1, 7) velocities along geodesic
                lengths: (n_steps+1,) cumulative arc length
            """
            xs = torch.zeros(n_steps + 1, self.dim, device=self.device)
            vs = torch.zeros(n_steps + 1, self.dim, device=self.device)
            lengths = torch.zeros(n_steps + 1, device=self.device)

            xs[0] = x0.clone()
            vs[0] = v0.clone()

            x = x0.clone()
            v = v0.clone()
            arc = 0.0

            for step in range(n_steps):
                # Störmer-Verlet (velocity Verlet)
                a = self.geodesic_acceleration(x, v, use_fd=use_fd)
                v_half = v + 0.5 * dt * a
                x_new = self._wrap(x + dt * v_half)
                a_new = self.geodesic_acceleration(x_new, v_half, use_fd=use_fd)
                v_new = v_half + 0.5 * dt * a_new

                # Arc length increment: ds = sqrt(g_ij dx^i dx^j)
                dx = x_new - x
                g = self.metric_at(x).squeeze(0)
                ds = torch.sqrt(torch.einsum('i,ij,j->', dx, g, dx).clamp(min=1e-20))
                arc += ds.item()

                x = x_new
                v = v_new
                xs[step + 1] = x
                vs[step + 1] = v
                lengths[step + 1] = arc

            return xs, vs, lengths

        def find_closed_geodesic(self, x0: torch.Tensor, v0: torch.Tensor,
                                 dt: float = 0.005, max_steps: int = 5000,
                                 closure_tol: float = 0.1,
                                 min_length: float = 0.5,
                                 use_fd: bool = True) -> Optional[Dict]:
            """
            Integrate a geodesic and check if it closes.

            Returns:
                dict with keys: 'length', 'x0', 'v0', 'closure_error', 'n_steps'
                or None if no closure detected.
            """
            x = x0.clone()
            v = v0.clone()
            arc = 0.0
            x_start = x0.clone()

            for step in range(max_steps):
                a = self.geodesic_acceleration(x, v, use_fd=use_fd)
                v_half = v + 0.5 * dt * a
                x_new = self._wrap(x + dt * v_half)
                a_new = self.geodesic_acceleration(x_new, v_half, use_fd=use_fd)
                v_new = v_half + 0.5 * dt * a_new

                dx = x_new - x
                g = self.metric_at(x).squeeze(0)
                ds = torch.sqrt(torch.einsum('i,ij,j->', dx, g, dx).clamp(min=1e-20))
                arc += ds.item()

                x = x_new
                v = v_new

                # Check closure (with periodic BCs)
                if arc > min_length:
                    if self.periodic:
                        diff = (x - x_start) % self.L
                        diff = torch.min(diff, self.L - diff)
                    else:
                        diff = x - x_start
                    closure_err = torch.norm(diff).item()

                    if closure_err < closure_tol:
                        return {
                            'length': arc,
                            'x0': x0.cpu().numpy(),
                            'v0': v0.cpu().numpy(),
                            'closure_error': closure_err,
                            'n_steps': step + 1,
                        }

            return None

        def normalize_velocity(self, x: torch.Tensor, v: torch.Tensor) -> torch.Tensor:
            """Normalize velocity to unit speed: g_ij v^i v^j = 1."""
            g = self.metric_at(x).squeeze(0)
            norm_sq = torch.einsum('i,ij,j->', v, g, v)
            return v / torch.sqrt(norm_sq.clamp(min=1e-20))

        def search_closed_geodesics(self, n_init: int = 1000,
                                    dt: float = 0.005, max_steps: int = 5000,
                                    closure_tol: float = 0.15,
                                    min_length: float = 0.5,
                                    seed: int = 42,
                                    verbose: bool = True) -> List[Dict]:
            """
            Monte Carlo search for closed geodesics.

            Samples random initial conditions and integrates geodesics,
            looking for those that return close to their starting point.

            Args:
                n_init: number of random initial conditions
                dt: integration time step
                max_steps: max steps per geodesic
                closure_tol: distance threshold for closure detection
                min_length: minimum geodesic length to consider
                seed: random seed
                verbose: print progress

            Returns:
                List of dicts with closed geodesic data
            """
            torch.manual_seed(seed)
            found = []

            for i in range(n_init):
                # Random starting point on K7
                x0 = torch.rand(self.dim, device=self.device) * self.L
                # Random direction
                v0 = torch.randn(self.dim, device=self.device)
                v0 = self.normalize_velocity(x0, v0)

                result = self.find_closed_geodesic(
                    x0, v0, dt=dt, max_steps=max_steps,
                    closure_tol=closure_tol, min_length=min_length
                )

                if result is not None:
                    found.append(result)
                    if verbose:
                        print(f"  [{i+1}/{n_init}] Closed geodesic: "
                              f"length={result['length']:.4f}, "
                              f"closure_err={result['closure_error']:.4f}")

                if verbose and (i + 1) % 100 == 0:
                    print(f"  Progress: {i+1}/{n_init}, found {len(found)} closed geodesics")

            return found


    def extract_primitive_lengths(geodesics: List[Dict],
                                 tolerance: float = 0.05) -> np.ndarray:
        """
        Extract primitive geodesic lengths (remove multiples).

        A geodesic of length L is a k-fold cover of a primitive geodesic
        of length L/k if L/k is also in the spectrum.

        Args:
            geodesics: list of dicts from search_closed_geodesics
            tolerance: relative tolerance for identifying multiples
        Returns:
            primitive_lengths: sorted array of primitive lengths
        """
        if not geodesics:
            return np.array([])

        lengths = sorted(set(round(g['length'], 3) for g in geodesics))
        lengths = np.array(lengths)

        primitive = []
        for l in lengths:
            is_multiple = False
            for p in primitive:
                ratio = l / p
                k = round(ratio)
                if k >= 2 and abs(ratio - k) / k < tolerance:
                    is_multiple = True
                    break
            if not is_multiple:
                primitive.append(l)

        return np.array(primitive)


    def prime_geodesic_test(solver: 'GeodesicSolver',
                           n_init: int = 5000,
                           dt: float = 0.005,
                           max_steps: int = 5000,
                           closure_tol: float = 0.15,
                           verbose: bool = True) -> Dict:
        """
        Full test of the prime-geodesic correspondence on K7.

        Hypothesis: primitive closed geodesic lengths l_p = C * log(p)
        for primes p = 2, 3, 5, 7, ...

        Args:
            solver: GeodesicSolver instance with loaded PINN
            n_init: number of random initial conditions to try
            dt: integration time step
            max_steps: max steps per geodesic
            closure_tol: closure detection tolerance
            verbose: print progress

        Returns:
            dict with:
                'geodesics': list of all found closed geodesics
                'primitive_lengths': array of primitive lengths
                'log_primes': log of first N primes
                'best_C': best-fit constant C in l = C*log(p)
                'correlation': Pearson correlation
                'residuals': deviations from C*log(p)
        """
        if verbose:
            print("=" * 60)
            print("PRIME-GEODESIC CORRESPONDENCE TEST ON K7")
            print("=" * 60)
            print(f"Searching {n_init} random geodesics...")

        # Step 1: Find closed geodesics
        geodesics = solver.search_closed_geodesics(
            n_init=n_init, dt=dt, max_steps=max_steps,
            closure_tol=closure_tol, verbose=verbose
        )

        if verbose:
            print(f"\nFound {len(geodesics)} closed geodesics total.")

        if len(geodesics) < 3:
            print("WARNING: Too few closed geodesics found. "
                  "Try increasing n_init or max_steps.")
            return {
                'geodesics': geodesics,
                'primitive_lengths': np.array([]),
                'log_primes': np.log(PRIMES_77[:10]),
                'best_C': float('nan'),
                'correlation': float('nan'),
                'residuals': np.array([]),
            }

        # Step 2: Extract primitive lengths
        primitive = extract_primitive_lengths(geodesics)
        if verbose:
            print(f"Primitive geodesic lengths ({len(primitive)}):")
            for i, l in enumerate(primitive[:20]):
                print(f"  l_{i+1} = {l:.4f}")

        # Step 3: Match with log(primes)
        n_match = min(len(primitive), len(PRIMES_77))
        log_p = np.log(np.array(PRIMES_77[:n_match], dtype=np.float64))
        lengths_matched = primitive[:n_match]

        # Best-fit C via least squares: l = C * log(p)
        # C = (l · log_p) / (log_p · log_p)
        best_C = np.dot(lengths_matched, log_p) / np.dot(log_p, log_p)

        # Pearson correlation
        if n_match >= 3:
            correlation = np.corrcoef(lengths_matched, log_p)[0, 1]
        else:
            correlation = float('nan')

        # Residuals
        predicted = best_C * log_p
        residuals = lengths_matched - predicted
        rms_residual = np.sqrt(np.mean(residuals ** 2))
        relative_error = rms_residual / np.mean(lengths_matched) if np.mean(lengths_matched) > 0 else float('nan')

        if verbose:
            print(f"\n{'=' * 60}")
            print(f"RESULTS: PRIME-GEODESIC CORRESPONDENCE")
            print(f"{'=' * 60}")
            print(f"Primitive geodesics found: {len(primitive)}")
            print(f"Matched with primes:       {n_match}")
            print(f"Best-fit C:                {best_C:.6f}")
            print(f"Expected C ~ pi*sqrt(2):   {math.pi * math.sqrt(2):.6f}")
            print(f"Expected C ~ 2*pi/sqrt(det):{2*math.pi/math.sqrt(65/32):.6f}")
            print(f"Pearson correlation:        {correlation:.6f}")
            print(f"RMS residual:              {rms_residual:.6f}")
            print(f"Relative error:            {relative_error:.4%}")
            print()

            if n_match >= 5:
                print("First 10 comparisons:")
                print(f"  {'Prime':>6} {'log(p)':>8} {'l_prim':>8} {'C*log(p)':>8} {'error':>8}")
                for i in range(min(10, n_match)):
                    p = PRIMES_77[i]
                    print(f"  {p:>6d} {log_p[i]:>8.4f} {lengths_matched[i]:>8.4f} "
                          f"{predicted[i]:>8.4f} {residuals[i]:>+8.4f}")

            print(f"\nVERDICT: ", end="")
            if correlation > 0.99:
                print("STRONG correlation with log(primes)!")
            elif correlation > 0.95:
                print("Good correlation with log(primes).")
            elif correlation > 0.80:
                print("Moderate correlation — suggestive but not conclusive.")
            else:
                print("Weak correlation — hypothesis not supported.")

        return {
            'geodesics': geodesics,
            'primitive_lengths': primitive,
            'log_primes': log_p,
            'best_C': best_C,
            'correlation': correlation,
            'rms_residual': rms_residual,
            'relative_error': relative_error,
            'residuals': residuals,
            'n_matched': n_match,
        }


    def quick_test(model: nn.Module, device: str = 'cuda',
                   n_init: int = 500) -> Dict:
        """
        Quick sanity check — run a small geodesic search.

        Usage:
            from gift_core.nn.geodesics import quick_test
            results = quick_test(model, device='cuda', n_init=500)
        """
        solver = GeodesicSolver(model, device=device)
        return prime_geodesic_test(solver, n_init=n_init, verbose=True)
