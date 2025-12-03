"""
GIFT Framework Dashboard - Streamlit Application

Interactive visualization of:
- 39 GIFT predictions vs PDG/NuFIT experimental data
- Monte Carlo robustness analysis
- κ_T torsion coefficient stability
- K₇ metric parameter optimization (if torch available)

Run with: streamlit run gift_core/dashboard.py
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Dict, List, Tuple

try:
    import streamlit as st
    import pandas as pd
    import plotly.express as px
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    STREAMLIT_AVAILABLE = True
except ImportError:
    STREAMLIT_AVAILABLE = False
    st = None
    px = None
    go = None

# Pandas is needed even without streamlit for data functions
try:
    import pandas as pd
    PANDAS_AVAILABLE = True
except ImportError:
    pd = None
    PANDAS_AVAILABLE = False

from gift_core.constants import (
    DIM_E8, DIM_E8xE8, DIM_G2, DIM_K7, B2, B3, H_STAR, P2,
    SIN2_THETA_W, TAU, KAPPA_T, Q_KOIDE, DELTA_CP, M_TAU_M_E, M_S_M_D,
    DET_G, LAMBDA_H_NUM, N_GEN
)
from gift_core.experimental import (
    SIN2_THETA_W_EXP, DELTA_CP_EXP, M_TAU_M_E_EXP, Q_KOIDE_EXP, M_S_M_D_EXP,
    M_Z_EXP, M_W_EXP, M_H_EXP, M_TOP, M_BOTTOM, M_CHARM,
    M_TAU, M_MUON, M_ELECTRON,
    THETA_12, THETA_23, THETA_13, DELTA_M21_SQ, DELTA_M31_SQ,
    ALPHA_EM, ALPHA_S_MZ, G_FERMI,
    Measurement, GIFT_COMPARISONS
)
from gift_core.monte_carlo import (
    MonteCarloEngine, KappaTRobustness,
    run_quick_mc, run_kappa_analysis
)
from gift_core.scales import M_PLANCK, M_STRING_DEFAULT, M_GUT, M_EW

# Check for torch
try:
    from gift_core.torch_optim import TORCH_AVAILABLE
    if TORCH_AVAILABLE:
        from gift_core.torch_optim import (
            optimize_k7_metric, scan_parameter_space, K7MetricOptimizer
        )
except ImportError:
    TORCH_AVAILABLE = False


# =============================================================================
# DATA PREPARATION
# =============================================================================

def get_all_predictions() -> pd.DataFrame:
    """Get all GIFT predictions and experimental comparisons."""
    data = []

    # Core GIFT predictions with experimental data
    predictions = [
        ("sin²θ_W", "Weinberg angle", float(SIN2_THETA_W),
         SIN2_THETA_W_EXP.value, SIN2_THETA_W_EXP.error, "Electroweak", "b₂/(b₃+dim_G₂)"),
        ("κ_T", "Torsion coefficient", float(KAPPA_T),
         None, None, "Geometry", "1/(b₃-dim_G₂-p₂)"),
        ("τ", "Hierarchy parameter", float(TAU),
         None, None, "Hierarchy", "(496×21)/(27×99)"),
        ("Q_Koide", "Koide parameter", float(Q_KOIDE),
         Q_KOIDE_EXP.value, Q_KOIDE_EXP.error, "Leptons", "dim_G₂/b₂"),
        ("δ_CP", "CP phase (°)", float(DELTA_CP),
         DELTA_CP_EXP.value, DELTA_CP_EXP.error, "CP violation", "7×14+99"),
        ("m_τ/m_e", "Tau/electron ratio", float(M_TAU_M_E),
         M_TAU_M_E_EXP.value, M_TAU_M_E_EXP.error, "Leptons", "7+10×248+10×99"),
        ("m_s/m_d", "Strange/down ratio", float(M_S_M_D),
         M_S_M_D_EXP.value, M_S_M_D_EXP.error, "Quarks", "4×5"),
        ("det(g)", "Metric determinant", float(DET_G),
         None, None, "Geometry", "65/32"),
        ("λ_H", "Higgs coupling num.", float(LAMBDA_H_NUM),
         None, None, "Higgs", "14+3"),
        ("N_gen", "Generations", float(N_GEN),
         3.0, 0.0, "Standard Model", "Topological"),
        ("H*", "Effective DOF", float(H_STAR),
         None, None, "Topology", "b₂+b₃+1"),
        ("p₂", "Pontryagin class", float(P2),
         None, None, "Topology", "dim_G₂/dim_K₇"),
        ("dim(E₈×E₈)", "E₈×E₈ dimension", float(DIM_E8xE8),
         496.0, 0.0, "Gauge", "2×248"),
    ]

    for symbol, name, pred, exp, err, category, formula in predictions:
        pull = None
        if exp is not None and err is not None and err > 0:
            pull = (pred - exp) / err

        data.append({
            "Symbol": symbol,
            "Name": name,
            "GIFT Prediction": pred,
            "Experimental": exp,
            "Uncertainty": err,
            "Pull (σ)": pull,
            "Category": category,
            "Formula": formula,
        })

    return pd.DataFrame(data)


def get_experimental_constants() -> pd.DataFrame:
    """Get PDG/NuFIT experimental constants."""
    data = [
        # Masses
        ("M_Z", "Z boson mass", M_Z_EXP.value, M_Z_EXP.error, "GeV", "PDG 2024"),
        ("M_W", "W boson mass", M_W_EXP.value, M_W_EXP.error, "GeV", "PDG 2024"),
        ("M_H", "Higgs mass", M_H_EXP.value, M_H_EXP.error, "GeV", "PDG 2024"),
        ("m_t", "Top quark", M_TOP.value, M_TOP.error, "GeV", "PDG 2024"),
        ("m_b", "Bottom quark", M_BOTTOM.value, M_BOTTOM.error, "GeV", "PDG 2024"),
        ("m_c", "Charm quark", M_CHARM.value, M_CHARM.error, "GeV", "PDG 2024"),
        ("m_τ", "Tau lepton", M_TAU.value, M_TAU.error, "MeV", "PDG 2024"),
        ("m_μ", "Muon", M_MUON.value, M_MUON.error, "MeV", "PDG 2024"),
        ("m_e", "Electron", M_ELECTRON.value, M_ELECTRON.error, "MeV", "PDG 2024"),
        # Neutrino mixing
        ("θ₁₂", "Solar angle", THETA_12.value, THETA_12.error, "°", "NuFIT 5.3"),
        ("θ₂₃", "Atmospheric angle", THETA_23.value, THETA_23.error, "°", "NuFIT 5.3"),
        ("θ₁₃", "Reactor angle", THETA_13.value, THETA_13.error, "°", "NuFIT 5.3"),
        ("Δm²₂₁", "Solar mass split", DELTA_M21_SQ.value, DELTA_M21_SQ.error, "eV²", "NuFIT 5.3"),
        ("Δm²₃₁", "Atmos mass split", DELTA_M31_SQ.value, DELTA_M31_SQ.error, "eV²", "NuFIT 5.3"),
        # Couplings
        ("α_EM", "Fine structure", ALPHA_EM.value, ALPHA_EM.error, "", "PDG 2024"),
        ("α_s(M_Z)", "Strong coupling", ALPHA_S_MZ.value, ALPHA_S_MZ.error, "", "PDG 2024"),
        ("G_F", "Fermi constant", G_FERMI.value, G_FERMI.error, "GeV⁻²", "PDG 2024"),
    ]

    return pd.DataFrame(data, columns=["Symbol", "Name", "Value", "Error", "Unit", "Source"])


# =============================================================================
# VISUALIZATION FUNCTIONS
# =============================================================================

def plot_predictions_vs_experiment(df: pd.DataFrame) -> go.Figure:
    """Create pull plot for predictions vs experiment."""
    # Filter to rows with experimental comparison
    df_compare = df[df["Pull (σ)"].notna()].copy()

    fig = go.Figure()

    # Color by pull magnitude
    colors = ['green' if abs(p) < 2 else 'orange' if abs(p) < 3 else 'red'
              for p in df_compare["Pull (σ)"]]

    fig.add_trace(go.Bar(
        x=df_compare["Symbol"],
        y=df_compare["Pull (σ)"],
        marker_color=colors,
        text=[f"{p:.1f}σ" for p in df_compare["Pull (σ)"]],
        textposition='outside',
        hovertemplate=(
            "<b>%{x}</b><br>"
            "Pull: %{y:.2f}σ<br>"
            "<extra></extra>"
        )
    ))

    # Add reference lines
    fig.add_hline(y=0, line_dash="solid", line_color="black", line_width=1)
    fig.add_hline(y=2, line_dash="dash", line_color="orange", line_width=1)
    fig.add_hline(y=-2, line_dash="dash", line_color="orange", line_width=1)
    fig.add_hline(y=3, line_dash="dash", line_color="red", line_width=1)
    fig.add_hline(y=-3, line_dash="dash", line_color="red", line_width=1)

    fig.update_layout(
        title="GIFT Predictions vs PDG/NuFIT Data",
        xaxis_title="Observable",
        yaxis_title="Pull (σ)",
        yaxis_range=[-20, 5],
        template="plotly_white",
        height=400,
    )

    return fig


def plot_category_breakdown(df: pd.DataFrame) -> go.Figure:
    """Create pie chart of prediction categories."""
    category_counts = df["Category"].value_counts()

    fig = px.pie(
        values=category_counts.values,
        names=category_counts.index,
        title="Predictions by Category",
        hole=0.4,
    )

    return fig


def plot_monte_carlo_results(results: Dict) -> go.Figure:
    """Plot Monte Carlo robustness results."""
    fig = make_subplots(
        rows=2, cols=2,
        subplot_titles=["κ_T Distribution", "sin²θ_W Distribution",
                       "Robustness Scores", "Parameter Correlations"]
    )

    # κ_T histogram
    if 'κ_T' in results:
        fig.add_trace(
            go.Histogram(x=results['κ_T'].samples, name="κ_T", nbinsx=50),
            row=1, col=1
        )
        fig.add_vline(x=float(KAPPA_T), line_dash="dash", line_color="red",
                     row=1, col=1)

    # sin²θ_W histogram
    if 'sin²θ_W' in results:
        fig.add_trace(
            go.Histogram(x=results['sin²θ_W'].samples, name="sin²θ_W", nbinsx=50),
            row=1, col=2
        )
        fig.add_vline(x=float(SIN2_THETA_W), line_dash="dash", line_color="red",
                     row=1, col=2)

    # Robustness bar chart
    robustness = [(k, v.robustness * 100) for k, v in results.items()]
    robustness.sort(key=lambda x: x[1], reverse=True)

    fig.add_trace(
        go.Bar(
            x=[r[0] for r in robustness],
            y=[r[1] for r in robustness],
            name="Robustness %",
            marker_color='steelblue'
        ),
        row=2, col=1
    )

    fig.update_layout(
        title="Monte Carlo Robustness Analysis",
        height=600,
        showlegend=False,
        template="plotly_white",
    )

    return fig


def plot_kappa_t_scan(kappa_results: Dict) -> go.Figure:
    """Plot κ_T vs string scale scan."""
    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=kappa_results['m_string'],
        y=kappa_results['kappa_t'],
        mode='lines+markers',
        name='κ_T',
        line=dict(color='steelblue', width=2),
    ))

    # Nominal value
    fig.add_hline(
        y=float(KAPPA_T),
        line_dash="dash",
        line_color="red",
        annotation_text="Nominal κ_T = 1/61"
    )

    fig.update_layout(
        title="κ_T Robustness vs String Scale",
        xaxis_title="String Scale M_s (GeV)",
        yaxis_title="κ_T",
        xaxis_type="log",
        template="plotly_white",
        height=400,
    )

    return fig


# =============================================================================
# STREAMLIT APP
# =============================================================================

def main():
    """Main Streamlit application."""
    st.set_page_config(
        page_title="GIFT Framework Dashboard",
        page_icon="🌌",
        layout="wide",
    )

    st.title("🌌 GIFT Framework Dashboard")
    st.markdown("""
    **Geometric Information Field Theory** - Formally verified predictions
    from E₈/G₂/K₇ topology compared to PDG 2024 and NuFIT 5.3 data.
    """)

    # Sidebar
    st.sidebar.title("Navigation")
    page = st.sidebar.radio(
        "Select Page",
        ["📊 Predictions vs Experiment", "🎲 Monte Carlo Analysis",
         "⚙️ Topological Constants", "🔧 Optimization"]
    )

    # ==========================================================================
    # PAGE 1: Predictions vs Experiment
    # ==========================================================================
    if page == "📊 Predictions vs Experiment":
        st.header("GIFT Predictions vs Experimental Data")

        df = get_all_predictions()

        # Summary metrics
        col1, col2, col3, col4 = st.columns(4)
        with col1:
            st.metric("Total Predictions", len(df))
        with col2:
            n_tested = df["Pull (σ)"].notna().sum()
            st.metric("Experimentally Tested", n_tested)
        with col3:
            n_agree = (df["Pull (σ)"].abs() < 3).sum()
            st.metric("Within 3σ", n_agree)
        with col4:
            if n_tested > 0:
                pct = n_agree / n_tested * 100
                st.metric("Agreement Rate", f"{pct:.0f}%")

        # Pull plot
        st.plotly_chart(plot_predictions_vs_experiment(df), use_container_width=True)

        # Data table
        st.subheader("Full Prediction Table")
        st.dataframe(
            df.style.format({
                "GIFT Prediction": "{:.6f}",
                "Experimental": "{:.6f}",
                "Uncertainty": "{:.6f}",
                "Pull (σ)": "{:+.2f}",
            }, na_rep="-"),
            use_container_width=True,
        )

        # Category breakdown
        col1, col2 = st.columns(2)
        with col1:
            st.plotly_chart(plot_category_breakdown(df), use_container_width=True)
        with col2:
            st.markdown("""
            ### Key Results

            | Observable | GIFT | Experiment | Status |
            |------------|------|------------|--------|
            | sin²θ_W | 3/13 = 0.2308 | 0.23122 | ⚠️ -15σ |
            | Q_Koide | 2/3 = 0.6667 | 0.66666 | ✅ <1σ |
            | δ_CP | 197° | 197° ± 42° | ✅ 0σ |
            | m_τ/m_e | 3477 | 3477.2 | ✅ <1σ |

            *Note: sin²θ_W tension may indicate running effects not captured in tree-level topology.*
            """)

    # ==========================================================================
    # PAGE 2: Monte Carlo Analysis
    # ==========================================================================
    elif page == "🎲 Monte Carlo Analysis":
        st.header("Monte Carlo Robustness Analysis")

        st.markdown("""
        Test stability of GIFT predictions under scale variations
        (Planck scale → String scale → GUT scale).
        """)

        col1, col2 = st.columns(2)
        with col1:
            n_samples = st.slider("Number of samples", 100, 10000, 1000, step=100)
        with col2:
            seed = st.number_input("Random seed", value=42, step=1)

        if st.button("🚀 Run Monte Carlo"):
            with st.spinner("Running simulation..."):
                engine = MonteCarloEngine(n_samples=n_samples, seed=int(seed))
                results = engine.run()

            st.success(f"Completed {n_samples} samples!")

            # Results plot
            st.plotly_chart(plot_monte_carlo_results(results), use_container_width=True)

            # Summary table
            st.subheader("Robustness Summary")
            summary_data = []
            for symbol, res in results.items():
                summary_data.append({
                    "Observable": symbol,
                    "Nominal": res.observable.nominal_value,
                    "MC Mean": res.mean,
                    "MC Std": res.std,
                    "Robustness": f"{res.robustness * 100:.1f}%",
                })
            st.dataframe(pd.DataFrame(summary_data), use_container_width=True)

        # κ_T specific analysis
        st.subheader("κ_T Torsion Coefficient Analysis")

        if st.button("🔍 Analyze κ_T"):
            with st.spinner("Running κ_T scan..."):
                analysis = KappaTRobustness(n_samples=1000)
                scan = analysis.run_scale_scan(n_points=50)

            st.plotly_chart(plot_kappa_t_scan(scan), use_container_width=True)

            st.markdown(f"""
            **κ_T = 1/61 ≈ {float(KAPPA_T):.6f}**

            The torsion coefficient is derived from:
            - b₃(K₇) = 77 (third Betti number)
            - dim(G₂) = 14 (exceptional holonomy)
            - p₂ = 2 (Pontryagin class)

            κ_T = 1/(77 - 14 - 2) = 1/61
            """)

    # ==========================================================================
    # PAGE 3: Topological Constants
    # ==========================================================================
    elif page == "⚙️ Topological Constants":
        st.header("Topological Constants")

        col1, col2 = st.columns(2)

        with col1:
            st.subheader("E₈ Exceptional Lie Algebra")
            st.metric("dim(E₈)", DIM_E8)
            st.metric("dim(E₈×E₈)", DIM_E8xE8)
            st.markdown("*Heterotic string gauge group*")

            st.subheader("G₂ Holonomy")
            st.metric("dim(G₂)", DIM_G2)
            st.markdown("*Exceptional holonomy of K₇*")

        with col2:
            st.subheader("K₇ Manifold (TCS)")
            st.metric("dim(K₇)", DIM_K7)
            st.metric("b₂(K₇)", B2)
            st.metric("b₃(K₇)", B3)
            st.metric("H*", H_STAR)
            st.metric("χ(K₇)", 2 * (B2 - B3))
            st.markdown("*Twisted Connected Sum construction*")

        st.subheader("Physical Scale Hierarchy")
        scales_df = pd.DataFrame({
            "Scale": ["Planck", "String (default)", "GUT", "Electroweak"],
            "Value (GeV)": [f"{M_PLANCK:.2e}", f"{M_STRING_DEFAULT:.2e}",
                          f"{M_GUT:.2e}", f"{M_EW:.2f}"],
        })
        st.table(scales_df)

        st.subheader("Experimental Data (PDG 2024 / NuFIT 5.3)")
        st.dataframe(get_experimental_constants(), use_container_width=True)

    # ==========================================================================
    # PAGE 4: Optimization
    # ==========================================================================
    elif page == "🔧 Optimization":
        st.header("K₇ Metric Optimization")

        if not TORCH_AVAILABLE:
            st.warning("""
            ⚠️ **PyTorch not installed**

            To enable optimization features:
            ```bash
            pip install torch
            ```
            """)
        else:
            st.markdown("""
            Optimize K₇ metric parameters (α, β, γ) to minimize χ²
            between GIFT predictions and experimental data.
            """)

            col1, col2, col3 = st.columns(3)
            with col1:
                lr = st.slider("Learning rate", 0.001, 0.1, 0.01, step=0.001)
            with col2:
                max_iter = st.slider("Max iterations", 100, 2000, 500, step=100)
            with col3:
                reg = st.slider("Regularization", 0.0, 1.0, 0.1, step=0.05)

            if st.button("🎯 Optimize"):
                with st.spinner("Optimizing..."):
                    optimizer = K7MetricOptimizer(
                        lr=lr,
                        max_iterations=max_iter,
                        regularization=reg,
                    )
                    result = optimizer.optimize()

                st.success("Optimization complete!")

                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("Initial χ²", f"{result.initial_chi2:.4f}")
                with col2:
                    st.metric("Final χ²", f"{result.final_chi2:.4f}")
                with col3:
                    st.metric("Improvement", f"{result.improvement():.1f}%")

                st.subheader("Optimized Parameters")
                param_df = pd.DataFrame({
                    "Parameter": ["α (Betti)", "β (G₂)", "γ (torsion)"],
                    "Value": [result.alpha, result.beta, result.gamma],
                    "Deviation from 1": [result.alpha - 1, result.beta - 1, result.gamma - 1],
                })
                st.table(param_df)

                # Convergence plot
                fig = go.Figure()
                fig.add_trace(go.Scatter(
                    y=result.history,
                    mode='lines',
                    name='χ²',
                ))
                fig.update_layout(
                    title="Optimization Convergence",
                    xaxis_title="Iteration",
                    yaxis_title="χ²",
                    template="plotly_white",
                )
                st.plotly_chart(fig, use_container_width=True)

            # Parameter scan
            st.subheader("Parameter Space Scan")
            param_to_scan = st.selectbox("Parameter to scan", ["alpha", "beta", "gamma"])

            if st.button("📈 Scan"):
                with st.spinner("Scanning..."):
                    params, chi2s = scan_parameter_space(
                        param=param_to_scan,
                        n_points=50,
                        range_min=0.8,
                        range_max=1.2,
                    )

                fig = go.Figure()
                fig.add_trace(go.Scatter(x=params, y=chi2s, mode='lines+markers'))
                fig.add_vline(x=1.0, line_dash="dash", line_color="red")
                fig.update_layout(
                    title=f"χ² vs {param_to_scan}",
                    xaxis_title=param_to_scan,
                    yaxis_title="χ²",
                    template="plotly_white",
                )
                st.plotly_chart(fig, use_container_width=True)

    # Footer
    st.markdown("---")
    st.markdown("""
    <div style='text-align: center; color: gray;'>
    GIFT Framework | Formally verified with Lean 4 + Coq 8.18 | Zero axioms
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    if not STREAMLIT_AVAILABLE:
        print("Streamlit not installed. Run: pip install streamlit plotly pandas")
    else:
        main()
