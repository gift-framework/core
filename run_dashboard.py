#!/usr/bin/env python
"""
Launch GIFT Framework Dashboard.

Usage:
    python run_dashboard.py
    # or
    streamlit run gift_core/dashboard.py
"""
import subprocess
import sys


def main():
    """Launch the Streamlit dashboard."""
    try:
        import streamlit
    except ImportError:
        print("Streamlit not installed. Installing required packages...")
        subprocess.check_call([
            sys.executable, "-m", "pip", "install",
            "streamlit", "plotly", "pandas"
        ])

    # Run dashboard
    subprocess.run([
        sys.executable, "-m", "streamlit", "run",
        "gift_core/dashboard.py",
        "--server.headless=true"
    ])


if __name__ == "__main__":
    main()
