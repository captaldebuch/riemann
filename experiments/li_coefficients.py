"""
Li Coefficient Computation
==========================
Computes Li coefficients λ_n numerically to check positivity and
search for recurrence patterns.

Li's criterion: RH ↔ λ_n ≥ 0 for all n ≥ 1
λ_n = (1/(n-1)!) · [d^n/ds^n (s^(n-1) log ξ(s))]_{s=1}

The first few Li coefficients:
  λ_1 = 1 + γ/2 - log(4π)/2 ≈ 0.0230957...
  λ_2 ≈ 0.0923447...
  λ_n > 0 for small n (verified numerically)

Usage: python li_coefficients.py --n_max 30
"""

import argparse
import math
import numpy as np
from mpmath import mp, mpf, log, gamma, zeta, pi, euler

mp.dps = 50  # 50 decimal places

def li_coefficient(n: int) -> float:
    """
    Compute λ_n using the formula:
    λ_n = Σ_{ρ} [1 - (1 - 1/ρ)^n]
    summed over nontrivial zeros ρ (using known zeros numerically).

    Note: This is a simplified numerical estimate using the first K zeros.
    """
    # First nontrivial zeros (imaginary parts)
    # From standard tables — more can be loaded from LMFDB
    gamma_zeros = [
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918720, 43.327073, 48.005150, 49.773832,
        52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
        67.079810, 69.546402, 72.067158, 75.704691, 77.144840,
    ]
    total = mpf(0)
    for t in gamma_zeros:
        rho = mpf('0.5') + 1j * mpf(str(t))
        rho_conj = mpf('0.5') - 1j * mpf(str(t))
        total += 1 - (1 - 1/rho)**n
        total += 1 - (1 - 1/rho_conj)**n
    return float(total.real)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n_max", type=int, default=20)
    args = parser.parse_args()

    print(f"Li coefficients λ_n (using first 20 pairs of zeros):\n")
    coeffs = []
    for n in range(1, args.n_max + 1):
        val = li_coefficient(n)
        coeffs.append(val)
        sign = "≥0 ✓" if val >= 0 else "< 0 ✗ RH VIOLATED"
        print(f"  λ_{n:2d} = {val:+.6f}  {sign}")

    print(f"\nAll positive: {all(c >= 0 for c in coeffs)}")
    print("\nNote: uses only 20 zero pairs — not conclusive for large n.")

if __name__ == "__main__":
    main()
