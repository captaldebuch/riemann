"""
Weil Kernel Search
==================
Searches for test functions φ with strong positivity properties
for the Weil explicit formula.

Goal: find a family of kernels where positivity becomes automatic,
yielding a new sufficient condition for RH.

DISCOVERY TARGET:
  ∃ K : KernelFamily, KernelDominatesAllTests K → WeilPositivity

Usage: python weil_kernel_search.py
"""

import numpy as np
from scipy.fft import fft, fftfreq

def gaussian_kernel(sigma: float, n_points: int = 1024):
    """Gaussian φ(x) = exp(-x²/2σ²) — Fourier-positive."""
    xs = np.linspace(-10, 10, n_points)
    phi = np.exp(-xs**2 / (2 * sigma**2))
    phi_hat = np.abs(fft(phi))
    return xs, phi, phi_hat

def check_fourier_positivity(phi_hat: np.ndarray, tol: float = 1e-10) -> bool:
    """Check if Fourier transform is non-negative."""
    return bool(np.all(phi_hat.real >= -tol))

def weil_prime_side(phi: np.ndarray, xs: np.ndarray, primes: list[int]) -> float:
    """
    Approximate prime-side contribution to Weil formula:
    Σ_p Σ_k (log p / p^{k/2}) φ(k log p)
    """
    dx = xs[1] - xs[0]
    total = 0.0
    for p in primes:
        for k in range(1, 5):
            x_val = k * np.log(p)
            if xs[0] <= x_val <= xs[-1]:
                idx = np.argmin(np.abs(xs - x_val))
                total += (np.log(p) / p**(k/2)) * phi[idx]
    return total

def main():
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

    print("Weil kernel candidates:\n")
    for sigma in [0.5, 1.0, 2.0, 5.0]:
        xs, phi, phi_hat = gaussian_kernel(sigma)
        fourier_pos = check_fourier_positivity(phi_hat)
        prime_contrib = weil_prime_side(phi, xs, primes)
        print(f"  Gaussian σ={sigma:4.1f}: Fourier-positive={fourier_pos}, "
              f"prime-side={prime_contrib:.4f}")

    print("\nNote: full Weil formula requires zero-side contributions.")
    print("NEXT STEP: add zero-side terms and search for dominant kernel family.")

if __name__ == "__main__":
    main()
