#!/usr/bin/env python3
"""Numerical gate for H14M-B pole and hypothetical-zero constants.

This is a diagnostic only.  It samples

  -zeta'(sigma)/zeta(sigma) - 1/(sigma-1)

on ``1 < sigma <= 2`` (Z2), and, at initial zeta zeros ``rho = beta+i*t``,

  (-Re zeta'/zeta(sigma+i*t) + 1/(sigma-beta)) / log(|t|+2)

(Z3).  The second quantity is the normalized remainder after the complete
zero contribution has been removed; no simple-zero assumption is used in the
Lean interface that this diagnostic informs.
"""

from __future__ import annotations

import argparse
import cmath
import math


# B_2, ..., B_20.  Double precision is enough for this non-rigorous gate.
EVEN_BERNOULLI = (
    1 / 6,
    -1 / 30,
    1 / 42,
    -1 / 30,
    5 / 66,
    -691 / 2730,
    7 / 6,
    -3617 / 510,
    43867 / 798,
    -174611 / 330,
)

# Initial critical-line ordinates, used only to sample the normalization in Z3.
ZETA_ZERO_ORDINATES = (
    14.134725141734693,
    21.022039638771555,
    25.01085758014569,
    30.424876125859513,
    32.93506158773919,
    37.586178158825675,
    40.9187190121475,
    43.32707328091499,
    48.00515088116716,
    49.7738324776723,
    52.97032147771446,
    56.44624769706339,
    59.34704400260235,
    60.83177852460981,
    65.11254404808161,
    67.07981052949417,
    69.54640171117398,
    72.06715767448191,
    75.70469069908393,
    77.1448400688748,
)


def rising_and_deriv(s: complex, order: int) -> tuple[complex, complex]:
    value = 1 + 0j
    deriv = 0j
    for offset in range(order):
        deriv = deriv * (s + offset) + value
        value *= s + offset
    return value, deriv


def zeta_and_deriv(s: complex, cutoff: int = 160) -> tuple[complex, complex]:
    """Euler--Maclaurin evaluation of zeta and its s-derivative."""
    log_cutoff = math.log(cutoff)
    value = 0j
    deriv = 0j
    for n in range(1, cutoff):
        term = cmath.exp(-s * math.log(n))
        value += term
        deriv -= math.log(n) * term

    tail_power = cmath.exp((1 - s) * log_cutoff)
    value += tail_power / (s - 1)
    deriv += tail_power * (-log_cutoff / (s - 1) - 1 / (s - 1) ** 2)

    endpoint = 0.5 * cmath.exp(-s * log_cutoff)
    value += endpoint
    deriv -= log_cutoff * endpoint

    for k, bernoulli in enumerate(EVEN_BERNOULLI, start=1):
        order = 2 * k - 1
        rising, rising_deriv = rising_and_deriv(s, order)
        power = cmath.exp((-s - order) * log_cutoff)
        coefficient = bernoulli / math.factorial(2 * k)
        value += coefficient * rising * power
        deriv += coefficient * (rising_deriv - log_cutoff * rising) * power
    return value, deriv


def zeta_log_derivative(s: complex | float) -> complex:
    value, deriv = zeta_and_deriv(complex(s))
    return deriv / value


def pole_remainder(sigma: float) -> float:
    return -zeta_log_derivative(sigma).real - 1 / (sigma - 1)


def sample_z2() -> None:
    near_one = [1 + 10 ** (-k) for k in range(1, 7)]
    grid = [1 + j / 200 for j in range(1, 201)]
    samples = sorted(set(near_one + grid))
    values = [(sigma, pole_remainder(sigma)) for sigma in samples]
    sigma_max, value_max = max(values, key=lambda pair: pair[1])
    sigma_min, value_min = min(values, key=lambda pair: pair[1])
    print("Z2 pole remainder: -zeta'/zeta(sigma) - 1/(sigma-1)")
    print(f"  sampled maximum {value_max:.15g} at sigma={sigma_max:.12g}")
    print(f"  sampled minimum {value_min:.15g} at sigma={sigma_min:.12g}")
    print("  numerical candidate A = 1 has a wide margin on this grid")


def sample_z3(zero_count: int) -> None:
    deltas = [0.05, 0.1, 0.2, 0.5, 1.0]
    rows: list[tuple[float, int, complex, float, float]] = []
    for index, ordinate in enumerate(ZETA_ZERO_ORDINATES[:zero_count], start=1):
        rho = 0.5 + 1j * ordinate
        beta = rho.real
        log_height = math.log(abs(ordinate) + 2)
        for delta in deltas:
            sigma = 1 + delta / log_height
            value = -zeta_log_derivative(sigma + 1j * ordinate).real
            normalized = (value + 1 / (sigma - beta)) / log_height
            rows.append((normalized, index, rho, sigma, value))
    rows.sort(key=lambda row: row[0])
    print("\nZ3 normalized remainder after subtracting the zero contribution")
    for label, row in (("minimum", rows[0]), ("maximum", rows[-1])):
        normalized, index, rho, sigma, value = row
        print(
            f"  {label}: {normalized:.15g} at zero #{index}, "
            f"rho={rho.real:.1f}+{rho.imag:.12g}i, sigma={sigma:.12g}, "
            f"-Re(zeta'/zeta)={value:.12g}"
        )
    print("  this samples only the analytic normalization; it is not a zero-free proof")


def sample_small_height_obstruction() -> None:
    """Expose the pole obstruction in the frozen global vertical-bound field."""
    print("\nSmall-height diagonal path sigma=1+epsilon, t=epsilon")
    print("  epsilon        -Re(zeta'/zeta)       divided by log(t+2)")
    for exponent in range(1, 7):
        epsilon = 10.0 ** (-exponent)
        value = -zeta_log_derivative(1 + epsilon + 1j * epsilon).real
        normalized = value / math.log(epsilon + 2)
        print(f"  {epsilon:8.1e}   {value:20.12g}   {normalized:20.12g}")
    print("  the normalized values grow like 1/(2*epsilon*log 2)")
    print("  hence no uniform C can cover every nonzero t")


def sample_repaired_height_range() -> None:
    """Gate the repaired vertical range ``|t| >= 1, 1 < sigma <= 2``."""
    sigmas = [1 + 10.0 ** (-k) for k in range(1, 7)]
    sigmas += [1 + j / 20 for j in range(1, 21)]
    heights = [1, 1.05, 1.1, 1.25, 1.5, 2, 3, 5, 10, 25, 50, 100, 250]
    rows: list[tuple[float, float, float, float]] = []
    for sign in (-1, 1):
        for height in heights:
            t = sign * height
            denominator = math.log(abs(t) + 2)
            for sigma in sigmas:
                value = -zeta_log_derivative(sigma + 1j * t).real
                rows.append((value / denominator, sigma, t, value))
    rows.sort(key=lambda row: row[0])
    print("\nRepaired R1 range: |t| >= 1 and 1 < sigma <= 2")
    for label, row in (("minimum", rows[0]), ("maximum", rows[-1])):
        normalized, sigma, t, value = row
        print(
            f"  {label}: normalized={normalized:.15g}, sigma={sigma:.12g}, "
            f"t={t:.12g}, -Re(zeta'/zeta)={value:.12g}"
        )
    print("  sampled range is bounded; the frozen repaired API keeps C existential")


def sample_center_lower_bound() -> None:
    """Gate the standard center lower bound used in the Borel--Jensen route."""
    zeta_three_halves = zeta_and_deriv(1.5)[0].real
    zeta_three = zeta_and_deriv(3.0)[0].real
    print("\nCenter lower-bound constants at sigma0 = 3/2")
    print(f"  zeta(3/2) ~= {zeta_three_halves:.15g}")
    print(f"  2 - zeta(3/2) ~= {2 - zeta_three_halves:.15g}")
    print(f"  zeta(3) / zeta(3/2) ~= {zeta_three / zeta_three_halves:.15g}")
    print("  the naive 2 - zeta(3/2) candidate is negative")


def sample_vertical_growth_strip() -> None:
    """Gate the P2 strip growth shape ``|zeta(s)| <= C (|t| + 2)``."""
    sigmas = [-0.5, -0.25, 0.0, 0.25, 0.5, 0.75]
    sigmas += [0.9, 0.99, 1.0, 1.01, 1.1, 1.25, 1.5, 1.75, 2.0]
    heights = [1, 1.05, 1.1, 1.25, 1.5, 2, 3, 5, 10, 25, 50, 100, 250]
    rows: list[tuple[float, float, float, float]] = []
    for sign in (-1, 1):
        for height in heights:
            t = sign * height
            denominator = abs(t) + 2
            for sigma in sigmas:
                value = abs(zeta_and_deriv(sigma + 1j * t)[0])
                rows.append((value / denominator, sigma, t, value))
    rows.sort(key=lambda row: row[0])
    print("\nP2 strip growth: |zeta(sigma+i*t)| / (|t|+2)")
    for label, row in (("minimum", rows[0]), ("maximum", rows[-1])):
        normalized, sigma, t, value = row
        print(
            f"  {label}: normalized={normalized:.15g}, sigma={sigma:.12g}, "
            f"t={t:.12g}, |zeta|={value:.12g}"
        )
    print("  sampled strip is consistent with a linear vertical-growth bound")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zeros", type=int, default=20)
    args = parser.parse_args()
    sample_z2()
    sample_z3(args.zeros)
    sample_small_height_obstruction()
    sample_repaired_height_range()
    sample_center_lower_bound()
    sample_vertical_growth_strip()


if __name__ == "__main__":
    main()
