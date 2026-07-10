#!/usr/bin/env python3
"""Exact/numerical sanity checks for the quantitative H14 Axer and zeta steps.

This is diagnostic only.  It checks the two finite identities exactly and
measures the proposed exponential majorant at the requested cutoffs.  It also
checks the sign and normalization in

    sum mu(n) log(n) / n**s = zeta'(s) / zeta(s)**2

and the limiting value -1 as s tends to 1 from the right.
"""

from __future__ import annotations

from fractions import Fraction
from math import exp, floor, fsum, log, sqrt


MAX_N = 1_000_000
SAMPLES = (1_000, 10_000, 100_000, 1_000_000)
A = 0.5
C_EXPONENT = A / 4


def zeta_and_deriv_euler_maclaurin(s: float, cutoff: int) -> tuple[float, float]:
    """Return zeta(s), zeta'(s) using four Euler--Maclaurin tail terms."""
    log_cutoff = log(cutoff)
    zeta_head = fsum(n ** (-s) for n in range(1, cutoff))
    deriv_head = -fsum(log(n) * n ** (-s) for n in range(1, cutoff))

    tail0 = cutoff ** (1 - s) / (s - 1)
    tail1 = 0.5 * cutoff ** (-s)
    tail2 = (s / 12) * cutoff ** (-s - 1)
    poly = s * (s + 1) * (s + 2)
    tail4 = -(poly / 720) * cutoff ** (-s - 3)

    deriv_tail0 = tail0 * (-log_cutoff - 1 / (s - 1))
    deriv_tail1 = -log_cutoff * tail1
    deriv_tail2 = (1 / 12 - s * log_cutoff / 12) * cutoff ** (-s - 1)
    poly_deriv = 3 * s * s + 6 * s + 2
    deriv_tail4 = (poly * log_cutoff - poly_deriv) / 720 * cutoff ** (-s - 3)
    return (
        zeta_head + tail0 + tail1 + tail2 + tail4,
        deriv_head + deriv_tail0 + deriv_tail1 + deriv_tail2 + deriv_tail4,
    )


def mobius_sieve(limit: int) -> list[int]:
    mu = [0] * (limit + 1)
    mu[1] = 1
    primes: list[int] = []
    composite = [False] * (limit + 1)
    for n in range(2, limit + 1):
        if not composite[n]:
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if n * p > limit:
                break
            composite[n * p] = True
            if n % p == 0:
                mu[n * p] = 0
                break
            mu[n * p] = -mu[n]
    return mu


def main() -> None:
    mu = mobius_sieve(MAX_N)
    mertens = [0] * (MAX_N + 1)
    for n in range(1, MAX_N + 1):
        mertens[n] = mertens[n - 1] + mu[n]

    empirical_c = max(
        abs(mertens[n]) / (n * exp(-A * sqrt(log(n))))
        for n in range(2, MAX_N + 1)
    )
    print(f"chosen a={A}, c'={C_EXPONENT}, empirical C={empirical_c:.9g}")

    for n in SAMPLES:
        hyperbola = sum(mu[k] * (n // k) for k in range(1, n + 1))
        assert hyperbola == 1

        # Check the exact termwise floor/fract decomposition without building
        # one enormous common denominator at N = 10^6.
        assert all(
            n * Fraction(mu[k], k)
            == mu[k] * (n // k) + mu[k] * Fraction(n % k, k)
            for k in range(1, n + 1)
        )
        fract_sum = fsum(mu[k] * (n % k) / k for k in range(1, n + 1))

        t = exp((A / 4) * sqrt(log(n)))
        cutoff = floor(n / t)
        head = fsum(mu[k] * (n % k) / k for k in range(1, cutoff + 1))
        tail = fract_sum - head
        scale = n * exp(-C_EXPONENT * sqrt(log(n)))
        ratio = abs(fract_sum) / scale
        print(
            f"N={n:7d} A1={hyperbola} A2=exact K={cutoff:7d} "
            f"head={float(head): .6g} tail={float(tail): .6g} "
            f"|fract|/(N exp(-c' sqrt(log N)))={ratio:.6g}"
        )

    boundary_partial = fsum(mu[n] * log(n) / n for n in range(1, MAX_N + 1))
    print(f"boundary partial at N={MAX_N}: {boundary_partial:+.12f}")
    for sigma in (2.0, 1.5, 1.2, 1.1, 1.05, 1.02):
        lhs = fsum(mu[n] * log(n) / n**sigma for n in range(1, MAX_N + 1))
        zeta, zeta_deriv = zeta_and_deriv_euler_maclaurin(sigma, 200_000)
        rhs = zeta_deriv / zeta**2
        print(
            f"sigma={sigma:4.2f} Lseries={lhs:+.12f} "
            f"zeta'/zeta^2={rhs:+.12f} error={lhs-rhs:+.3e}"
        )


if __name__ == "__main__":
    main()
