#!/usr/bin/env python3
"""Exact/numerical sanity checks for the quantitative H14 Axer step.

This is diagnostic only.  It checks the two finite identities exactly and
measures the proposed exponential majorant at the requested cutoffs.
"""

from __future__ import annotations

from fractions import Fraction
from math import exp, floor, fsum, log, sqrt


MAX_N = 1_000_000
SAMPLES = (1_000, 10_000, 100_000, 1_000_000)
A = 0.5
C_EXPONENT = A / 4


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


if __name__ == "__main__":
    main()
