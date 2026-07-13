#!/usr/bin/env python3
"""Numerical gate for the H15 norm residual from classical Mertens decay.

BBLS Proposition 48 rewrites the symmetric cotangent contribution as

    -2 * sum_{m >= 1} (1/m) * sum_h c_N(h)/h
         * sum_k c_N(k) B1(m*h/k).

This script checks that normalization against the finite Vasyunin formula and
then decomposes the centered package into the two cancellations that any proof
must preserve:

    Q_N = logRatio_N + cotangent_N - 1,
    D_N = Q_N + 2 * (explicitLinearMobiusSum_N + 1).

Thus ``logRatio_N`` cancels the order-one cotangent term around the main term
``1``, and the residual ``Q_N`` is paired with the doubled linear centering.
The table reports both pairings before probing the actual inner sum

    I_N(A) = sum_{k <= N} c_N(k) B1(A/k),  A = m*h,

at N = 100, 300, 1000, 3000.  For integral A it also checks the exact finite
decomposition

    I_N(A) = sum_k c_N(k) {A/k} - (1/2) sum_k c_N(k)
             + (1/2) sum_{k|A} c_N(k).

The diagnostic is deliberately a gate, not evidence for a Lean theorem.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np

from phase15_h15_finish_diagnostics import (
    EULER_GAMMA,
    LOG_TWO_PI_MINUS_GAMMA,
    mobius_sieve,
    vasyunin_cotangent_matrix,
)


DEFAULT_NS = (100, 300, 1000, 3000)


def bernoulli_b1_integer_ratio(a: np.ndarray | int, k: np.ndarray) -> np.ndarray:
    """Dedekind-sawtooth B1(a/k), exactly at the integer/rational level."""
    remainder = np.remainder(a, k)
    return np.where(remainder == 0, 0.0, remainder / k - 0.5)


def cutoff_coefficients(n: int, mu: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    k_int = np.arange(1, n + 1, dtype=np.int64)
    k = k_int.astype(np.float64)
    c = -mu[1 : n + 1].astype(np.float64) * (1.0 - k / (n + 1.0))
    return k_int, c


def inner_sum(a: int, k: np.ndarray, c: np.ndarray) -> float:
    return float(c @ bernoulli_b1_integer_ratio(a, k))


def inner_decomposition(a: int, k: np.ndarray, c: np.ndarray) -> tuple[float, float]:
    remainder = np.remainder(a, k)
    fractional = remainder / k
    divisor = remainder == 0
    rhs = float(c @ fractional - 0.5 * c.sum() + 0.5 * c[divisor].sum())
    return inner_sum(a, k, c), rhs


@dataclass(frozen=True)
class InnerProbe:
    n: int
    label: str
    a: int
    value: float
    decomposition_error: float


def deterministic_a_values(n: int) -> tuple[tuple[str, int], ...]:
    return (
        ("A=1", 1),
        ("A=floor(N/2)", max(1, n // 2)),
        ("A=N", n),
        ("A=N^2/4", max(1, n * n // 4)),
        ("A=N^2", n * n),
        ("A=2N^2+1", 2 * n * n + 1),
    )


def sampled_max_probe(n: int, k: np.ndarray, c: np.ndarray, samples: int) -> InnerProbe:
    rng = np.random.default_rng(15015 + n)
    values = rng.integers(1, 2 * n * n + 2, size=samples, dtype=np.int64)
    remainders = np.remainder(values[:, None], k[None, :])
    b1 = np.where(remainders == 0, 0.0, remainders / k[None, :] - 0.5)
    sums = b1 @ c
    index = int(np.argmax(np.abs(sums)))
    a = int(values[index])
    lhs, rhs = inner_decomposition(a, k, c)
    return InnerProbe(n, f"sample-max/{samples}", a, lhs, lhs - rhs)


def collect_inner_probes(ns: tuple[int, ...], samples: int) -> list[InnerProbe]:
    mu = mobius_sieve(max(ns))
    result: list[InnerProbe] = []
    for n in ns:
        k, c = cutoff_coefficients(n, mu)
        for label, a in deterministic_a_values(n):
            lhs, rhs = inner_decomposition(a, k, c)
            result.append(InnerProbe(n, label, a, lhs, lhs - rhs))
        result.append(sampled_max_probe(n, k, c, samples))
    return result


def cotangent_component(n: int, mu: np.ndarray) -> float:
    k, c = cutoff_coefficients(n, mu)
    v = vasyunin_cotangent_matrix(n, progress=False)
    h_float = k.astype(np.float64)[:, None]
    k_float = k.astype(np.float64)[None, :]
    cot_kernel = -math.pi / (2.0 * h_float * k_float) * (v + v.T)
    return float(np.sum(c[:, None] * c[None, :] * cot_kernel))


def centered_package(n: int, mu: np.ndarray) -> tuple[float, ...]:
    """Return the exact finite components in the proposed frozen bound."""
    k_int, c = cutoff_coefficients(n, mu)
    k = k_int.astype(np.float64)
    h = k[:, None]
    kk = k[None, :]
    coeff = c[:, None] * c[None, :]
    v = vasyunin_cotangent_matrix(n, progress=False)
    cot = float(np.sum(coeff * (-math.pi / (2.0 * h * kk) * (v + v.T))))
    logratio_kernel = (kk - h) / (2.0 * h * kk) * np.log(h / kk)
    logratio = float(np.sum(coeff * logratio_kernel))
    sum_c_over_h = float(np.sum(c / k))
    sum_c = float(np.sum(c))
    loggamma = LOG_TWO_PI_MINUS_GAMMA * sum_c_over_h * sum_c
    chi_kernel = (np.log(k) + 1.0 - EULER_GAMMA) / k
    explicit_linear = float(np.sum(-c * chi_kernel))
    defect_minus_loggamma = logratio + cot - 1.0 + 2.0 * (explicit_linear + 1.0)
    package = abs(loggamma) + abs(defect_minus_loggamma)
    return loggamma, logratio, cot, explicit_linear, defect_minus_loggamma, package


def print_smooth_product_components(ns: tuple[int, ...]) -> None:
    """Probe the two linear factors in the separately absolute log-gamma term."""
    mu = mobius_sieve(max(ns))
    print("\nSmooth log-gamma product factors (no cotangent table required)")
    print(
        "N        sum(c/h)          sum(c)       loggamma    "
        "|loggamma|*log^2   N*|loggamma|"
    )
    for n in ns:
        k_int, c = cutoff_coefficients(n, mu)
        k = k_int.astype(np.float64)
        sum_c_over_h = float(np.sum(c / k))
        sum_c = float(np.sum(c))
        loggamma = LOG_TWO_PI_MINUS_GAMMA * sum_c_over_h * sum_c
        print(
            f"{n:7d}  {sum_c_over_h:+16.9e}  {sum_c:+12.6f}  "
            f"{loggamma:+12.7e}  "
            f"{abs(loggamma)*math.log(n+2.0)**2:18.9e}  "
            f"{n*abs(loggamma):14.7f}"
        )


def print_centered_package(ns: tuple[int, ...]) -> None:
    mu = mobius_sieve(max(ns))
    rows = [(n, centered_package(n, mu)) for n in ns]
    print("\nExact centered correlation package")
    print(
        "N      loggamma      logratio      cotangent       Q=R+C-1   "
        "2(linear+1)       D=Q+2L      package*log^2"
    )
    for n, components in rows:
        loggamma, logratio, cot, linear, corrected, package = components
        logn = math.log(n + 2.0)
        quadratic_pair = logratio + cot - 1.0
        linear_center = 2.0 * (linear + 1.0)
        print(
            f"{n:3d}  {loggamma:+12.7f}  {logratio:+12.7f}  {cot:+12.7f}  "
            f"{quadratic_pair:+12.7f}  {linear_center:+12.7f}  "
            f"{corrected:+12.7f}  "
            f"{package*logn*logn:13.7f}"
        )

    print("\nCancellation and rate diagnostics")
    print(
        "N      Q*log^2      2L*log^2       D*log^2    |loggamma|*log^2  "
        "cancel(R,C;1)  cancel(Q,2L)"
    )
    for n, components in rows:
        loggamma, logratio, cot, linear, corrected, _ = components
        logn2 = math.log(n + 2.0) ** 2
        quadratic_pair = logratio + cot - 1.0
        linear_center = 2.0 * (linear + 1.0)
        first_cancel = (abs(logratio) + abs(cot) + 1.0) / max(
            abs(quadratic_pair), 1e-300
        )
        second_cancel = (abs(quadratic_pair) + abs(linear_center)) / max(
            abs(corrected), 1e-300
        )
        print(
            f"{n:3d}  {quadratic_pair*logn2:+12.7f}  "
            f"{linear_center*logn2:+12.7f}  {corrected*logn2:+12.7f}  "
            f"{abs(loggamma)*logn2:18.7f}  {first_cancel:13.3f}  "
            f"{second_cancel:12.3f}"
        )


def reordered_cotangent_partial(n: int, m_max: int, mu: np.ndarray) -> float:
    k, c = cutoff_coefficients(n, mu)
    h = k[:, None]
    kk = k[None, :]
    outer = (c / k.astype(np.float64))[:, None] * c[None, :]
    total = 0.0
    for m in range(1, m_max + 1):
        b1 = bernoulli_b1_integer_ratio(m * h, kk)
        total += -2.0 * float(np.sum(outer * b1)) / m
    return total


def check_reordered_normalization() -> None:
    ns = (20, 50, 100)
    mu = mobius_sieve(max(ns))
    print("Reordered BBLS triple-series normalization")
    print("N    M       direct-cotangent       triple-partial         difference")
    for n in ns:
        direct = cotangent_component(n, mu)
        for factor in (1, 5, 20, 100):
            m_max = factor * n
            partial = reordered_cotangent_partial(n, m_max, mu)
            print(
                f"{n:3d}  {m_max:6d}  {direct:+19.11f}  "
                f"{partial:+19.11f}  {partial-direct:+.3e}"
            )


def print_inner_probes(probes: list[InnerProbe]) -> None:
    print("\nInner Möbius-sawtooth sums")
    print(
        "N       profile             A          I_N(A)       |I|/N    "
        "|I|/(N exp(-sqrt(log N)))   decomposition-error"
    )
    for p in probes:
        scale = p.n * math.exp(-math.sqrt(math.log(p.n)))
        print(
            f"{p.n:4d}  {p.label:18s} {p.a:10d}  {p.value:+13.7f}  "
            f"{abs(p.value)/p.n:9.3e}  {abs(p.value)/scale:18.6e}  "
            f"{p.decomposition_error:+.2e}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ns", nargs="+", type=int, default=list(DEFAULT_NS))
    parser.add_argument("--samples", type=int, default=1024)
    parser.add_argument("--skip-triple", action="store_true")
    parser.add_argument(
        "--centered-ns",
        nargs="+",
        type=int,
        default=[20, 50, 100, 300],
        help="cutoffs for the exact centered-pairing table",
    )
    parser.add_argument(
        "--smooth-ns",
        nargs="+",
        type=int,
        default=[100, 300, 1000, 3000, 10000, 100000, 1000000],
        help="cutoffs for the cheap smooth-product factor table",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    ns = tuple(sorted(set(args.ns)))
    print_smooth_product_components(tuple(sorted(set(args.smooth_ns))))
    if not args.skip_triple:
        check_reordered_normalization()
        print_centered_package(tuple(sorted(set(args.centered_ns))))
    print_inner_probes(collect_inner_probes(ns, args.samples))


if __name__ == "__main__":
    main()
