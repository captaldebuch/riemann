#!/usr/bin/env python3
"""Numerical diagnostics for the Phase 15 quadratic interaction kernel.

This script mirrors the Lean definitions of ``cutoffMobiusCoeff``,
``cotangentSumVFormula``, and ``quadraticInteractionKernel``.  It is diagnostic
only: it does not supply a proof or a bound for ``interaction_bound``.
"""

from __future__ import annotations

import argparse
import math
import time
from dataclasses import dataclass

try:
    import numpy as np
except ModuleNotFoundError as exc:  # pragma: no cover - environment-dependent message
    raise SystemExit(
        "This diagnostic requires NumPy. Run it from the project's scientific "
        "Python environment."
    ) from exc


DEFAULT_NS = (50, 100, 200, 500, 1000)


@dataclass(frozen=True)
class ScaleResult:
    n: int
    total: float
    diagonal: float
    near_sqrt: float
    far_sqrt: float
    near_n_over_log_n: float
    far_n_over_log_n: float
    coprime: float
    noncoprime: float
    absolute_mass: float
    positive_mass: float
    negative_mass: float
    gcd_exact: np.ndarray
    gcd_groups: tuple[tuple[str, float], ...]
    ratio_groups: tuple[tuple[str, float], ...]


def mobius_sieve(limit: int) -> np.ndarray:
    """Return μ(0), …, μ(limit) using a linear sieve."""
    mu = np.zeros(limit + 1, dtype=np.int8)
    mu[1] = 1
    composite = np.zeros(limit + 1, dtype=bool)
    primes: list[int] = []
    for value in range(2, limit + 1):
        if not composite[value]:
            primes.append(value)
            mu[value] = -1
        for prime in primes:
            product = value * prime
            if product > limit:
                break
            composite[product] = True
            if value % prime == 0:
                mu[product] = 0
                break
            mu[product] = -mu[value]
    return mu


def vasyunin_cotangent_matrix(limit: int, progress: bool) -> np.ndarray:
    """Compute V(h,k) for 1 ≤ h,k ≤ limit.

    For a fixed denominator k, V(h,k) depends only on h modulo k.  Computing
    all residue classes at once keeps the total work at Σ k² vectorized integer
    operations rather than a cubic Python loop.
    """
    values = np.zeros((limit, limit), dtype=np.float64)
    all_h = np.arange(1, limit + 1, dtype=np.int64)
    started = time.perf_counter()

    for k in range(2, limit + 1):
        a = np.arange(1, k, dtype=np.int64)
        cotangent = 1.0 / np.tan(math.pi * a / k)
        residue_classes = np.arange(k, dtype=np.int64)[:, None]
        fractions = ((residue_classes * a[None, :]) % k).astype(np.float64) / k
        by_residue = fractions @ cotangent
        values[:, k - 1] = by_residue[all_h % k]

        if progress and (k % 100 == 0 or k == limit):
            elapsed = time.perf_counter() - started
            print(f"  cotangent table: k={k:4d}/{limit} ({elapsed:7.2f}s)")

    return values


def quadratic_interaction_kernel(limit: int, progress: bool) -> np.ndarray:
    """Evaluate the symmetric interaction kernel on {1,…,limit}²."""
    vasyunin = vasyunin_cotangent_matrix(limit, progress)
    indices = np.arange(1, limit + 1, dtype=np.float64)
    h = indices[:, None]
    k = indices[None, :]
    denominator = 2.0 * h * k
    log_ratio = (k - h) / denominator * np.log(h / k)
    cotangent = -math.pi / denominator * (vasyunin + vasyunin.T)
    kernel = log_ratio + cotangent

    symmetry_error = float(np.max(np.abs(kernel - kernel.T)))
    if symmetry_error > 5e-12:
        raise RuntimeError(f"kernel symmetry check failed: max error {symmetry_error:.3e}")
    return kernel


def grouped_gcd_contributions(exact: np.ndarray, n: int) -> tuple[tuple[str, float], ...]:
    ranges = (
        ("gcd=1", 1, 1),
        ("gcd=2", 2, 2),
        ("gcd=3..5", 3, 5),
        ("gcd=6..10", 6, 10),
        ("gcd=11..25", 11, 25),
        ("gcd=26..50", 26, 50),
        ("gcd>50", 51, n),
    )
    groups: list[tuple[str, float]] = []
    for label, lo, hi in ranges:
        if lo > n:
            contribution = 0.0
        else:
            contribution = float(exact[lo : min(hi, n) + 1].sum())
        groups.append((label, contribution))
    return tuple(groups)


def grouped_ratio_contributions(terms: np.ndarray) -> tuple[tuple[str, float], ...]:
    n = terms.shape[0]
    indices = np.arange(1, n + 1, dtype=np.float64)
    ratio = indices[:, None] / indices[None, :]
    groups = (
        ("h/k < 1/4", ratio < 0.25),
        ("1/4 ≤ h/k < 1/2", (0.25 <= ratio) & (ratio < 0.5)),
        ("1/2 ≤ h/k < 3/4", (0.5 <= ratio) & (ratio < 0.75)),
        ("3/4 ≤ h/k < 1", (0.75 <= ratio) & (ratio < 1.0)),
        ("h/k = 1", ratio == 1.0),
        ("1 < h/k ≤ 4/3", (1.0 < ratio) & (ratio <= 4.0 / 3.0)),
        ("4/3 < h/k ≤ 2", (4.0 / 3.0 < ratio) & (ratio <= 2.0)),
        ("2 < h/k ≤ 4", (2.0 < ratio) & (ratio <= 4.0)),
        ("h/k > 4", ratio > 4.0),
    )
    return tuple((label, float(terms[mask].sum())) for label, mask in groups)


def analyze_scale(n: int, mu: np.ndarray, kernel: np.ndarray) -> ScaleResult:
    indices = np.arange(1, n + 1, dtype=np.float64)
    coefficients = -mu[1 : n + 1].astype(np.float64) * (1.0 - indices / (n + 1.0))
    terms = kernel[:n, :n] * coefficients[:, None] * coefficients[None, :]

    integer_indices = np.arange(1, n + 1, dtype=np.int64)
    distance = np.abs(integer_indices[:, None] - integer_indices[None, :])
    diagonal_mask = distance == 0
    sqrt_mask = (distance > 0) & (distance <= math.sqrt(n))
    n_over_log_n_mask = (distance > 0) & (distance <= n / math.log(n))

    total = float(terms.sum())
    diagonal = float(terms[diagonal_mask].sum())
    near_sqrt = float(terms[sqrt_mask].sum())
    near_n_over_log_n = float(terms[n_over_log_n_mask].sum())

    gcd_values = np.gcd(integer_indices[:, None], integer_indices[None, :])
    gcd_exact = np.bincount(
        gcd_values.ravel(), weights=terms.ravel(), minlength=n + 1
    )

    return ScaleResult(
        n=n,
        total=total,
        diagonal=diagonal,
        near_sqrt=near_sqrt,
        far_sqrt=total - diagonal - near_sqrt,
        near_n_over_log_n=near_n_over_log_n,
        far_n_over_log_n=total - diagonal - near_n_over_log_n,
        coprime=float(gcd_exact[1]),
        noncoprime=float(gcd_exact[2:].sum()),
        absolute_mass=float(np.abs(terms).sum()),
        positive_mass=float(terms[terms > 0].sum()),
        negative_mass=float(terms[terms < 0].sum()),
        gcd_exact=gcd_exact,
        gcd_groups=grouped_gcd_contributions(gcd_exact, n),
        ratio_groups=grouped_ratio_contributions(terms),
    )


def print_summary(results: list[ScaleResult]) -> None:
    print("\nInteraction sum and distance-to-diagonal decomposition")
    print(
        "N       total      total-1       diagonal      near√N       far√N   "
        "nearN/logN   farN/logN"
    )
    for result in results:
        print(
            f"{result.n:4d}  {result.total:11.7f}  {result.total - 1:11.7f}  "
            f"{result.diagonal:11.7f}  {result.near_sqrt:11.7f}  "
            f"{result.far_sqrt:11.7f}  {result.near_n_over_log_n:11.7f}  "
            f"{result.far_n_over_log_n:11.7f}"
        )

    print("\nCancellation and coprimality")
    print("N       positive      negative       |terms|      gcd=1       gcd>1")
    for result in results:
        print(
            f"{result.n:4d}  {result.positive_mass:12.7f}  "
            f"{result.negative_mass:12.7f}  {result.absolute_mass:12.7f}  "
            f"{result.coprime:11.7f}  {result.noncoprime:11.7f}"
        )

    for result in results:
        print(f"\nN={result.n}: gcd groups")
        print("  " + "  ".join(f"{label}: {value:+.7f}" for label, value in result.gcd_groups))
        top = sorted(
            ((gcd, float(value)) for gcd, value in enumerate(result.gcd_exact[1:], 1)),
            key=lambda item: abs(item[1]),
            reverse=True,
        )[:10]
        print("  largest exact gcd contributions: " + ", ".join(
            f"g={gcd}: {value:+.7f}" for gcd, value in top
        ))

        print(f"N={result.n}: h/k ratio groups")
        for label, value in result.ratio_groups:
            print(f"  {label:20s} {value:+.7f}")

    largest = results[-1]
    print(f"\nFinite-N conclusion (largest cutoff N={largest.n})")
    print(
        f"  diagonal={largest.diagonal:+.7f}; "
        f"coprime={largest.coprime:+.7f}; noncoprime={largest.noncoprime:+.7f}"
    )
    print(
        f"  √N window={largest.near_sqrt:+.7f}, "
        f"its far complement={largest.far_sqrt:+.7f}"
    )
    print(
        f"  N/log N window={largest.near_n_over_log_n:+.7f}, "
        f"its far complement={largest.far_n_over_log_n:+.7f}"
    )
    print(
        "  Evidence: the target +1 is produced by broad off-diagonal averaging "
        "and cancellation, not by the diagonal, a stable near-diagonal window, "
        "or coprime pairs alone."
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ns",
        nargs="+",
        type=int,
        default=list(DEFAULT_NS),
        help="cutoffs to analyze (default: 50 100 200 500 1000)",
    )
    parser.add_argument("--quiet", action="store_true", help="hide cotangent-table progress")
    args = parser.parse_args()
    if any(n < 2 for n in args.ns):
        parser.error("all cutoffs must be at least 2")
    return args


def main() -> None:
    args = parse_args()
    cutoffs = sorted(set(args.ns))
    limit = max(cutoffs)
    started = time.perf_counter()
    mu = mobius_sieve(limit)
    kernel = quadratic_interaction_kernel(limit, progress=not args.quiet)
    results = [analyze_scale(n, mu, kernel) for n in cutoffs]
    print_summary(results)
    print(f"\nCompleted in {time.perf_counter() - started:.2f}s")


if __name__ == "__main__":
    main()
