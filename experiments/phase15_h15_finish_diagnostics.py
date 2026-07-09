#!/usr/bin/env python3
"""Diagnostics for the Phase 15H norm-square finish attempt.

This script mirrors the Lean definitions around
``explicitQuadraticInteractionRemainder_eq_normSq_sub_linear``:

    remainder_N = ||Σ c_N(h) {1/(h x)}||²
                  - (log(2π)-γ) (Σ c_N(h)/h) (Σ c_N(h))
                  - 1.

It also reports the χ-cross term

    <χ, Σ c_N(h)ρ_h> = Σ c_N(h) (log h + 1 - γ) / h

and the completed-square energy

    ||χ - Σ c_N(h)ρ_h||² = 1 - 2 cross + norm.

The norm is evaluated via the already-used Vasyunin/BBLS closed form for the
Gram entry.  This is a diagnostic, not a proof or a certificate.
"""

from __future__ import annotations

import argparse
import math
import time
from dataclasses import dataclass

try:
    import numpy as np
except ModuleNotFoundError as exc:  # pragma: no cover
    raise SystemExit("This diagnostic requires NumPy.") from exc


DEFAULT_NS = (100, 500, 1000, 3000)
EULER_GAMMA = 0.577215664901532860606512090082402431
LOG_TWO_PI_MINUS_GAMMA = math.log(2.0 * math.pi) - EULER_GAMMA


@dataclass(frozen=True)
class FinishDiagnostics:
    n: int
    kernel_sum: float
    smooth_product: float
    norm_integral: float
    remainder: float
    identity_error: float
    cross_chi_rho: float
    defect_energy: float
    sum_c_over_h: float
    sum_c: float
    cutoff_over_k_sum: float
    cutoff_log_over_k_sum: float


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
    """Compute cotangentSumVFormula(h,k), 1 ≤ h,k ≤ limit.

    For fixed k the value depends only on h mod k, so all rows for a fixed
    denominator are computed from the k residue classes.
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
            print(f"  cotangent table: k={k:5d}/{limit} ({elapsed:8.2f}s)", flush=True)

    return values


def quadratic_interaction_kernel(limit: int, progress: bool) -> np.ndarray:
    """Evaluate the Lean ``quadraticInteractionKernel`` on {1,…,limit}²."""
    vasyunin = vasyunin_cotangent_matrix(limit, progress)
    indices = np.arange(1, limit + 1, dtype=np.float64)
    h = indices[:, None]
    k = indices[None, :]
    denominator = 2.0 * h * k
    log_ratio = (k - h) / denominator * np.log(h / k)
    cotangent = -math.pi / denominator * (vasyunin + vasyunin.T)
    kernel = log_ratio + cotangent
    np.fill_diagonal(kernel, 0.0)

    symmetry_error = float(np.max(np.abs(kernel - kernel.T)))
    if symmetry_error > 1e-9:
        raise RuntimeError(f"kernel symmetry check failed: max error {symmetry_error:.3e}")
    return kernel


def analyze_scale(n: int, mu: np.ndarray, kernel: np.ndarray) -> FinishDiagnostics:
    idx = np.arange(1, n + 1, dtype=np.float64)
    mu_n = mu[1 : n + 1].astype(np.float64)
    weight = 1.0 - idx / (n + 1.0)

    # Lean: cutoffMobiusCoeff N k = - μ(k) * (1 - k/(N+1)).
    c = -mu_n * weight
    c_over_h = c / idx
    sum_c_over_h = float(np.sum(c_over_h))
    sum_c = float(np.sum(c))

    terms = kernel[:n, :n] * c[:, None] * c[None, :]
    kernel_sum = float(np.sum(terms))

    smooth_product = LOG_TWO_PI_MINUS_GAMMA * sum_c_over_h * sum_c
    gram = kernel[:n, :n] + (LOG_TWO_PI_MINUS_GAMMA / 2.0) * (
        1.0 / idx[:, None] + 1.0 / idx[None, :]
    )
    norm_integral = float(np.sum(gram * c[:, None] * c[None, :]))

    remainder = kernel_sum - 1.0
    identity_error = norm_integral - smooth_product - 1.0 - remainder

    chi_rho = (np.log(idx) + 1.0 - EULER_GAMMA) / idx
    cross_chi_rho = float(np.sum(c * chi_rho))
    defect_energy = 1.0 - 2.0 * cross_chi_rho + norm_integral

    cutoff_over_k_sum = float(np.sum(mu_n * weight / idx))
    cutoff_log_over_k_sum = float(np.sum(mu_n * weight * np.log(idx) / idx))

    return FinishDiagnostics(
        n=n,
        kernel_sum=kernel_sum,
        smooth_product=smooth_product,
        norm_integral=norm_integral,
        remainder=remainder,
        identity_error=identity_error,
        cross_chi_rho=cross_chi_rho,
        defect_energy=defect_energy,
        sum_c_over_h=sum_c_over_h,
        sum_c=sum_c,
        cutoff_over_k_sum=cutoff_over_k_sum,
        cutoff_log_over_k_sum=cutoff_log_over_k_sum,
    )


def print_results(results: list[FinishDiagnostics]) -> None:
    print("\nH15-H3 norm representation diagnostics")
    print(
        "N      norm_int        smooth       kernel_sum     remainder   "
        "id_error      rem*logN"
    )
    for r in results:
        logn = math.log(r.n + 2.0)
        print(
            f"{r.n:5d}  {r.norm_integral:+13.8f}  {r.smooth_product:+11.8f}  "
            f"{r.kernel_sum:+13.8f}  {r.remainder:+11.8f}  "
            f"{r.identity_error:+.3e}  {r.remainder * logn:+11.8f}"
        )

    print("\nLinear/cross and completed-square diagnostics")
    print(
        "N      cross=<χ,Σcρ>   defect_energy    sum(c/h)      sum(c)      "
        "overK        logOverK+1"
    )
    for r in results:
        print(
            f"{r.n:5d}  {r.cross_chi_rho:+14.8f}  {r.defect_energy:+14.8f}  "
            f"{r.sum_c_over_h:+11.8f}  {r.sum_c:+10.6f}  "
            f"{r.cutoff_over_k_sum:+10.7f}  {r.cutoff_log_over_k_sum + 1.0:+12.8f}"
        )

    print("\nCandidate leading behavior")
    print("N      norm - smooth - 1       |remainder|       1/logN      1/logN^2")
    for r in results:
        logn = math.log(r.n + 2.0)
        print(
            f"{r.n:5d}  {r.norm_integral - r.smooth_product - 1.0:+18.10f}  "
            f"{abs(r.remainder):13.8f}  {1.0/logn:10.7f}  {1.0/logn**2:10.7f}"
        )

    if len(results) >= 2:
        xs = np.array([math.log(math.log(r.n + 2.0)) for r in results], dtype=np.float64)
        ys = np.array([math.log(max(abs(r.remainder), 1e-300)) for r in results], dtype=np.float64)
        slope, intercept = np.polyfit(xs, ys, 1)
        print(
            "\nFit |remainder_N| ≈ C / log(N)^p over reported points: "
            f"p ≈ {-slope:.3f}, C ≈ {math.exp(intercept):.6g}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ns", nargs="+", type=int, default=list(DEFAULT_NS))
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument(
        "--max-formula-n",
        type=int,
        default=3000,
        help=(
            "Largest N to attempt with the vectorized cotangent formula. "
            "Use a smaller value if the local machine cannot hold/check N=3000."
        ),
    )
    args = parser.parse_args()
    if any(n < 2 for n in args.ns):
        parser.error("all cutoffs must be at least 2")
    if max(args.ns) > args.max_formula_n:
        parser.error("requested cutoff exceeds --max-formula-n")
    return args


def main() -> None:
    args = parse_args()
    cutoffs = sorted(set(args.ns))
    limit = max(cutoffs)
    started = time.perf_counter()
    print(f"Computing formula diagnostics up to N={limit}", flush=True)
    mu = mobius_sieve(limit)
    kernel = quadratic_interaction_kernel(limit, progress=not args.quiet)
    results = [analyze_scale(n, mu, kernel) for n in cutoffs]
    print_results(results)
    print(f"\nCompleted in {time.perf_counter() - started:.2f}s")


if __name__ == "__main__":
    main()
