#!/usr/bin/env python3
"""Numerical gate for the Phase 15 mode-split strategy.

This diagnostic intentionally freezes no Lean statement.  It checks the
proposed split

    centered(N) = (W_1(N) - 1) + bracket(N),

where

    centered(N) = logRatio_N + cotangent_N - 1
                  + 2 * (explicitLinearMobiusSum_N + 1)

is the signed centered Bernoulli package appearing in
``QuadraticInteractionCenteredBernoulliPairEstimate`` and

    W_1(N) = 2 * sum_{h,k <= N} c_N(h)c_N(k) B_1(h/k) / h

is the first BBLS Fourier mode of the cotangent/Bernoulli component.

The table reports the natural rate diagnostics for ``W_1 - 1`` and for the
residual bracket.  Sparse ``W_1`` sampling up to larger N is blockwise and does
not require the Vasyunin cotangent table.
"""

from __future__ import annotations

import argparse
import math
import time
from dataclasses import dataclass

import numpy as np

from phase15_h15_finish_diagnostics import (
    EULER_GAMMA,
    LOG_TWO_PI_MINUS_GAMMA,
    mobius_sieve,
    vasyunin_cotangent_matrix,
)


DEFAULT_BRACKET_NS = tuple(range(20, 401, 20))
DEFAULT_W1_NS = (100, 200, 400, 700, 1000, 1500, 2000, 3000, 5000, 7500, 10000)
DEFAULT_W1_BREAKDOWN_NS = (100, 400, 1000)


@dataclass(frozen=True)
class ModeSplitRow:
    n: int
    loggamma: float
    logratio: float
    cotangent: float
    explicit_linear: float
    centered: float
    w1: float

    @property
    def w1_minus_one(self) -> float:
        return self.w1 - 1.0

    @property
    def bracket(self) -> float:
        return self.centered - self.w1_minus_one


def bernoulli_b1_ratio(h: np.ndarray, k: np.ndarray) -> np.ndarray:
    """Return B_1(h/k) for positive integer arrays h,k.

    This uses exact integer remainders before converting to floating point:
    B_1(a/b) = 0 if b | a, otherwise (a mod b)/b - 1/2.
    """

    remainder = np.remainder(h, k)
    return np.where(remainder == 0, 0.0, remainder / k - 0.5)


def cutoff_coefficients(n: int, mu: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    k_int = np.arange(1, n + 1, dtype=np.int64)
    k = k_int.astype(np.float64)
    c = -mu[1 : n + 1].astype(np.float64) * (1.0 - k / (n + 1.0))
    return k_int, c


def w1_mode(n: int, mu: np.ndarray, block_size: int = 512) -> float:
    """Compute W_1(N) blockwise.

    ``W_1 = 2 * sum_h (c_h/h) * sum_k c_k B_1(h/k)``.
    """

    k_int, c = cutoff_coefficients(n, mu)
    k_float = k_int.astype(np.float64)
    c_over_h = c / k_float
    total = 0.0
    k_row = k_int[None, :]
    for start in range(0, n, block_size):
        stop = min(n, start + block_size)
        h_col = k_int[start:stop, None]
        b1 = bernoulli_b1_ratio(h_col, k_row)
        total += float((c_over_h[start:stop] * (b1 @ c)).sum())
    return 2.0 * total


def centered_components_from_vasyunin(
    n: int, mu: np.ndarray, vasyunin: np.ndarray
) -> tuple[float, float, float, float, float]:
    k_int, c = cutoff_coefficients(n, mu)
    k = k_int.astype(np.float64)
    h = k[:, None]
    kk = k[None, :]
    coeff = c[:, None] * c[None, :]
    v = vasyunin[:n, :n]

    cotangent = float(np.sum(coeff * (-math.pi / (2.0 * h * kk) * (v + v.T))))
    logratio_kernel = (kk - h) / (2.0 * h * kk) * np.log(h / kk)
    logratio = float(np.sum(coeff * logratio_kernel))
    sum_c_over_h = float(np.sum(c / k))
    sum_c = float(np.sum(c))
    loggamma = LOG_TWO_PI_MINUS_GAMMA * sum_c_over_h * sum_c
    chi_kernel = (np.log(k) + 1.0 - EULER_GAMMA) / k
    explicit_linear = float(np.sum(-c * chi_kernel))
    centered = logratio + cotangent - 1.0 + 2.0 * (explicit_linear + 1.0)
    return loggamma, logratio, cotangent, explicit_linear, centered


def collect_bracket_rows(ns: tuple[int, ...], progress: bool) -> list[ModeSplitRow]:
    max_n = max(ns)
    mu = mobius_sieve(max_n)
    started = time.perf_counter()
    v = vasyunin_cotangent_matrix(max_n, progress=progress)
    if progress:
        print(f"cotangent matrix up to N={max_n} ready in {time.perf_counter() - started:.2f}s")
    rows: list[ModeSplitRow] = []
    for n in ns:
        loggamma, logratio, cotangent, explicit_linear, centered = (
            centered_components_from_vasyunin(n, mu, v)
        )
        rows.append(
            ModeSplitRow(
                n=n,
                loggamma=loggamma,
                logratio=logratio,
                cotangent=cotangent,
                explicit_linear=explicit_linear,
                centered=centered,
                w1=w1_mode(n, mu),
            )
        )
    return rows


def print_bracket_rows(rows: list[ModeSplitRow], print_step: int) -> None:
    print("\nMode split bracket diagnostic")
    print(
        "N       W1-1        bracket      centered     "
        "|W1-1|log   |W1-1|log^2   |bracket|log^2"
    )
    for row in rows:
        if row.n % print_step != 0 and row.n not in (rows[0].n, rows[-1].n):
            continue
        logn = math.log(row.n + 2.0)
        print(
            f"{row.n:4d}  {row.w1_minus_one:+11.7f}  {row.bracket:+11.7f}  "
            f"{row.centered:+11.7f}  "
            f"{abs(row.w1_minus_one) * logn:11.7f}  "
            f"{abs(row.w1_minus_one) * logn * logn:13.7f}  "
            f"{abs(row.bracket) * logn * logn:15.7f}"
        )

    max_w1_log = max(abs(row.w1_minus_one) * math.log(row.n + 2.0) for row in rows)
    max_w1_log2 = max(
        abs(row.w1_minus_one) * math.log(row.n + 2.0) ** 2 for row in rows
    )
    max_bracket_log2 = max(
        abs(row.bracket) * math.log(row.n + 2.0) ** 2 for row in rows
    )
    print("\nSummary over bracket grid")
    print(f"  max |W1-1|*log(N+2)      = {max_w1_log:.9f}")
    print(f"  max |W1-1|*log(N+2)^2    = {max_w1_log2:.9f}")
    print(f"  max |bracket|*log(N+2)^2 = {max_bracket_log2:.9f}")


def print_sparse_w1(ns: tuple[int, ...], block_size: int) -> None:
    mu = mobius_sieve(max(ns))
    print("\nSparse W1-only diagnostic")
    print("N          W1           W1-1       |W1-1|log   |W1-1|log^2")
    for n in ns:
        started = time.perf_counter()
        value = w1_mode(n, mu, block_size=block_size)
        elapsed = time.perf_counter() - started
        logn = math.log(n + 2.0)
        print(
            f"{n:5d}  {value:+12.8f}  {value - 1.0:+11.8f}  "
            f"{abs(value - 1.0) * logn:11.8f}  "
            f"{abs(value - 1.0) * logn * logn:13.8f}  "
            f"({elapsed:6.2f}s)"
        )


def print_w1_breakdown(ns: tuple[int, ...]) -> None:
    """Report where the first-mode main term numerically lives.

    This is intentionally matrix-based and meant only for moderate N.  The
    decomposition uses the research-sign convention for W1, not the Lean
    ``cutoffMobiusBernoulliMode`` sign.
    """

    mu = mobius_sieve(max(ns))
    print("\nW1 contribution breakdown (research-sign W1)")
    print(
        "N        W1      h<k       h>k     1/2<r<2     "
        "r<=1/2     r>=2      q=1      q=2      q=3..5   q=6..10   q>10"
    )
    for n in ns:
        k_int, c = cutoff_coefficients(n, mu)
        k_float = k_int.astype(np.float64)
        h = k_int[:, None]
        kk = k_int[None, :]
        contrib = (
            2.0
            * (c / k_float)[:, None]
            * c[None, :]
            * bernoulli_b1_ratio(h, kk)
        )
        h_lt_k = h < kk
        h_gt_k = h > kk
        near = (2 * h > kk) & (h < 2 * kk) & (h != kk)
        low = 2 * h <= kk
        high = h >= 2 * kk
        q = h // kk
        q1 = h_gt_k & (q == 1)
        q2 = h_gt_k & (q == 2)
        q3_5 = h_gt_k & (3 <= q) & (q <= 5)
        q6_10 = h_gt_k & (6 <= q) & (q <= 10)
        q_gt10 = h_gt_k & (q > 10)

        def s(mask: np.ndarray) -> float:
            return float(contrib[mask].sum())

        print(
            f"{n:4d}  {float(contrib.sum()):+8.5f}  {s(h_lt_k):+8.5f}  "
            f"{s(h_gt_k):+8.5f}  {s(near):+10.5f}  {s(low):+9.5f}  "
            f"{s(high):+8.5f}  {s(q1):+8.5f}  {s(q2):+8.5f}  "
            f"{s(q3_5):+9.5f}  {s(q6_10):+9.5f}  {s(q_gt10):+8.5f}"
        )


def parse_ns(raw: str | None, default: tuple[int, ...]) -> tuple[int, ...]:
    if raw is None:
        return default
    values = tuple(int(part) for part in raw.split(",") if part.strip())
    if not values:
        raise SystemExit("empty --ns list")
    if min(values) < 1:
        raise SystemExit("N values must be positive")
    return values


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--bracket-ns",
        default=None,
        help="comma-separated N values for the full bracket check (default: 20,40,...,400)",
    )
    parser.add_argument(
        "--all-20-400",
        action="store_true",
        help="run the full bracket grid N=20,21,...,400",
    )
    parser.add_argument(
        "--w1-ns",
        default=None,
        help="comma-separated N values for sparse W1-only sampling",
    )
    parser.add_argument(
        "--w1-breakdown-ns",
        default=None,
        help="comma-separated moderate N values for first-mode contribution breakdown",
    )
    parser.add_argument("--block-size", type=int, default=512)
    parser.add_argument("--print-step", type=int, default=20)
    parser.add_argument("--no-progress", action="store_true")
    args = parser.parse_args()

    bracket_ns = (
        tuple(range(20, 401))
        if args.all_20_400
        else parse_ns(args.bracket_ns, DEFAULT_BRACKET_NS)
    )
    w1_ns = parse_ns(args.w1_ns, DEFAULT_W1_NS)
    w1_breakdown_ns = parse_ns(args.w1_breakdown_ns, DEFAULT_W1_BREAKDOWN_NS)
    rows = collect_bracket_rows(bracket_ns, progress=not args.no_progress)
    print_bracket_rows(rows, print_step=args.print_step)
    print_sparse_w1(w1_ns, block_size=args.block_size)
    print_w1_breakdown(w1_breakdown_ns)


if __name__ == "__main__":
    main()
