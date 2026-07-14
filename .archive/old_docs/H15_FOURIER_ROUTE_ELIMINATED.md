# H15 Fourier Decomposition Route: ELIMINATED
## Numerical Evidence That This Approach Does Not Work

**Date**: 2026-07-13  
**Status**: ROUTE ELIMINATED  
**Evidence**: Computational verification

---

## The Approach (Failed)

**Strategy**: Decompose the sawtooth using Fourier series:
$$B_1(x) = \sum_{j \ne 0} \frac{e^{2\pi i jx}}{2\pi i j}$$

Then:
$$\sum_{k=1}^{N} \mu(k) B_1(A/k) = \sum_{j \ne 0} \frac{1}{2\pi i j} \sum_{k=1}^{N} \mu(k) e^{2\pi i j A/k}$$

If we could bound each reciprocal-phase Möbius sum, we could sum over $j$ with the Fourier decay $1/j^2$.

---

## The Problem (Discovered via Computation)

**Empirical finding** (N=1000, A=5):

$$|\sum_{k=1}^{N} \mu(k) e(jA/k)| \approx O(1) \text{ to } O(\sqrt{N})$$

across all tested values of $j$ (j = 1, 2, 3, 5, 10, 20, 50, 100, 200).

**Convergence analysis**:

If each phase sum is bounded by $C \sqrt{N}$ (or even constant), then:
$$\sum_j \frac{1}{j^2} \cdot O(\sqrt{N}) \sim O(\sqrt{N}) \cdot \sum_j \frac{1}{j^2} = O(\sqrt{N}) \cdot O(1) = O(\sqrt{N})$$

But H15 requires $O(1/\log^2 N)$, which is **exponentially smaller** than $O(\sqrt{N})$.

**Ratio gap**:
$$\frac{\text{Fourier bound}}{\text{Required bound}} = \frac{O(\sqrt{N})}{O(1/\log^2 N)} \sim N^{1/2} \cdot \log^2 N \to \infty$$

---

## Why This Route Fails

The Fourier decomposition is insufficient because:

1. **Reciprocal-phase sums lack sufficient cancellation**
   - Linear-phase Möbius sums $\sum \mu(k) e(\alpha k)$ have strong cancellation (Weyl bounds)
   - Reciprocal-phase sums $\sum \mu(k) e(A/k)$ do NOT have the same cancellation
   - The oscillation is "too slow" at large $k$ (phase grows as $A/k$, not $\alpha k$)

2. **Fourier weights decay too slowly**
   - Fourier series of sawtooth has weights $1/j$ (not $1/j^2$)
   - With $1/j^2$ in the Fourier formula, we get $1/j$ net decay
   - This is not enough to dominate the $O(\sqrt{N})$ phase-sum growth

3. **No additional cancellation mechanism**
   - The cutoff weight $\omega_N(k) = 1 - k/(N+1)$ provides boundary smoothing, not oscillatory cancellation
   - To achieve $O(1/\log^2 N)$, we would need an additional mechanism (e.g., Farey structure, modular inversion, or a genuinely novel technique)

---

## Implications for the H15 Search

**This elimination tells us**:

1. **The bound is not a trivial consequence of Fourier analysis**
   - It requires techniques beyond standard harmonic analysis
   - Likely candidates: Farey-cell methods, Estermann zeta / Mellin inversion, or entirely new mathematics

2. **Reciprocal-phase Möbius bounds are non-standard**
   - Standard references (Weyl, van der Corput, linear-phase methods) do NOT apply
   - A primary theorem on reciprocal-phase sums would be specialized and notable

3. **Possible explanations**:
   - **A**: The bound exists in the literature but is technical and not widely known
   - **B**: The bound is conditional on additional structure (e.g., only for Farey-partition sums, not uniform in $A$)
   - **C**: The bound is genuinely novel and remains open

---

## Next Priorities

**Search focus should shift to**:

1. **Farey-cell decomposition** (Graham–Kolesnik, Nowak)
   - Reciprocal structure via $|ad - bc| = 1$ might provide the needed cancellation
   - Non-modular reciprocals still involve reciprocal structure that could help

2. **Estermann zeta / Mellin inversion** (Montgomery–Vaughan Ch. 13)
   - Autocorrelation via Mellin might transport the bound from another domain
   - But: inversion might lose rates; need to verify carefully

3. **Expert consultation**
   - The reciprocal-phase Möbius bound may be a known open problem
   - Or it may be a well-kept secret in specialized literature

---

## Conclusion

**The Fourier decomposition route does not work for H15.**

The numerical evidence is clear: naive Fourier-then-sum yields $O(\sqrt{N})$, not $O(1/\log^2 N)$.

To proceed, we must:
- Find a non-Fourier technique in the literature, OR
- Admit that the bound is open, OR
- Develop new mathematics

All three are honest outcomes.

---

## Raw Numerical Data

```
H15 FOURIER DECOMPOSITION VERIFICATION
======================================

N=  100: max(|sawtooth|·log²(N)) = 456.9987
N=  300: max(|sawtooth|·log²(N)) = 561.5257
N=  500: max(|sawtooth|·log²(N)) = 960.3366
N= 1000: max(|sawtooth|·log²(N)) = 1573.1029
N= 2000: max(|sawtooth|·log²(N)) = 3011.1111

Monotonically decreasing? False
Bound GROWING as O(√N) or worse: CONSISTENT WITH FOURIER ROUTE FAILURE
```

---

**Next step**: Refocus search on Farey cells and Mellin inversion; prepare to declare H15 open if neither works.

