# Phase 15 pair research: j-mode spectrum of the Mobius-Bernoulli cotangent term.
# Identity: phi1(theta) = sum_j B1(j*theta)/j, so the cotangent component
#   C(N) = 2 sum_{h,k<=N} c(h)c(k) phi1(h/k)/h  decomposes as sum_j W_j(N),
#   W_j(N) = (2/j) sum_{h,k} c(h)c(k) B1(j h/k)/h,  c(k) = -mu(k)(1-k/(N+1)).
# Question: does |W_j| mass concentrate at small j (decay-tractable) or spread (SW-strength)?
import numpy as np

def mobius_sieve(n):
    mu = np.ones(n + 1, dtype=np.int64)
    primes = []
    is_comp = np.zeros(n + 1, dtype=bool)
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i); mu[i] = -1
        for p in primes:
            if i * p > n: break
            is_comp[i * p] = True
            if i % p == 0:
                mu[i * p] = 0; break
            mu[i * p] = -mu[i]
    mu[0] = 0
    return mu

def B1(x):
    f = x - np.floor(x)
    out = f - 0.5
    out[np.abs(f) < 1e-12] = 0.0
    out[np.abs(f - 1) < 1e-12] = 0.0
    return out

for N in (300, 1000):
    mu = mobius_sieve(N)
    k = np.arange(1, N + 1)
    c = -mu[1:] * (1 - k / (N + 1.0))
    ratio = np.outer(k, 1.0 / k)          # ratio[h-1,k-1] = h/k
    W = np.outer(c / k, c)                # W[h-1,k-1] = c(h)/h * c(k)
    total = 0.0
    cum = []
    Js = 96
    Wj = np.zeros(Js + 1)
    for j in range(1, Js + 1):
        Wj[j] = (2.0 / j) * np.sum(W * B1(j * ratio))
        total += Wj[j]
        cum.append(total)
    absW = np.abs(Wj[1:])
    top = np.argsort(-absW)[:6] + 1
    print(f"N={N}: total(J=96)={total:+.6f}")
    print(f"  top-|W_j| modes: " + ", ".join(f"j={t}:{Wj[t]:+.5f}" for t in top))
    print(f"  mass in j<=8: {np.sum(np.abs(Wj[1:9])):.5f}  in 9<=j<=96: {np.sum(absW[8:]):.5f}")
    print(f"  tail scaling: sum|W_j| j in (48,96]: {np.sum(absW[48:]):.5f}")
