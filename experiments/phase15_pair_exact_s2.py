# Exact S2 = C(N) - W1(N): C via V-sum closed forms (O(N^3), small N), W1 direct.
import numpy as np, math
exec(open('experiments/phase15_pair_spectrum.py').read().split('for N in')[0])

def cot_component(N, mu):
    k = np.arange(1, N + 1); c = -mu[1:] * (1 - k / (N + 1.0))
    # phi1(h/k) = (pi/2k) V(h,k); build V for all h per fixed k vectorized
    C = 0.0
    for kk in range(1, N + 1):
        a = np.arange(1, kk)
        if len(a) == 0:
            phi = np.zeros(N)  # k=1: V=0
        else:
            cot = np.cos(np.pi * a / kk) / np.sin(np.pi * a / kk)
            fr = np.outer(np.arange(1, N + 1), a) * (1.0 / kk)
            fr = fr - np.floor(fr)
            phi = (math.pi / (2 * kk)) * (fr @ cot)   # phi1(h/kk) for h=1..N
        C += 2.0 * np.sum((c / np.arange(1, N + 1)) * phi * c[kk - 1])
    return C

for N in (100, 200, 400):
    mu = mobius_sieve(N); k = np.arange(1, N + 1); c = -mu[1:] * (1 - k / (N + 1.0))
    ratio = np.outer(k, 1.0 / k); W = np.outer(c / k, c)
    W1 = 2.0 * np.sum(W * B1(ratio))
    C = cot_component(N, mu)
    S2 = C - W1
    lg, lg2 = math.log(N + 2), math.log(N + 2) ** 2
    print(f"N={N:4d} C={C:+.5f} W1-1={W1-1:+.5f}(xlog={(W1-1)*lg:+.3f}) S2={S2:+.5f}(xlog={S2*lg:+.3f}, xlog2={S2*lg2:+.3f})")
# W1-1 scaling to larger N (cheap)
for N in (1000, 3000):
    mu = mobius_sieve(N); k = np.arange(1, N + 1); c = -mu[1:] * (1 - k / (N + 1.0))
    W1 = 2.0 * np.sum(np.outer(c / k, c) * B1(np.outer(k, 1.0 / k)))
    lg = math.log(N + 2)
    print(f"N={N:4d} W1-1={W1-1:+.5f} xlog={(W1-1)*lg:+.3f} xlog2={(W1-1)*lg**2:+.3f}")
