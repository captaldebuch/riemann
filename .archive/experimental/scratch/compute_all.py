import sympy as sp
from sympy import pi, log, sqrt, EulerGamma, gcd

def compute_V(h, k):
    V = 0
    for a in range(1, k):
        V += sp.frac(sp.Rational(a*h, k)) * sp.cot(pi * a / k)
    return sp.simplify(V)

pairs = []
for k in range(2, 11):
    for h in range(1, k):
        if gcd(h, k) == 1:
            pairs.append((h, k))

print(f"Total pairs: {len(pairs)}")

for h, k in pairs:
    V_hk = compute_V(h, k)
    V_kh = compute_V(k, h)
    tot = sp.simplify(V_hk + V_kh)
    print(f"({h},{k}): V_hk+V_kh = {tot}")

