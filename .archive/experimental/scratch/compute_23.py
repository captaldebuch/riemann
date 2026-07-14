import sympy as sp
from sympy import pi, log, sqrt, EulerGamma

def compute_V(h, k):
    V = 0
    for a in range(1, k):
        V += sp.frac(sp.Rational(a*h, k)) * sp.cot(pi * a / k)
    return sp.simplify(V)

h, k = 2, 3
V23 = compute_V(h, k)
V32 = compute_V(k, h)

print(f"V({h},{k}) =", V23)
print(f"V({k},{h}) =", V32)

expr = sp.Rational(1,2) * (log(2*pi) - EulerGamma) * (sp.Rational(1,h) + sp.Rational(1,k)) \
       + sp.Rational(k-h, 2*h*k) * log(sp.Rational(h,k)) \
       - pi / (2*h*k) * (V23 + V32)

print("Expr =", sp.simplify(expr))
print("Float =", expr.evalf(50))
