import mpmath as mp
from fractions import Fraction

mp.dps = 100

def get_integral(h, k):
    # int_0^infty {u/h} {u/k} / u^2 du
    # Since {u/h} = u/h for u in (0, h), if h <= k, the integral has different segments.
    # We can evaluate it numerically with high precision.
    f = lambda u: (u/h - mp.floor(u/h)) * (u/k - mp.floor(u/k)) / (u**2)
    return mp.quad(f, [0, mp.inf])

for h, k in [(1,1), (1,2), (2,2)]:
    val = get_integral(h, k)
    print(f"h={h}, k={k}: {val}")
    
    # We want a rational bound: val approx Q. Let's find a simple Fraction.
    # We can just round to 6 decimal places.
    val_float = float(val)
    f = Fraction(val_float).limit_denominator(1000000)
    
    # Let's say error = 1e-6
    error = Fraction(1, 1000000)
    print(f"  value: {f.numerator}/{f.denominator}")
    print(f"  error: {error.numerator}/{error.denominator}")
