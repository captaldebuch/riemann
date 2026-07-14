import sympy as sp
import mpmath as mp

mp.dps = 50

def true_integral(h, k):
    # integrate {1/(hx)} * {1/(kx)} dx from 0 to infinity
    # Let x = 1/t. dx = -dt/t^2.
    # int_0^infty {t/h} * {t/k} dt / t^2
    # We can compute this numerically with mpmath
    
    f = lambda t: (t/h - mp.floor(t/h)) * (t/k - mp.floor(t/k)) / (t**2)
    return mp.quad(f, [0, mp.inf])

print("h=1, k=1:", true_integral(1, 1))
print("h=1, k=2:", true_integral(1, 2))
print("h=2, k=2:", true_integral(2, 2))
