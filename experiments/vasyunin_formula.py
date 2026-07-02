import math

def V(h, k):
    res = 0.0
    for a in range(1, k):
        frac = (a * h / k) - math.floor(a * h / k)
        res += frac / math.tan(math.pi * a / k)
    return res

def b(h, k):
    gamma = 0.57721566490153286
    log2pi = math.log(2 * math.pi)
    term1 = (log2pi - gamma) / 2.0 * (1.0/h + 1.0/k)
    term2 = (k - h) / (2.0 * h * k) * math.log(h/k) if h != k else 0.0
    term3 = math.pi / (2.0 * h * k) * (V(h, k) + V(k, h))
    return 2 * math.pi * (term1 + term2 - term3)

print("b(1, 1) =", b(1, 1))
print("b(1, 2) =", b(1, 2))
print("b(2, 2) =", b(2, 2))
