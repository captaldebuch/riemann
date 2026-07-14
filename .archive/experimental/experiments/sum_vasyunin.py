import mpmath as mp

mp.dps = 50

def exact_vasyunin(h, k):
    # compute sum_n=1^infty int_{n}^{n+1}
    # actually we just sum intervals where both u/h and u/k are continuous.
    # The discontinuities are at u = m*h and u = m*k.
    # The set of discontinuities is all integers since h, k are integers.
    total = mp.mpf(0)
    # from 0 to 1
    # u/h < 1, u/k < 1. So {u/h} = u/h, {u/k} = u/k
    # integral is 1/(hk)
    total += mp.mpf(1) / (h*k)
    
    # from 1 to infinity
    # we sum from n=1 to 1000000
    for n in range(1, 1000000):
        # We integrate from n to n+1. We need points of discontinuity inside (n, n+1)
        # But if h,k are integers, the discontinuities are only AT integers!
        # So {u/h} = u/h - floor(u/h) is constant inside (n, n+1)? NO!
        # u/h is an integer when u is a multiple of h.
        # So the discontinuities of {u/h} are at multiples of h.
        # Multiples of h are ALWAYS integers!
        # So inside (n, n+1), there are NO discontinuities!
        # Let u = n + t, t in (0, 1).
        # floor(u/h) is constant. Let it be fh = n // h.
        # floor(u/k) is fk = n // k.
        fh = n // h
        fk = n // k
        
        # integrand: (u/h - fh)*(u/k - fk) / u^2
        # = ( 1/(hk) ) - (fh/k + fk/h)/u + (fh*fk)/u^2
        
        # integral from n to n+1:
        # int 1/u^2 du = 1/n - 1/(n+1)
        # int 1/u du = log((n+1)/n)
        # int 1 du = 1 (but wait, there is no 1 du term, the leading term is 1/(hk) * u^2/u^2 = 1/(hk))
        
        term1 = mp.mpf(1)/(h*k)
        term2 = -(mp.mpf(fh)/k + mp.mpf(fk)/h) * mp.log(mp.mpf(n+1)/n)
        term3 = mp.mpf(fh*fk) * (mp.mpf(1)/n - mp.mpf(1)/(n+1))
        
        total += term1 + term2 + term3
        
    return total

print("h=1, k=1:", exact_vasyunin(1, 1))
print("h=1, k=2:", exact_vasyunin(1, 2))
print("h=2, k=2:", exact_vasyunin(2, 2))
