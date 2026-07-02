import sys
import os
import math
import numpy as np
import matplotlib.pyplot as plt

sys.path.insert(0, os.path.dirname(__file__))
from phase11c_search import compute_numeric_energy

def get_mobius():
    M = 2000
    mu = np.ones(M + 1, dtype=int)
    primes = []
    is_prime = np.ones(M + 1, dtype=bool)
    is_prime[0:2] = False
    for p in range(2, M + 1):
        if is_prime[p]:
            primes.append(p)
            for i in range(p * 2, M + 1, p):
                is_prime[i] = False
    for p in primes:
        for i in range(p, M + 1, p):
            mu[i] *= -1
        for i in range(p * p, M + 1, p * p):
            mu[i] = 0
    return mu

def evaluate_candidate(c_opt, mu, profile_name, cutoff):
    mu_cutoff = -mu * cutoff
    
    # Scale to match optimal c via least squares
    norm = np.dot(mu_cutoff, mu_cutoff)
    if norm > 0:
        a = np.dot(c_opt, mu_cutoff) / norm
        c_approx = a * mu_cutoff
    else:
        a = 0
        c_approx = np.zeros_like(c_opt)
        
    residual = np.linalg.norm(c_opt - c_approx)
    corr = np.corrcoef(c_opt, mu_cutoff)[0, 1] if np.std(mu_cutoff) > 0 else 0
    return corr, residual

def main():
    Ns = [20, 50, 100, 200]
    mu_all = get_mobius()
    
    for N in Ns:
        E_N, c_opt, _ = compute_numeric_energy(N)
        k_vals = np.arange(1, N + 1)
        mu = mu_all[1:N+1]
        
        t = k_vals / N
        t_plus_1 = k_vals / (N + 1)
        
        candidates = {
            "1. -μ(k)": np.ones_like(k_vals),
            "2. -μ(k) * (1 - k/N)": 1.0 - t,
            "3. -μ(k) * (1 - k/(N+1))": 1.0 - t_plus_1,
            "4. -μ(k) * max(0, 1 - k/N)": np.maximum(0, 1.0 - t),
            "5. -μ(k) * (1 - k/N)^2": (1.0 - t)**2
        }
        
        print(f"================ N = {N} ================")
        print(f"E_N = {E_N:.6f}, E_N * log(N+2) = {E_N * math.log(N + 2):.6f}")
        for name, cutoff in candidates.items():
            corr, res = evaluate_candidate(c_opt, mu, name, cutoff)
            print(f"  {name:30s} : Corr = {corr:7.4f}, Resid = {res:7.4f}")
        print()

if __name__ == '__main__':
    main()
