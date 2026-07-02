import math
import numpy as np
import sympy
from sympy import mobius
import matplotlib.pyplot as plt
import os

GAMMA = 0.57721566490153286060651209
LOG_2PI = math.log(2 * math.pi)

def frac(x):
    return x - math.floor(x)

def V_vasyunin(h, k):
    if k == 1:
        return 0.0
    val = 0.0
    for m in range(1, k):
        val += frac(h * m / k) * (1.0 / math.tan(math.pi * m / k))
    return val

def compute_components(N):
    c = np.zeros(N + 1)
    for k in range(1, N + 1):
        c[k] = -mobius(k) * (1 - k / (N + 1))
        
    linear_comp = 0.0
    for k in range(1, N + 1):
        chi_rho = (math.log(k) + 1 - GAMMA) / k
        linear_comp += -2 * c[k] * chi_rho
        
    q_loggamma = 0.0
    q_logratio = 0.0
    q_cotangent = 0.0
    
    for h in range(1, N + 1):
        for k in range(1, N + 1):
            term = c[h] * c[k]
            
            # Log Gamma part
            lg = (LOG_2PI - GAMMA) / 2 * (1/h + 1/k)
            q_loggamma += term * lg
            
            # Log Ratio part
            if h != k:
                lr = (k - h) / (2 * h * k) * math.log(h / k)
            else:
                lr = 0.0
            q_logratio += term * lr
            
            # Cotangent part
            cot = -math.pi / (2 * h * k) * (V_vasyunin(h, k) + V_vasyunin(k, h))
            q_cotangent += term * cot

    residue = 0.0
    total = 1.0 + linear_comp + q_loggamma + q_logratio + q_cotangent + residue
    
    return {
        "N": N,
        "Linear": linear_comp,
        "Q_loggamma": q_loggamma,
        "Q_logratio": q_logratio,
        "Q_cotangent": q_cotangent,
        "Residue": residue,
        "Total": total,
        "Total_scaled": total * math.log(N + 2)
    }

Ns = [10, 20, 50, 100, 200, 500]
results = []

for N in Ns:
    print(f"Computing N={N}...")
    res = compute_components(N)
    results.append(res)
    
print("N\tLinear\tQ_loggamma\tQ_logratio\tQ_cotangent\tResidue\tTotal\tTotal*log(N+2)")
for r in results:
    print(f"{r['N']}\t{r['Linear']:.6f}\t{r['Q_loggamma']:.6f}\t{r['Q_logratio']:.6f}\t{r['Q_cotangent']:.6f}\t{r['Residue']:.6f}\t{r['Total']:.6f}\t{r['Total_scaled']:.6f}")

print("\nNormalized Diagnostics:")
print("N\tLin+1\tQ_tot\tLin+Q_tot+1\tQ_lg+Q_lr\tQ_cot/Tot")
for r in results:
    q_tot = r['Q_loggamma'] + r['Q_logratio'] + r['Q_cotangent']
    lin_plus_1 = r['Linear'] + 1.0
    tot_comb = lin_plus_1 + q_tot
    q_lg_lr = r['Q_loggamma'] + r['Q_logratio']
    q_cot_ratio = r['Q_cotangent'] / r['Total'] if r['Total'] != 0 else 0
    print(f"{r['N']}\t{lin_plus_1:.6f}\t{q_tot:.6f}\t{tot_comb:.6f}\t{q_lg_lr:.6f}\t{q_cot_ratio:.6f}")

# Plots
Ns_plot = [r['N'] for r in results]
logNs = [math.log(N) for N in Ns_plot]

plt.figure(figsize=(10, 6))
plt.plot(logNs, [r['Linear'] for r in results], marker='o', label='Linear')
plt.plot(logNs, [r['Q_loggamma'] for r in results], marker='o', label='Q_loggamma')
plt.plot(logNs, [r['Q_logratio'] for r in results], marker='o', label='Q_logratio')
plt.plot(logNs, [r['Q_cotangent'] for r in results], marker='o', label='Q_cotangent')
plt.axhline(-1, color='black', linestyle='--', label='y=-1')
plt.axhline(0, color='gray', linestyle='--')
plt.xlabel('log(N)')
plt.ylabel('Component Value')
plt.title('Components vs log(N)')
plt.legend()
plt.grid(True)
plt.savefig('docs/components_vs_logn.png')

plt.figure(figsize=(10, 6))
plt.plot(Ns_plot, [r['Total'] for r in results], marker='o', label='Total Energy')
plt.xlabel('N')
plt.ylabel('Energy')
plt.title('Total Energy vs N')
plt.legend()
plt.grid(True)
plt.savefig('docs/total_energy.png')

plt.figure(figsize=(10, 6))
plt.plot(Ns_plot, [r['Total_scaled'] for r in results], marker='o', label='Total * log(N+2)')
plt.xlabel('N')
plt.ylabel('Total * log(N+2)')
plt.title('Scaled Energy vs N')
plt.legend()
plt.grid(True)
plt.savefig('docs/scaled_energy.png')

