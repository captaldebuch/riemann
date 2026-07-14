import sys
import os
import math
import numpy as np
from fractions import Fraction
import matplotlib.pyplot as plt

# Import from existing script
sys.path.insert(0, os.path.dirname(__file__))
from gram_matrix_search import compute_gram_matrix

def exact_inner_product(k):
    m = k + 1
    gamma = 0.57721566490153286
    return (math.log(m) + 1.0 - gamma) / m

def compute_numeric_energy(N):
    G = compute_gram_matrix(N)
    
    l = np.zeros(N)
    for k in range(N):
        l[k] = exact_inner_product(k)
        
    # Solve G c = l
    # Since G is ill-conditioned, we use SVD/pinv or high precision. 
    # Let's try np.linalg.solve first, if it fails, use pinv.
    cond = np.linalg.cond(G)
    try:
        c = np.linalg.solve(G, l)
    except np.linalg.LinAlgError:
        c = np.linalg.pinv(G) @ l
        
    energy = 1.0 - 2 * np.dot(c, l) + np.dot(c, G @ c)
    return energy, c, cond

def main():
    Ns = [10, 20, 50, 75, 100, 150, 200, 300, 500]
    energies = []
    
    print(f"{'N':<5} | {'E_N':<20} | {'E_N * log(N+2)':<20} | {'E_N * log(N+2)^2':<20} | {'Cond Number':<15}")
    print("-" * 90)
    
    results = []
    
    for N in Ns:
        E, c, cond = compute_numeric_energy(N)
        energies.append(E)
        
        logN2 = math.log(N + 2)
        E_log = E * logN2
        E_log2 = E * (logN2 ** 2)
        E_sqrt_log = E * math.sqrt(logN2)
        
        print(f"{N:<5} | {E:<20.8e} | {E_log:<20.8f} | {E_log2:<20.8f} | {cond:<15.2e}")
        
        results.append({
            'N': N,
            'E': E,
            'c': c
        })
        
    # Plotting
    plt.figure(figsize=(10, 6))
    Ns_plot = np.array(Ns)
    Es_plot = np.array(energies)
    
    plt.plot(Ns_plot, Es_plot, 'o-', label='E_N')
    plt.plot(Ns_plot, Es_plot * np.log(Ns_plot + 2), 's-', label='E_N * log(N+2)')
    plt.plot(Ns_plot, Es_plot * np.log(Ns_plot + 2)**2, 'd-', label='E_N * log(N+2)^2')
    plt.plot(Ns_plot, Es_plot * np.sqrt(np.log(Ns_plot + 2)), '^-', label='E_N * sqrt(log(N+2))')
    
    plt.yscale('log')
    plt.xlabel('N')
    plt.ylabel('Value')
    plt.title('Báez-Duarte Energy Decay Rates')
    plt.legend()
    plt.grid(True)
    plt.savefig(os.path.join(os.path.dirname(__file__), 'decay_rates.png'))
    print("Saved plot to decay_rates.png")
    
    # Plot coefficients
    plt.figure(figsize=(12, 8))
    for res in results:
        N = res['N']
        c = res['c']
        plt.plot(np.arange(1, N+1)/N, c, label=f'N={N}')
        
    plt.xlabel('k/N')
    plt.ylabel('c_k')
    plt.title('Optimal Coefficients Profile (c_k vs k/N)')
    plt.legend()
    plt.grid(True)
    plt.savefig(os.path.join(os.path.dirname(__file__), 'coefficients_profile.png'))
    print("Saved plot to coefficients_profile.png")

if __name__ == '__main__':
    main()
