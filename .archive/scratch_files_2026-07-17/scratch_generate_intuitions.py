import re

content = """
    <section class="view-section active">
      <h2>Intuitions & Strategies</h2>
      <p style="font-size: 1.05rem; color: #475569; margin-bottom: 2rem;">
        How do we trace a proof from a vague idea to a formal theorem? By taking a <strong>Digital Humanities (DH)</strong> perspective on the Riemann Hypothesis corpus, we map over 160 years of mathematical intuitions not as isolated formulas, but as an interconnected ecosystem of intellectual lineage.
      </p>

      <div style="background: #f8fafc; padding: 2rem; border-radius: 8px; border-left: 4px solid #3b82f6; margin-bottom: 2rem;">
        <h3 style="color: #1e40af; margin-top: 0;">Our Formalization Route: The Functional Paradigm</h3>
        <p style="color: #334155; line-height: 1.6;">
          Why did we choose the <strong>Nyman–Beurling / Báez-Duarte</strong> strategy for our Lean 4 formalization? As the timeline below illustrates, the classical analytic and spectral routes require highly complex bounding and uncomputable operators. The functional analysis route, pioneered by Nyman, Beurling, and Báez-Duarte, translates the Riemann Hypothesis into a <em>density problem in a Hilbert space</em>. This allowed us to map the hypothesis onto discrete step functions, replacing infinite analytic continuation with computable, algebraic closure properties—making it the ideal algorithmic structure for formal verification.
        </p>
      </div>

      <div class="timeline" style="border-left: 3px solid #cbd5e1; margin-left: 1rem; padding-left: 2rem; position: relative;">

        <!-- 1. Bernhard Riemann -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #3b82f6; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1859 — Bernhard Riemann</h4>
          <em style="color: #64748b; font-size: 0.95rem;">The Critical Line and Symmetric Balance</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Riemann conjectured that it is "very likely" that all non-trivial zeros lie on the critical vertical line $\\Re(s) = 1/2$. This symmetric alignment implies that the fluctuations of prime numbers around their average density are perfectly balanced, behaving like the bounds seen in statistical random walks.</p>
        </div>

        <!-- 2. Adolf Piltz -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1884 — Adolf Piltz</h4>
          <em style="color: #64748b; font-size: 0.95rem;">The Generalized Riemann Hypothesis (GRH)</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Extended Riemann's conjecture to the Dirichlet $L$-functions $L(s, \\chi)$, hypothesizing their zeros also reside strictly on $\\Re(s) = 1/2$, guaranteeing optimal error terms for primes in arithmetic progressions.</p>
        </div>

        <!-- 3. Hilbert and Polya -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #8b5cf6; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1910s — David Hilbert & Aladar Pólya</h4>
          <em style="color: #64748b; font-size: 0.95rem;">The Spectral Interpretation</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Proposed that imaginary parts of the non-trivial zeros correspond to the eigenvalues of a self-adjoint (Hermitian) operator on a Hilbert space, embedding the hypothesis into theoretical physics.</p>
        </div>

        <!-- 4. Marcel Riesz -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1916 — Marcel Riesz</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Asymptotic Power Series Bounds</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Riesz proposed an equivalent analytic criterion based on the asymptotic behavior of a specific power series, conjecturing RH is true iff $\\sum_{k=1}^\\infty \\frac{(-x)^k}{k! \\zeta(2k+1)} = O(x^{-1/4})$.</p>
        </div>

        <!-- 5. George Polya -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1926–1927 — George Pólya</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Trigonometric Integral Hypotheses</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Studied the Fourier transform of the Riemann $\\Xi(t)$ function, proposing necessary and sufficient positivity conditions on integral equations to satisfy RH.</p>
        </div>

        <!-- 6. Andreas Speiser -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1934 — Andreas Speiser</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Zeros of the Derivative</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Proved RH is equivalent to the assertion that $\\zeta'(s)$ has no complex zeros with a real part strictly less than 1/2.</p>
        </div>

        <!-- 7. Pál Turán -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1948 — Pál Turán</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Approximative Partial Sums</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Attempted to find an algebraic finite barrier to zeros by studying the partial sums $S_N(s) = \\sum_{n=1}^N n^{-s}$.</p>
        </div>

        <!-- 8. Nicolaas Govert de Bruijn -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1950 — Nicolaas Govert de Bruijn</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Backwards Heat Flow Deformations</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Studied deformations of the $\\Xi$ function as a backwards heat equation, showing real zero properties are preserved under heat flow.</p>
        </div>

        <!-- 9. Arne Beurling and Bertil Nyman -->
        <div style="background: #eff6ff; padding: 1.5rem; border-radius: 6px; margin-bottom: 2.5rem; position: relative; margin-left: -1.5rem; border: 1px solid #bfdbfe;">
          <div style="position: absolute; left: -1.15rem; top: 1.75rem; width: 14px; height: 14px; background: #f59e0b; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1d4ed8; font-size: 1.15rem;">1950–1955 — Arne Beurling & Bertil Nyman <span style="font-size: 0.8rem; background: #3b82f6; color: white; padding: 2px 6px; border-radius: 4px; margin-left: 0.5rem; vertical-align: middle;">Our Formalization Base</span></h4>
          <em style="color: #3b82f6; font-size: 0.95rem;">Functional Completeness</em>
          <p style="color: #1e3a8a; margin-top: 0.5rem; line-height: 1.5;">The Nyman-Beurling criterion translates RH into a density problem in functional analysis. Nyman proved that RH is equivalent to the statement that the space of linear combinations of fractional parts $f(x) = \\sum c_k \\{\\theta_k/x\\}$ is dense in $L^2(0,1)$. Beurling extended this to the positive real line in $L^2(0, \\infty)$. This paradigm shift replaces analytic continuation with Hilbert space closure.</p>
        </div>

        <!-- 10. André Weil -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1952 — André Weil</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Explicit Formulas and Positivity</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Proved RH is equivalent to a positivity condition $\\sum_v W_v(g * g^*) \\ge 0$ on a distribution evaluating test functions constructed by convolution.</p>
        </div>

        <!-- 11. Arnaud Denjoy -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #10b981; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">Mid-20th Century — Arnaud Denjoy</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Random Parity and Coin Tosses</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Formulated a probabilistic heuristic where the parity of prime factors (Möbius function) behaves randomly like coin tosses, equating RH to a random walk bound $M(x) = O(x^{1/2+\\epsilon})$.</p>
        </div>

        <!-- 12. Hugh Montgomery -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #8b5cf6; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1973 — Hugh Montgomery</h4>
          <em style="color: #64748b; font-size: 0.95rem;">GUE and Eigenvalue Spacing</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Conjectured the statistical pair correlation of Riemann zeros matches the eigenvalue spacing of large random Hermitian matrices (GUE), linking number theory to quantum chaos.</p>
        </div>

        <!-- 13. Charles M. Newman -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1976 — Charles M. Newman</h4>
          <em style="color: #64748b; font-size: 0.95rem;">The "Barely True" Conjecture</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Formulated that if RH is true, it is "only barely so", predicting the de Bruijn-Newman constant satisfies $\\Lambda \\ge 0$ (proven by Rodgers and Tao in 2018).</p>
        </div>

        <!-- 14. Hugh Montgomery -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1980 — Hugh Montgomery</h4>
          <em style="color: #64748b; font-size: 0.95rem;">The Limit of Asymptotic Fluctuations</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Conjectured a precise scale for the maximum deviation of the prime-counting error term from its average.</p>
        </div>

        <!-- 15. Guy Robin -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1984 — Guy Robin</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Divisor Function Upper Bounds</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Translated RH into a pure arithmetic inequality: RH is equivalent to $\\sigma(n) < e^\\gamma n \\log\\log n$ for all $n > 5040$.</p>
        </div>

        <!-- 16. Louis de Branges -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1986 — Louis de Branges</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Hilbert Spaces of Entire Functions</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Conjectured RH would follow from a positivity condition on a Hilbert space of entire functions $H(E)$.</p>
        </div>

        <!-- 17. Katz and Sarnak -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #8b5cf6; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1999 — Nicholas Katz & Peter Sarnak</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Random Matrix Ensembles</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Expanded pair correlation to families of L-functions, linking low-lying zeros to scaling limits of classical compact matrix ensembles.</p>
        </div>

        <!-- 18. Alain Connes -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #8b5cf6; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1999 — Alain Connes</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Noncommutative Odele Class Absorption</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Proposed zeros appear as an "absorption spectrum" within a geometric space constructed from adele classes $\\mathbb{A}/\\mathbb{Q}^*$.</p>
        </div>

        <!-- 19. Berry and Keating -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #8b5cf6; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">1999 — Michael Berry & Jonathan Keating</h4>
          <em style="color: #64748b; font-size: 0.95rem;">The Classical Quantum Chaos Hamiltonian</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Conjectured the classical Hamiltonian $H = \\frac{1}{2}(xp + px)$, when quantized, possesses a spectrum corresponding exactly to the zeta zeros.</p>
        </div>

        <!-- 20. Keating and Snaith -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #8b5cf6; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">2000 — Jonathan Keating & Nina Snaith</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Moment Conjectures</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Proved L-functions "conspire" and statistically reflect random matrix structures through high-precision moments.</p>
        </div>

        <!-- 21. Jeffrey Lagarias -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">2002 — Jeffrey Lagarias</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Harmonic Number Bounds</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Refined Robin's divisor criterion: RH holds iff $\\sigma(n) < H_n + e^{H_n} \\log H_n$, where $H_n$ is the $n$-th harmonic number.</p>
        </div>

        <!-- 22. Luis Báez-Duarte -->
        <div style="background: #eff6ff; padding: 1.5rem; border-radius: 6px; margin-bottom: 2.5rem; position: relative; margin-left: -1.5rem; border: 1px solid #bfdbfe;">
          <div style="position: absolute; left: -1.15rem; top: 1.75rem; width: 14px; height: 14px; background: #f59e0b; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1d4ed8; font-size: 1.15rem;">2003 — Luis Báez-Duarte <span style="font-size: 0.8rem; background: #3b82f6; color: white; padding: 2px 6px; border-radius: 4px; margin-left: 0.5rem; vertical-align: middle;">Our Formalization Base</span></h4>
          <em style="color: #3b82f6; font-size: 0.95rem;">Discrete Fractional Part Approximations</em>
          <p style="color: #1e3a8a; margin-top: 0.5rem; line-height: 1.5;">Strengthened the Nyman-Beurling criterion by proving that one can restrict the parameters specifically to the discrete sequence $\\theta_k = 1/k$. He showed that the convergence of the discrete sequence of step functions $\\{1/(kx)\\}$ in $L^2(0, \\infty)$ is perfectly equivalent to the truth of the Riemann Hypothesis, effectively discretizing the problem for computation.</p>
        </div>

        <!-- 23. Farmer, Gonek, Hughes -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">2007 — Farmer, Gonek, Hughes</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Absolute Maximum Critical Bounds</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Conjectured the absolute maximum size of the zeta function on the critical line.</p>
        </div>

        <!-- 24. Bender, Brody, Müller -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #8b5cf6; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">2017 — Bender, Brody, Müller</h4>
          <em style="color: #64748b; font-size: 0.95rem;">PT-Symmetric Quantum Operators</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Conjectured a pseudo-Hermitian quantum operator invariant under space-time reflection has eigenvalues that are entirely real and match RH zeros.</p>
        </div>

        <!-- 25. Connes and Moscovici -->
        <div style="margin-bottom: 2.5rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #8b5cf6; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">2022 — Alain Connes & Henri Moscovici</h4>
          <em style="color: #64748b; font-size: 0.95rem;">The UV Prolate Spectrum</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Discovered eigenvalues of the prolate spheroidal wave operator are asymptotically similar to the squares of zeta zeros.</p>
        </div>

        <!-- 26. Alain Connes -->
        <div style="margin-bottom: 1rem; position: relative;">
          <div style="position: absolute; left: -2.65rem; top: 0.25rem; width: 14px; height: 14px; background: #cbd5e1; border-radius: 50%; border: 3px solid white;"></div>
          <h4 style="margin: 0; color: #1e293b; font-size: 1.15rem;">2026 — Alain Connes</h4>
          <em style="color: #64748b; font-size: 0.95rem;">Euler Product Extremization Limits</em>
          <p style="color: #475569; margin-top: 0.5rem; line-height: 1.5;">Proposed extremizing a restriction of the Weil quadratic form using finite Euler products, showing approximating values lie exactly on the critical line.</p>
        </div>

      </div>
    </section>
"""

with open('doc/html/js/app.js', 'r') as f:
    app_content = f.read()

# Replace the body of renderIntuitions()
pattern = re.compile(r'function renderIntuitions\(\) \{.*?\n\}', re.DOTALL)
replacement = f'function renderIntuitions() {{\n  return `{content}`;\n}}'
app_content = pattern.sub(replacement, app_content)

with open('doc/html/js/app.js', 'w') as f:
    f.write(app_content)
