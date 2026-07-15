# H15 Phase 1: Diagnostic Research Programme

**Objective:** Identify which decomposition most clearly reveals the cancellation structure in H15  
**Timeline:** 1–2 weeks (parallel with H14 Aristotle work)  
**Input:** Classical H15 conjecture + 7 decomposition methods  
**Output:** Empirical evidence showing which decomposition yields cleanest cancellation  
**Success:** One decomposition emerges as the winning structure for Phase 2 formalization  

---

## THE H15 PROBLEM (Reminder)

Prove or disprove:
$$\left|\sum_{h,k \leq N} \mu(h) \mu(k) \left(1 - \frac{h}{N+1}\right)\left(1 - \frac{k}{N+1}\right) K(h,k)\right| \leq \frac{C}{\log N}$$

where $K(h,k)$ is the quadratic interaction kernel from Vasyunin/BBLS machinery.

**Key fact:** The cancellation is **global and signed**. It's hidden in how the signs of $\mu(h) \mu(k)$ interact with the kernel weights. Our job: find the decomposition that makes this cancellation visible.

---

## SEVEN DECOMPOSITIONS (Run All Seven)

### Decomposition 1: GCD Stratification

**Idea:** Group pairs $(h,k)$ by $d = \gcd(h,k)$. Within each stratum, analyze cancellation.

**Protocol:**
1. For each $d \in \{1, 2, 3, \ldots, 20\}$:
   - Count pairs: $\#\{(h,k) : h,k \leq N, \gcd(h,k) = d\}$
   - Compute partial sum: $S_d = \sum_{\gcd(h,k)=d} \mu(h)\mu(k) \left(1-\frac{h}{N+1}\right)\left(1-\frac{k}{N+1}\right) K(h,k)$
   - Record $|S_d|$ and ratio $|S_d| / S_{total}$

2. Plot: $\log d$ vs. $\log |S_d|$ (expect decay? clustering?)

3. **Success indicator:** 
   - If one stratum dominates: cancellation is gcd-localized
   - If strata scatter: cancellation is more global (move to other decompositions)

**Numerical test (N=100):**
```
d=1:   |S_1| = ?  (coprime pairs)
d=2:   |S_2| = ?
...
d=20:  |S_20| = ?
Sum:   |S_total| = ?
```

**Expected outcome:** Does the bound $1/\log N$ emerge from this stratification?

---

### Decomposition 2: Farey Cell Binning

**Idea:** Use Farey sequences to partition the $(h/N, k/N)$ plane into cells. Each cell is a fundamental domain of bounded complexity.

**Protocol:**
1. Generate Farey sequence $F_N$ (all reduced fractions $a/b$ with $b \leq N$, sorted)
2. For each cell $(F_i, F_{i+1})$ (a Farey neighbor pair):
   - Count lattice points $(h,k)$ in this "hyperbolic" cell
   - Compute partial sum $S_{cell}$ restricted to this cell
   - Record $|S_{cell}|$

3. Plot: Cell index vs. $|S_{cell}|$ (expect cancellation within cells?)

4. **Success indicator:**
   - If cancellation is strongest within Farey cells: this is the structure
   - If cancellation spreads across cells: move to next decomposition

**Numerical test (N=100):**
```
Farey cells:
Cell 1 (0/1 to 1/100):   |S_cell| = ?
Cell 2 (1/100 to 1/99):  |S_cell| = ?
...
Sum over all cells: |S_total| = ?
```

**Expected outcome:** Do Farey cells isolate cancellation regions?

---

### Decomposition 3: Dyadic Block Decomposition

**Idea:** Partition $[1, N]$ into dyadic blocks: $[2^j, 2^{j+1})$ for $h$ and $k$ independently.

**Protocol:**
1. For each dyadic pair of blocks $(2^i, 2^{i+1}) \times (2^j, 2^{j+1})$:
   - Restrict sum to pairs with $h \in [2^i, 2^{i+1})$ and $k \in [2^j, 2^{j+1})$
   - Compute $S_{i,j}$ (partial sum in block)
   - Record $|S_{i,j}|$

2. Plot: Heat map of $\log |S_{i,j}|$ vs. $(i,j)$ (expect diagonal dominance? anti-diagonal?)

3. **Success indicator:**
   - If diagonal blocks cancel most strongly: structure is "self-interaction"
   - If off-diagonal: structure is more complex
   - If random: move to next

**Numerical test (N=128, 7 dyadic levels):**
```
Block structure:
         j=0    j=1    j=2   ...
i=0:    |S_00| |S_01| |S_02| ...
i=1:    |S_10| |S_11| |S_12| ...
...
```

**Expected outcome:** Which block structure shows clearest cancellation pattern?

---

### Decomposition 4: Estermann Main vs. Error Terms

**Idea:** Lift to Estermann/Mellin framework. Separate the "+1" main term from the remainder.

**Protocol:**
1. Write $K(h,k)$ as an integral involving the Estermann zeta function
2. Decompose: $K(h,k) = K_{main}(h,k) + K_{error}(h,k)$
3. Compute separately:
   - $S_{main} = \sum_{h,k} \mu(h)\mu(k) (...) K_{main}(h,k)$
   - $S_{error} = \sum_{h,k} \mu(h)\mu(k) (...) K_{error}(h,k)$

4. Record: $|S_{main}|$, $|S_{error}|$, and ratio $|S_{error}| / |S_{main}|$

5. **Success indicator:**
   - If error term is tightly controlled: Estermann route looks viable
   - If error explodes: Estermann route is harder

**Numerical test (N=100):**
```
Main term contribution:  |S_main| = ?
Error term contribution: |S_error| = ?
Ratio:                   |S_error|/|S_main| = ?
```

**Expected outcome:** Does Estermann framework isolate the hard cancellation?

---

### Decomposition 5: Coprime vs. Non-Coprime Pairs

**Idea:** Separate $\gcd(h,k)=1$ (coprime) from $\gcd(h,k) > 1$ (non-coprime). Do they cancel together or separately?

**Protocol:**
1. Compute:
   - $S_{coprime} = \sum_{\gcd(h,k)=1, h,k \leq N} \mu(h)\mu(k) (...) K(h,k)$
   - $S_{non-coprime} = \sum_{\gcd(h,k)>1, h,k \leq N} \mu(h)\mu(k) (...) K(h,k)$

2. Record: $|S_{coprime}|$, $|S_{non-coprime}|$, and their ratio

3. **Success indicator:**
   - If coprime pairs dominate and cancel: structure is simpler
   - If non-coprime essential to cancellation: structure is more complex

**Numerical test (N=100):**
```
Coprime pairs:     |S_coprime| = ?
Non-coprime pairs: |S_non-coprime| = ?
Total:             |S_total| = ?
```

**Expected outcome:** Can we isolate the cancellation to coprime pairs?

---

### Decomposition 6: Continued-Fraction Depth

**Idea:** Group pairs by the depth of the continued-fraction expansion of $h/k$. Simple fractions (short CF) vs. complex ones (long CF).

**Protocol:**
1. For each fraction $h/k$ in reduced form, compute CF depth: $d(h/k) = \text{length of continued fraction}$
2. Compute partial sums grouped by depth:
   - $S_1 = \sum_{d(h/k)=1} \mu(h)\mu(k) (...) K(h,k)$ (e.g., $h/k = p/q$ where $p$ is $q±1$)
   - $S_2 = \sum_{d(h/k)=2} \mu(h)\mu(k) (...) K(h,k)$
   - etc.

3. Plot: CF depth vs. $|S_{depth}|$

4. **Success indicator:**
   - If short-CF fractions dominate: structure is on "simple" rationals
   - If all depths equally important: structure is global

**Numerical test (N=100):**
```
CF depth 1: |S_1| = ?
CF depth 2: |S_2| = ?
...
```

**Expected outcome:** Does cancellation concentrate on rational numbers with short CF?

---

### Decomposition 7: Fourier/Bernoulli Mode Decomposition

**Idea:** Expand $K(h,k)$ and weights in Fourier/Bernoulli modes. Which frequencies carry the cancellation?

**Protocol:**
1. Write weights $\left(1 - \frac{h}{N+1}\right)$ as a Fourier series (or Bernoulli polynomial expansion)
2. For each frequency $\omega$, compute:
   - $S_\omega = \sum_{h,k} \mu(h)\mu(k) (\text{weight}_\omega(h)) (\text{weight}_\omega(k)) K(h,k)$

3. Plot: Frequency $\omega$ vs. $|S_\omega|$ (expect dominant frequency?)

4. **Success indicator:**
   - If one frequency dominates: cancellation is on a single mode
   - If broad spectrum: cancellation is more subtle

**Numerical test (N=100):**
```
ω=0:  |S_0| = ?
ω=1:  |S_1| = ?
ω=2:  |S_2| = ?
...
```

**Expected outcome:** Which Fourier mode most clearly shows the cancellation?

---

## REPORTING TEMPLATE (For Each Decomposition)

For each of the 7 decompositions, provide:

```
Decomposition: [Name]
===============================================

Data collected (N=100, 500, 1000):
- [Key metric 1]: [values]
- [Key metric 2]: [values]
- [Summary: does cancellation cluster or spread?]

Plots generated:
- [Description of plot 1]
- [Description of plot 2]

Observations:
- Does this decomposition isolate cancellation?
- What's the decay rate (if visible)?
- How does it compare to target O(1/log N)?

Success indicator:
- [ ] Strong evidence this is the right decomposition
- [ ] Moderate evidence; inconclusive
- [ ] Weak evidence; move to next decomposition

Next step if successful:
- [What this would unlock for Phase 2]
```

---

## EXPECTED OUTCOMES & SELECTION CRITERIA

**Winning decomposition** is the one that:
1. Cleanest shows cancellation (one or few regions where cancellation is visible)
2. Matches or approaches $O(1/\log N)$ target in that region
3. Provides a clear **formalization roadmap** (how to state it in Lean)
4. Suggests a concrete proof strategy (which classical machinery to apply)

**Possible winners:**
- **Decomposition 2 (Farey cells):** → H15 Route 2 (reciprocity/Bettin-Drappeau)
- **Decomposition 4 (Estermann):** → H15 Route 1 (contour remainder bounds)
- **Decomposition 7 (Fourier modes):** → H15 Route 3 (Dirichlet polynomial energy)

**If no clear winner emerges:**
- Run hybrid: combine two decompositions (e.g., Estermann + Farey)
- Return to theory: consult papers on Bettin-Conrey, BBLS, modern RH approaches

---

## TIMELINE & EFFORT

**Phase 1a (Setup):** 2–3 days
- Code up all 7 decompositions
- Generate N=100 baseline data
- Create plotting infrastructure

**Phase 1b (Exploration):** 5–7 days
- Run each decomposition on N=100, 500, 1000
- Collect and visualize data
- Identify emergent patterns

**Phase 1c (Validation):** 2–3 days
- Test winning decomposition on larger N (if needed)
- Cross-check against papers (Bettin-Conrey, BBLS, etc.)
- Write up findings

**Total:** 1–2 weeks

---

## SUCCESS CRITERIA FOR PHASE 1

✅ **Phase 1 is complete when:**
1. All 7 decompositions have been tested (N≥500)
2. One or two decompositions show clear cancellation clustering
3. Empirical evidence supports one of the three proof routes
4. A formalization roadmap is visible (which lemmas matter, what structure to encode)

✅ **Phase 2 can start when:**
- Decomposition choice is made
- Mathematical structure is understood
- Lean formalization skeleton is sketched (no proofs, just definitions + sorry)

---

## RESOURCES

**Classical papers (in corpus):**
- Bettin-Conrey (1111.0931): period functions, reciprocity
- BBLS (1401.2932 area): Estermann machinery, error term analysis
- Farey/hyperbolic (1401.3150): geometric structure

**Code templates (to adapt):**
- Möbius sum: standard, in any NT library
- Kernel K(h,k): formalize from Vasyunin/BBLS paper
- Farey sequences: classical algorithm
- Fourier expansion: FFT-based or analytical

---

## PARALLEL EXECUTION NOTE

**This runs in parallel with H14 Aristotle work:**
- H14 Borel-Jensen: Aristotle (days 1–4)
- H14 Perron: Aristotle (days 1–4)
- H15 Phase 1: You, diagnostics (days 1–10)

By day 10–14, you have:
- ✅ H14 complete (from Aristotle)
- ✅ H15 structure identified (from Phase 1)
- 🚀 Ready for Phase 2 (formalization + Phase 3 route selection)

---

**This Phase 1 diagnostic programme turns theory into empirical evidence.**

It doesn't prove H15, but it reveals which decomposition is worth formalizing. That's the gateway to a genuine proof attempt.

