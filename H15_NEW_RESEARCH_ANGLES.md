# H15 New Research Angles: Analysis of Expanded Corpus
**Date:** 2026-07-15  
**Trigger:** 27 new papers added; H15-classified papers now include alternative techniques

---

## Current H15 Status Recap

**Blocked Route:** Direct analytic approach via DFI/Bettin–Chandee (bound 8× too weak)

**Missing Piece:** Estermann/Kuznetsov machinery for modulus-dependent amplitude estimation $\beta_q(b)$ under sign oscillations.

**Decision:** Research-only (not formalized). But with expanded corpus, three NEW angles emerge.

---

## Angle 1: Character Sum Approach (NEW)

### Hypothesis
The Möbius/period-function bilinear correlation can be reformulated as a **weighted Dirichlet character sum**, enabling leverage of classical character sum bounds.

### Papers to Investigate
- **1409.1634:** "Dirichlet Character Sums" (Beck et al., 2014) — currently H13, but contains character bounds
- **1601.06839:** "Reciprocal Relations and Theorems" (Auli, Bayad, Beck, 2017) — explicitly links reciprocal sums to character theory

### Key Insight
Dirichlet characters encode modular structure. If we can write:
$$\sum_{g \leq N} \mu(g)^2 \cdot \omega(g) = \sum_{q} \chi(q) \cdot S_q(N)$$
where $\chi$ is a character and $S_q$ is a controlled partial sum, then **character sum bounds automatically encode the modular-dependent amplitude structure**.

### Technical Route
1. **Factorization via characters:** Express $\mu(g)$ evaluation mod $q$ using character decomposition
2. **Orthogonalit relations:** Use $\sum_\chi \chi(a)\overline{\chi(b)} = \phi(q) \cdot \mathbb{1}_{a \equiv b \pmod q}$ to isolate modular contributions
3. **Character sum bounds:** Apply classical bounds (e.g., Pólya–Vinogradov, Montgomery–Vaughan) to each character's contribution
4. **Cancellation assembly:** Show that the character-wise bounds **automatically give the O(1/log N) when aggregated**

### Why This Might Work
- Avoids Estermann machinery entirely (shifts to character theory, which is in Mathlib)
- Reciprocity laws automatically encode the sign oscillations
- Character sums have tight bounds tailored to modular structure (exactly what we need)

### Lean Feasibility
✅ **HIGH** — Character sums are standard in analytic number theory; bounds exist in literature.

---

## Angle 2: Automorphic Forms / GL(2) Route (NEW)

### Hypothesis
The bilinear cotangent cancellation encodes the **spectral properties of GL(2) automorphic forms**, specifically the Fourier coefficients of Eisenstein series and their cancellation.

### Papers to Investigate
- **1503.05121:** "Fourier Analysis on GL(2)" (2015) — representation theory angle on Fourier expansion
- **1807.08249:** "L-Functions and Modular Forms" (2018) — connects L-functions to modular structure

### Key Insight
Automorphic forms on GL(2) are exactly the objects that encode:
- Modular structure (via the underlying lattice)
- Functional equations (via the Mellin transform)
- Character theory (via Hecke eigenvalues)

The Nyman–Beurling period function $\psi_\theta(x) = \{1/x\}$ might have a natural automorphic interpretation as a **coefficient of an Eisenstein series or theta series**.

### Technical Route
1. **Identify the automorphic form:** Find $F \in L^2(\Gamma \backslash GL(2, \mathbb{R})^+)$ such that $\psi_\theta$ is a coefficient of $F$
2. **Spectral decomposition:** Write $F = \sum_\phi c_\phi \phi$ where $\phi$ ranges over automorphic spectrum
3. **Cancellation from orthogonality:** Use Petersson inner product to show that **cross-term cancellation is automatic from spectral orthogonality**
4. **Bound via L-function growth:** Apply bounds on $L(1/2 + it, \pi)$ to control the cancellation rate

### Why This Might Work
- Automorphic forms ALREADY encode modular structure, zero distribution, and functional equations
- Eisenstein series have explicit formulas (easier than digging for Estermann machinery)
- The cancellation might simply be a **consequence of spectral orthogonality**, not a new result

### Lean Feasibility
⚠️ **MEDIUM** — Automorphic forms exist in some Mathlib/research formalization, but GL(2) machinery is sparse. Requires careful porting.

---

## Angle 3: Kuznetsov Trace Formula / Spectral Method (NEW)

### Hypothesis
The Kuznetsov trace formula (which we identified as missing) might be **avoided entirely** by working at the spectral level rather than the pointwise level. Instead of estimating $\beta_q(b)$ pointwise, estimate its **L²-norm or spectral norm**.

### Papers to Investigate
- **1601.06839:** Reciprocal relations (might contain trace formula insights)
- **1807.08249:** L-functions and modular forms (trace formulas connect L-functions to automorphic spectrum)

### Key Insight
The Kuznetsov trace formula is:
$$\sum_{\text{automorphic}} \lambda_\pi(n) \lambda_\pi(m) = \delta_{n,m} + \text{(oscillating terms)}$$

Instead of asking "what is $\beta_q(b)$ pointwise?", ask "what is $\|\beta_q\|_2^2$ spectrally?". This might have a **closed-form answer via trace formulas**, bypassing the pointwise estimation entirely.

### Technical Route
1. **L² formulation:** Reformulate the O(1/log N) problem as $\|\sum_q \mu(q)^2 \cdot \text{(error)} \|_2 \leq C/\log N$
2. **Plancherel/Parseval:** Expand the squared norm using orthogonal decomposition
3. **Trace formula application:** Apply Kuznetsov (or a simpler variant) to the sum of squared contributions
4. **Bound harvest:** Show that the trace formula automatically gives the O(1/log N)

### Why This Might Work
- Shifts from pointwise to spectral, where cancellation is automatic
- Kuznetsov formula is an identity (not an estimate), so it gives exact results
- The O(1/log N) might emerge from **spectral gap properties** of Hecke operators, not amplitude estimation

### Lean Feasibility
⚠️ **LOW-MEDIUM** — Trace formulas are advanced; spectral theory formalization is sparse. But worth exploring conceptually.

---

## Angle 4: Conditional Routes / Numerical Validation

### Hypothesis
Since we've proven the exact centered-bilinear kernel and the DFI/Bettin–Chandee gap, perhaps we can:

1. **Prove the O(1/log N) bound conditionally** (assuming some reasonable conjecture on amplitudes)
2. **Verify numerically to 5+ decimal places** that the bound holds for N up to 10⁶

This creates a **strong empirical foundation** for expert escalation and might guide the proof strategy.

### Papers to Investigate
- **2607.09110:** "Phase 1 Diagnostics for H15 Kernel" (new, 2026) — might contain numerical validation
- **2607.09797:** "Recent Advances in RH Approximations" (new, 2026) — might have computational insights
- **2607.04632:** "Möbius Correlations and Cancellation" (new, 2026) — might show empirical cancellation

### Technical Route
1. **Conditional formulation:** Assume $\beta_q(b) \leq B / \sqrt{q}$ (a reasonable estimate)
2. **Compute the implied bound:** Show that this assumption gives exactly O(1/log N)
3. **Numerical validation:** For N = 10, 100, 1000, 10000, compute actual cancellation vs. theoretical bound
4. **Report findings:** If empirics match theory, highlight which assumption(s) are tight

### Why This Might Work
- Experts are often guided by empirical evidence
- A conditional proof + numerical validation is a **publishable research contribution** even if not fully unconditional
- Guides future proof work (shows exactly where tightness lies)

### Lean Feasibility
✅ **HIGH** — Lean can check numerical bounds; empirical validation is straightforward.

---

## Proposed Research Agenda (4–8 weeks)

| Week | Angle | Action | Deliverable |
|------|-------|--------|-------------|
| **1** | **Angle 1 (Chars)** | Deep-read 1409.1634 + 1601.06839 | Character sum factorization sketch |
| **2** | **Angle 1 (Chars)** | Attempt Dirichlet character reformulation | Proof outline or refutation |
| **3** | **Angle 2 (Auto)** | Study 1503.05121 + 1807.08249 | Automorphic form identification (if exists) |
| **4** | **Angle 2 (Auto)** | Sketch GL(2) spectral orthogonality argument | Plausibility assessment |
| **5** | **Angle 3 (Spectral)** | Literature review: trace formulas in modern form | Applicable formula(s) identified |
| **6** | **Angle 4 (Conditional)** | Conditional formulation + numerical validation | Empirical report (N up to 10⁶) |
| **7** | **Synthesis** | Compare all four angles; identify most promising | Revised H15 strategy memo |
| **8** | **Documentation** | Write research findings; prepare expert brief | Publication-ready research note |

---

## Success Criteria

✅ **Minimal:** One of the four angles yields a **proof sketch** with clear remaining gaps  
✅ **Strong:** Two angles converge on the **same mechanism** (suggests deep truth)  
✅ **Exceptional:** Full O(1/log N) proof via any angle  

---

## Why This Timing Is Good

1. **Corpus expanded:** 27 new papers provide fresh perspectives
2. **H15 gap identified:** We know EXACTLY what's missing (Estermann/Kuznetsov)
3. **Three new H15 papers (2026):** May contain recent breakthroughs
4. **Character sum + automorphic form literature:** Well-developed, in Mathlib/arXiv
5. **Project status:** 67% complete — can afford 4–8 week exploratory investment

---

## Risk Assessment

| Angle | Risk | Mitigation |
|-------|------|-----------|
| **Chars** | Character sum bounds might be weaker than needed | Validate on small cases; check literature |
| **Auto** | GL(2) machinery not in Mathlib | Focus on conceptual sketch, not formalization |
| **Spectral** | Trace formulas might not simplify the problem | Start with literature review to assess |
| **Conditional** | Empirical validation is not a proof | Position as "research foundation" not solution |

---

## Recommendation

**Start with Angle 1 (Character Sums)** — it's the most self-contained, builds on existing H13 work (Dirichlet characters), and has the highest Lean feasibility. If character sums don't close the gap, pivot to Angle 4 (conditional + numerical validation) to build empirical foundation for expert escalation.

---

**Status:** READY FOR RESEARCH EXPLORATION ✅
