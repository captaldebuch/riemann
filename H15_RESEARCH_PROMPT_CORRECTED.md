# SUPERSEDED: H15 LINEAR-TAPER RESEARCH PROMPT

> This linear-taper protocol has been retired. The active protocol is
> `H15_BCF_LOG_TAPER_RESEARCH_PROTOCOL.md`, using the Bettin--Conrey--Farmer
> logarithmic taper. Do not use the targets or empirical data below for new
> H15 work.

# H15 QUADRATIC MÖBIUS-VASYUNIN CANCELLATION: RETIRED RESEARCH PROMPT

## Problem: Prove RH Through Nyman–Beurling Energy

The Riemann Hypothesis is equivalent (by Nyman–Beurling–Báez-Duarte criterion) to bounding the squared defect energy:

$$E_N = 1 + 2L_N + \Lambda_\gamma(N) + Q_N = \left\|\chi - \sum_{n\le N}c_N(n)\rho_n\right\|_2^2$$

where the quadratic component Q_N encodes genuine **bilinear Möbius interaction**, not a pointwise maximum.

**Correct Target (Not O(1/log² N)):**

$$|\Lambda_\gamma(N)| + |Q_N - 1 + 2(L_N+1)| \le \frac{C}{\log(N+2)} \tag{H15}$$

Proving this unconditionally would prove RH. This is not expected to follow mechanically from PNT-strength Möbius decay.

---

## The Exact Objects

### Weights
$$w_N(n) = 1 - \frac{n}{N+1}, \quad c_N(n) = -\mu(n)w_N(n)$$

### Kernel (Frozen in QuadraticInteraction.lean)
$$K(h,k) = \frac{k-h}{2hk}\log\frac{h}{k} - \frac{\pi}{2hk}\bigl(V(h,k)+V(k,h)\bigr)$$

where
$$V(p,q) = \int_0^\infty B_1\left(\frac{pt}{q}\right)\frac{dt}{t^2}$$
(Bernoulli polynomial integral, BBLS Prop 48).

### The Quadratic Sum
$$Q_N = \sum_{h,k\le N} c_N(h)c_N(k)K(h,k)$$

### Linear Component
$$L_N = \sum_{n\le N} \mu(n)w_N(n) \frac{\log n + 1 - \gamma}{n}$$

---

## Empirical Diagnostic (N=1000)

**Verified Computation:**
```
Q_1000 = 1.0042264
Q_1000 - 1 = 0.0042264

Decomposition by gcd structure:
  Coprime (gcd=1):     -0.3023752
  Non-coprime (gcd>1): +1.3066016
  
Mass balance:
  Positive terms: ~625.98
  Negative terms: ~-624.97
  Net: ~1.0
```

**Critical Observation:** The cancellation between ~625 and ~-625 is real. Any approach that takes absolute values loses this structure and cannot achieve O(1/log N).

**Source:** `phase15_quadratic_interaction_diagnostics.py:190`

---

## Why O(1/log² N) Is Impossible

**Theorem (Bettin–Conrey–Farmer, arXiv:1211.5191):**

The unconditional lower bound on the optimal squared Nyman–Beurling defect is **Ω(1/log N)**, not Ω(1/log² N).

Therefore:
- ✅ O(1/log N) is mathematically viable
- ❌ O(1/log² N) violates the unconditional lower bound
- The archived `H15CenteredAggregateEstimate` target is impossible and should be retired

---

# RESEARCH TASK: THREE ROUTES WITH HONEST ASSESSMENT

Investigate each route. Report not what you hope to find, but what the mathematics actually says.

For each route:
1. **State the exact theorem** to be proved
2. **Trace classical sources** (where does each component come from?)
3. **Identify blockers** (where does the proof actually get stuck?)
4. **Assess tractability** (what is the honest difficulty?)
5. **Recommend action** (pursue, validate, or retire?)

---

## ROUTE 1: Estermann/BBLS Contour Remainder

### Objective
Extract the bilinear Q_N from rational autocorrelation A(λ) via exact Mellin inversion, then bound via contour deformation.

### Classical Infrastructure (Fully Available)

From Báez-Duarte–Balazard–Landreau–Saias (arXiv:math/0306251):

**Proposition 48:**
$$\sum_{m\ge1}\frac{B_1(mp/q)}{m} = \frac{\pi}{2q}V(p,q)$$

**Proposition 86 (Mellin of multiplicative autocorrelation):**
$$\mathcal{M}A(s) = -\frac{\zeta(-s)\zeta(s+1)}{s(s+1)}$$

**Proposition 89 (Exact rational autocorrelation):**
All needed identities in terms of V(p,q) + V(q,p).

The Estermann function has meromorphic continuation, functional equation, and polynomial vertical growth for fixed rational h/k.

### The Proposed Path
1. Combine the entire h,k ≤ N sum before deforming
2. Obtain a two-variable Mellin/Perron representation
3. Extract centered main terms
4. Shift one finite contour (not N separate shifts)
5. Bound the remainder uniformly in N

### Critical Blockers

**Blocker 1: Uniform Boundedness Over All Rationals**
- BBLS provides vertical growth for each fixed h/k
- Does NOT supply modulus-uniform bound after summing all h,k ≤ N
- The aggregate Dirichlet polynomial approximates 1/ζ(s)

**Blocker 2: Zero Encounters**
- Moving the contour through the critical strip encounters zeros of ζ(s)
- De la Vallée Poussin's zero-free region near Re s = 1 does not control this
- Standard contour bounds fail

**Blocker 3: Cancellation Destruction**
- Bounding the Estermann remainder separately for ~625 rational pairs h/k
- Destroys the observed ~625 + ~(-625) = ~1 cancellation
- Individual bounds:  ∑ |remainder_hk| is too large

**The Core Issue:**
The remainder integral, when summed over all h,k ≤ N, encounters ζ zeros and cannot be controlled to O(1/log N) using existing Estermann machinery.

### Assessment

| Dimension | Rating | Reasoning |
|-----------|--------|-----------|
| Conceptual clarity | 4/5 | Exact Mellin/residue theory exists and is sound |
| Classical foundation | 3/5 | Pointwise theory works; aggregate uniformity does not |
| Technical difficulty | 5/5 | Missing bound is RH-level hard |
| Success likelihood | **1/5** | Contour shift cannot capture global cancellation |

### Recommendation

✅ **USE FOR VERIFICATION ONLY:** Route 1 extracts the exact main terms and audits classical theorems. It is excellent for confirming that K(h,k) is correctly formulated.

❌ **DO NOT USE AS PRIMARY PROOF:** Cannot deliver O(1/log N) bound unconditionally.

### If You Pursue This Anyway

**Next step:** Derive a single exact Mellin integral for E_N with all N-dependence explicit:
$$\frac{1}{2\pi}\int_{\mathbb{R}} \frac{|1-\zeta(\tfrac12+it)A_N(\tfrac12+it)|^2}{\tfrac14+t^2}\,dt$$

If the integral reduces to this form, you have produced an RH-equivalent reformulation, not a new estimate.

---

## ROUTE 2: Iterated Reciprocity + Reciprocal Phases [RECOMMENDED]

### Objective
Stratify by gcd, apply Vasyunin/Bettin–Conrey reciprocity to coprime pairs, then match the resulting phases with Duke–Friedlander–Iwaniec (DFI) bilinear Kloosterman estimates.

### Classical Infrastructure (Partially Available)

**Stratification:** Write h = ga, k = gb where g = gcd(h,k). Non-squarefree strata vanish formally; squarefree non-coprime strata are numerically essential.

**Reciprocity (Bettin–Conrey, arXiv:1111.0931):**
- Exact Vasyunin reciprocity formula for primitive pairs a/b
- Connection to Estermann functions and Voronoi summation

**Bernoulli Representation (BBLS Prop. 48):**
$$\sum_{m\ge1}\frac{1}{m}\sum_{h,k\le N}\frac{c_N(h)c_N(k)}{h}B_1\!\left(\frac{mh}{k}\right)$$
retaining log-ratio, -1, and linear correction throughout.

**Approximation (Vaaler, 1985):**
Finite smooth approximation to B_1 via exponential sums.

**Bilinear Estimates:**
- **DFI (Duke–Friedlander–Iwaniec):** Sharp bounds for genuine Kloosterman fractions e(a m̄/n)
- **Bettin–Chandee (arXiv:1502.00769):** Improved trilinear estimates

### The Proposed Path

1. Apply Vaaler approximation to B_1, express as finite sum of smooth functions
2. Use reciprocity to transform a/b sum into additive/modular-inverse phases
3. Match the resulting exponential sums with DFI Kloosterman forms
4. Apply Bettin–Chandee to obtain O(1/log N) bounds
5. Sum over all gcd strata while preserving the ~625 vs ~-625 cancellation

### CRITICAL BLOCKER: PHASE MISMATCH

#### The Three Competing Phases

**Phase A (from BBLS/Vaaler):**
$$e\!\left(\frac{rmh}{k}\right)$$
Direct expansion from Bernoulli reciprocity gives this form.

**Phase B (DFI Standard):**
$$e\!\left(\frac{a\bar{m}}{n}\right)$$
where m̄ is the modular inverse, mod n. This is what DFI theorems require.

**Phase C (Current Lean Code, H15ForwardSpine.lean:32):**
$$e\!\left(\frac{A}{mn}\right)$$
**INCORRECT.** Doesn't match either Phase A or Phase B.

#### The Problem

**DFI theorems apply to genuine Kloosterman fractions** with modular inverses. The BBLS expansion gives rational phases without inverses. The existing Lean code uses a third form that matches neither.

**To proceed, you must prove an exact finite identity:**

$$\text{Phase A} \equiv \text{Phase B} \pmod{\text{error } O(1/\log N)}$$

Or prove they are incompatible and find an alternative DFI matching.

### Further Structural Blockers

Even after phase matching:

**Blocker A: Pointwise vs. Cancellation**
- Reciprocity is an pointwise identity, not a cancellation mechanism
- Absolute summation over dyadic blocks destroys the observed ~625 vs ~-625 cancellation
- Must preserve both Möbius signs and track cross-block interference

**Blocker B: gcd Strata Handling**
- DFI estimates are for balanced dyadic ranges
- gcd stratification introduces unbalanced endpoints, scaling factors
- Cannot blindly apply DFI to each gcd stratum and sum

**Blocker C: Harmonic Mode**
- The linear component L_N includes a sum over all n
- DFI handles separated dyadic blocks, not harmonic (all-denominators) mode
- Voronoi naturally transforms divisor coefficients, not two Möbius weights

### Assessment

| Dimension | Rating | Reasoning |
|-----------|--------|-----------|
| Conceptual clarity | 4/5 | Best match to arithmetic structure; phase issue is concrete |
| Classical foundation | 3/5 | Reciprocity and DFI exist separately; global match does not |
| Technical difficulty | 5/5 | New theorem needed: exact phase conversion + gcd + harmonic |
| Success likelihood | **2/5** | Highest of the three routes, but still blocked by phase mismatch |

### Recommendation

✅ **PURSUE THIS ROUTE.** Phase mismatch is a specific, addressable blocker. If resolved, it leads to the strongest classical machinery (DFI + Bettin–Chandee).

❌ **DO NOT FORMALIZE IN LEAN YET.** The phase identity must be proved on paper first.

### Next Concrete Step: The Phase Conversion Lemma

**Prove (or refute):**

> **Lemma:** For coprime (a,b) with 1 ≤ a,b ≤ N, the centered symmetric kernel
> $$K(a,b) + K(b,a) = \text{[V(a,b) + V(b,a) expression]}$$
> can be expressed as
> $$\sum_m \phi_m \cdot e\!\left(\frac{a\bar{m}}{b}\right)$$
> where m̄ is the modular inverse mod b, with explicit coefficients φ_m and total error O(1/log N) after summing all a,b ≤ N.

**What This Deliverable Should Contain:**
1. Exact identity (not approximation)
2. All coefficients and endpoint conventions
3. Numerical check: does the formula match the diagonal for small N?
4. Error bound: what is the remainder term?
5. Feasibility check: do DFI majorants sum to ≤ C/log N for the resulting dyadic blocks?

---

## ROUTE 3: Dirichlet Energy / Spectral Methods [VALIDATION TOOL]

### Objective
Formalize E_N as a squared projection distance, then analyze via Mellin/Plancherel and spectral bounds.

### Exact Formulation

Define the Nyman–Beurling operator:
$$T_N a(x) = \sum_{n\le N} a_n\left\{\frac{1}{nx}\right\}$$

where {·} is the fractional part. The Gram matrix is G_N = T*_N T_N, and our coefficients are c_N.

**Exact Identity (Already Proved in Repository):**
$$E_N = \|\chi - T_N c_N\|^2_2 = \text{[Gram expansion in terms of K(h,k)]}$$

(QuadraticInteraction.lean:917)

### The Proposed Path

1. Confirm the exact Mellin–Plancherel identity for this specific linear taper
2. Extract the critical-line Dirichlet-polynomial integral representation
3. Apply spectral or large-sieve machinery

**Classical Tools (Available):**
- **Montgomery–Vaughan:** Sharp Hilbert inequalities for separated frequencies
- **Deshouillers–Iwaniec:** Spectral large-sieve for Kloosterman sums

### Why This Route Fundamentally Fails as a Proof

**Standard operator-norm bound:**
$$\|\chi - T_N c_N\| \le \|\chi\| + \|T_N\| \cdot \|c_N\|$$

This gives a large upper bound and is **wrong for this problem**.

**Why:**
- Standard bounds ignore the special role of the Möbius direction
- They ignore the alignment between T_N c_N and χ
- They destroy the structure we need to preserve

**What is actually needed:**
Not an operator norm ‖T_N‖, but a **vector-specific projection estimate**. Equivalently, control of:
$$1 - \zeta(s)A_N(s) \quad \text{on the critical line}$$

Showing this tends to zero is **precisely the Nyman–Beurling obstruction**, which is RH-equivalent.

### Assessment

| Dimension | Rating | Reasoning |
|-----------|--------|-----------|
| Conceptual clarity | 5/5 | Clean mathematical objects; already formalized exactly |
| Classical foundation | 4/5 | Gram and Mellin machinery are standard |
| Technical difficulty | 5/5 | Missing spectral statement is equivalent to RH |
| Success likelihood | **1/5** | Generic operator-norm arguments cannot solve RH-equivalent problems |

### Recommendation

✅ **USE AS A FALSIFICATION/VALIDATION GATE:**

1. Prove the exact Mellin–Plancherel identity for this linear taper as a sanity check
2. Determine: Does RH plus Bettin–Conrey–Farmer's zero-moment hypothesis imply E_N = O(1/log N) for these coefficients?
   - Their optimal result uses a specially chosen Dirichlet polynomial
   - Does not automatically validate every natural cutoff
3. If even the conditional (RH + hypothesis) result fails, abandon this direction

❌ **DO NOT use for primary proof:** Operator norms destroy Möbius alignment.

### If You Use This to Validate

**Next step:**
1. Compute the exact Mellin integral for E_N
2. Compare with Bettin–Conrey–Farmer's integral for their polynomial
3. Document any structural difference
4. Reject or proceed based on whether conditional result applies

---

# INTEGRATION: HYBRID ROUTE 2 + ROUTE 3

### Phase 1: Validation (Route 3)
- Prove exact Mellin identity for E_N
- Check whether RH + zero-moment hypothesis gives O(1/log N)
- Confirm that unconditional O(1/log N) is not automatic

### Phase 2: Phase Conversion (Route 2)
- Prove the exact phase conversion lemma for coprime (a,b)
- Show e(rmh/k) [BBLS] ≡ e(a m̄/n) [DFI] or identify mismatch
- Preserve Möbius signs, gcd strata, harmonic mode, centering

### Phase 3: DFI Matching (Route 2)
- Only after phase conversion, test DFI/Bettin–Chandee bounds
- Sum over all gcd strata preserving the ~625 vs ~-625 cancellation
- Verify total remainder ≤ C/log N

---

# EXPERT CONSULTATION PACKET

If Route 2 Phase 2 blocks despite good-faith effort, prepare this packet:

**To:** Specialists in Bettin–Conrey cotangent sums / bilinear Kloosterman estimates

**Contents:**

1. **The exact kernel:**
   $$K(h,k) = \frac{k-h}{2hk}\log\frac{h}{k} - \frac{\pi}{2hk}(V(h,k)+V(k,h))$$

2. **The weights:** c_N(n) = -μ(n)w_N(n), w_N(n) = 1 - n/(N+1)

3. **Verified N=1000 table:**
   ```
   Q_1000 = 1.0042264
   Coprime: -0.3023752
   Non-coprime: +1.3066016
   Positive mass: 625.98
   Negative mass: -624.97
   ```

4. **Three phase candidates:**
   - Current (BBLS): e(rmh/k)
   - DFI standard: e(a m̄/n)
   - Incorrect Lean: e(A/(mn))

5. **The blocking question:**
   > Can K(h,k) + K(k,h) decompose into DFI-compatible phases while preserving all gcd strata, Möbius signs, harmonic mode, and exact centering, with total remainder O(1/log N)?

---

# Critical Rule: Do Not Formalize Until Math Is Settled

**DO NOT translate any of this into Lean until:**
1. Phase conversion lemma is proved on paper
2. DFI variables and exponents match exactly
3. Bettin–Chandee bounds verified to apply
4. Expert consultation confirms the strategy

Premature Lean translation will obscure the actual mathematical blockers.

**This is a RESEARCH investigation, not a formalization task.**

---

# Summary Table

| Route | Best For | Critical Blocker | Likelihood | Action |
|-------|----------|-----------------|------------|--------|
| **1 (Estermann)** | Exact main terms, theorem auditing | Cannot sum remainders to O(1/log N) uniformly | 1/5 | Verify only |
| **2 (Reciprocity)** | Strong machinery, arithmetic structure | Phase mismatch: BBLS vs DFI phases incompatible | 2/5 | **PURSUE** |
| **3 (Spectral)** | Falsification, validation | Operator norm destroys Möbius alignment; RH-hard | 1/5 | Validate only |

---

# Go

Begin with **Route 3 Phase 1:** Prove the exact Mellin identity for E_N and check the Bettin–Conrey–Farmer conditional result.

Then move to **Route 2 Phase 2:** Derive the phase conversion lemma.

Report what the mathematics actually says, not what you hope.
