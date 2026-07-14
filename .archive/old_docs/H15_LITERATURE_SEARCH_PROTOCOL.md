# H15 Reciprocal-Phase Bounds: Systematic Literature Search
## Finding Primary Theorems (Not Inventing Them)

**Status**: Correcting false bridges; seeking actual published theorems  
**Date**: 2026-07-13  
**Objective**: Locate or prove a primary theorem bounding the H15 reciprocal-phase sum

---

## The Exact Problem to Solve

The H15 open problem reduces to bounding:

$$\sum_{k=1}^{N} \mu(k) \cdot \omega_N(k) \cdot B_1(A/k) = O(1/\log^2 N)$$

where:
- $\mu(k)$ is the Möbius function
- $\omega_N(k)$ is a cutoff weight (e.g., $1 - k/(N+1)$)
- $B_1(x) = x - 1/2$ is the sawtooth (Dedekind fractional part)
- $A$ is a fixed parameter ($1 \le A \le N$)
- The bound must hold uniformly in $A$

**Critical constraint**: This is NOT $\sum \mu(k) e(\alpha k)$ (linear phase). It is $\sum \mu(k) B_1(A/k)$, a reciprocal-phase sum.

---

## Search Strategy 1: Vaaler's Diophantine Approximation

**Key paper**: Vaaler (1985) on best rational approximations and sawtooth functions.

### What to verify
- Does Vaaler's work treat reciprocal-phase sums $e(jA/k)$ for the sawtooth?
- Does he provide bounds on $\sum \mu(k) B_1(A/k)$?
- If he uses Fourier decomposition, what are the resulting phase-sum bounds?

### Search terms
- "Vaaler" + "sawtooth" + "reciprocal"
- "Vaaler" + "Dedekind" + "Diophantine"
- "rational approximation" + "Möbius" + "sawtooth"

### Expected outcome
- If Vaaler already bounds the reciprocal phases, cite and formalize
- If not, understand his technique and check if it extends

---

## Search Strategy 2: Möbius Reciprocal-Phase Sums (Direct)

**Exact search**: Papers treating sums of the form $\sum \mu(k) f(A/k)$ or $\sum \mu(k) e(jA/k)$

### What to verify
- Does the literature treat reciprocal-phase Möbius sums explicitly?
- Are there bounds on $\sum_{k \le N} \mu(k) e(2\pi i j A/k)$ for fixed $A, j$?
- What is the dependence on $N$, $|j|$, $A$?

### Search terms
- "Möbius sum" + "reciprocal phase"
- "reciprocal" + "exponential sum" + "Möbius"
- "Farey" + "Möbius" + "phase" (Farey neighbors have modular inverse structure)

### Papers to check
- Estermann (classical work on character sums with reciprocals)
- Nontrivial Dirichlet series evaluations (might contain reciprocal-sum bounds)

### Expected outcome
- Locate a published theorem: "If [conditions], then $|\sum \mu(k) e(jA/k)| \le [bound]$"

---

## Search Strategy 3: Vaaler Fourier Decomposition + Existing Bounds

**Decomposition**: $B_1(x) = \sum_{j \ne 0} \frac{e^{2\pi i jx}}{2\pi i j}$ (Fourier series)

When inserted into the sawtooth sum:
$$\sum_{k=1}^{N} \mu(k) B_1(A/k) = \sum_{j \ne 0} \frac{1}{2\pi i j} \sum_{k=1}^{N} \mu(k) e^{2\pi i jA/k}$$

### What to verify
- Can we use **existing** character-sum or exponential-sum bounds on $\sum \mu(k) e(jA/k)$?
- Which bounds apply? (Kloosterman, Weyl, van der Corput, etc.)
- What rates do they give?

### Candidate sources
- **Kloosterman sums** (Duke–Friedlander–Iwaniec, but uses $e(a\bar{m}/n)$ not $e(jA/k)$)
  - Can the modular inverse structure be transformed away?
  - Or do we need a different bound?

- **Weyl/van der Corput** (standard oscillatory-integral bounds)
  - Applies to sums with smooth phase (not $1/k$, which is singular)
  - Bound is likely $O(N^{1/2})$, too weak for H15

- **Estermann zeta** (autocorrelation via Mellin transform)
  - Connects reciprocal-phase sums to zeta growth
  - Need to check if the existing growth bounds in Lean suffice

### Expected outcome
- Either: "Use Estermann zeta growth + Mellin inversion to bound the phases"
- Or: "Kloosterman structure [doesn't/does] extend to reciprocal phases; need alternative"

---

## Search Strategy 4: Estermann Zeta & Autocorrelation Methods

**Key idea**: The reciprocal-phase sum can be viewed as a Mellin-transform pair via Estermann's work.

### What to verify
- Estermann's autocorrelation formula and its zeta connection
- Does the Mellin transform of $\sum \mu(k) B_1(A/k)$ relate to known $\zeta(s)$ bounds?
- Can we invert the Mellin transform to recover the sum bound?

### Papers to check
- Estermann (1928) on the Estermann zeta function
- Modern work on Mellin inversion and oscillatory integrals

### Expected outcome
- If yes: "Estermann zeta bounds + Mellin inversion + effective Perron → reciprocal-phase bound"
- If no: "Estermann structure is insufficient; need additional cancellation"

---

## Search Strategy 5: Modern Work on Correlations & Averages

**Key papers to check**:

### Matomäki–Radziwiłł–Tao (correct reference: arXiv:1503.05121)
- **What they do**: Bound $\sum \mu(n) f(n) f(n+h)$ for linear shifts
- **What we need**: Reciprocal-phase structure $\sum \mu(k) B_1(A/k)$
- **Verdict**: Different problem (linear vs. reciprocal); check if their techniques extend

### Tao–Teräväinen (on Chowla conjecture variants)
- **What they do**: Averaged, twisted linear correlations
- **Verdict**: Again linear phases; not directly applicable

### Harper–Klurman–Mangerel (on character sums)
- **What they do**: Bounds on $\sum \chi(n) e(an/q)$ and twisted sums
- **Verdict**: Character sums, not pure Möbius; check for cross-application

### Soundararajan work on moment bounds
- **Relevant?**: Check if any moment-bound techniques apply to reciprocal phases

---

## Search Strategy 6: Transformation Theorems

**Question**: Is there a change of variables or transformation that converts the H15 reciprocal-phase sum to a form with **known** bounds?

### Candidate transformations
- **Hyperbola method**: Can we decompose into coprime/gcd pieces with different bounds?
- **Summation-by-parts**: Does partial summation with the Möbius function reduce to a simpler form?
- **Perron inversion**: Can we use Perron's formula to move the sum to a contour integral with known bounds?

### Expected outcome
- Either: "The reciprocal-phase sum reduces to [known bounded form] via [transformation]"
- Or: "No known transformation; the reciprocal-phase structure is genuinely novel"

---

## What NOT to Search For

**❌ Don't search for**:
- "Mollified Chowla" as a direct application (it treats linear phases, not reciprocal)
- Generic "summation-by-parts" papers (A2 false claim already disproven)
- Papers on other Dirichlet characters unless they explicitly treat reciprocal phases
- Anything claiming MRT or DFI apply without checking parameter matching first

---

## Search Execution Plan

### Phase 1: Direct Literature Lookup (This week)
- [ ] Check Vaaler (1985) for reciprocal-phase sawtooth treatment
- [ ] Search MathSciNet/arXiv for "reciprocal phase Möbius" or similar
- [ ] Review Estermann's papers and modern Mellin-inversion work
- [ ] Check if Farey-summation techniques apply to non-modular reciprocal phases

### Phase 2: Cross-reference Check (1–2 weeks)
- [ ] For each promising paper, verify:
  - Does it treat $e(jA/k)$ (reciprocal phase) or something else?
  - What is the explicit bound and its dependence on parameters?
  - Are there unproven auxiliary claims embedded in the proof?
- [ ] Numerical test: Does the published bound predict $O(1/\log^2 N)$ when applied to H15?

### Phase 3: Transformation Analysis (1–2 weeks)
- [ ] If no direct bound found, systematically check transformations:
  - Hyperbola method → does it isolate a known bounded form?
  - Partial summation → does it reduce to a simpler sum?
  - Perron inversion → can the resulting contour integral be bounded?

### Phase 4: Decision (end of Month 1)
- [ ] **If found**: Primary theorem located; cite, verify parameters, formalize
- [ ] **If not found**: Document why each route fails; propose open problem status

---

## What Constitutes a Valid "Match"

A published theorem counts as a valid bridge if:

1. **The sum has the same form**: $\sum_{k \le N} \mu(k) \cdot (\text{oscillatory}) \le \text{bound}(N)$
2. **The phase is reciprocal or can be transformed to reciprocal**: $e(jA/k)$ or equivalent
3. **The bound is explicit**: Not "small" or "bounded" but actual rate (e.g., $O(1/\log^2 N)$)
4. **Parameters match**: The theorem applies for the ranges of $A, j, N$ we need
5. **Hypotheses are discharged**: All needed conditions (Mertens, RH, bounds) are already Lean-proved

**Anything less**: Mark as "promising" but not yet formalized; note what verification is needed.

---

## Known Obstacles (From User Feedback)

- MRT is about linear phases $e(\alpha n)$, not reciprocal phases $e(jA/k)$ ✗
- DFI uses modular inverses $e(a\bar{m}/n)$, not arbitrary reciprocals ✗
- Generic Abel summation does NOT solve conditional harmonic convergence ✗
- Vaaler may treat Fourier phases but not necessarily with Möbius structure ✓?
- Estermann may have a Mellin connection but inversion rates are unclear ✓?

---

## Preliminary Hypothesis

Based on the structure, the reciprocal-phase bound might require:

1. **Primary source**: Either Vaaler's reciprocal-phase work or a modern extension
2. **Transformation**: Decomposition into Farey neighbors (non-modular reciprocal structure)
3. **Summation argument**: Integration over Farey cells with explicit error tracking
4. **Rate**: Depends on how cancellation is obtained; likely related to $\log$-factors from Farey density

If none of the above sources yield the bound, the problem may be genuinely novel and require new mathematics.

---

## What Success Looks Like

**Success (Phase 4 outcome A)**:
> "Found: Paper [X] by [Authors], [Year]. Theorem: $|\sum_{k \le N} \mu(k) f(A/k)| \le C/\log^2 N$ under [conditions]. Conditions verified in Lean: [list]. Formalize [Theorem name]."

**Honest Open (Phase 4 outcome B)**:
> "Searched: [20 papers reviewed]. No primary source found for reciprocal-phase Möbius bounds with $O(1/\log^2 N)$ rate. Transformation approaches tried: [list]. None yield matching bound. H15 reciprocal-phase sum appears to be an open problem. Recommend expert consultation on whether this is genuinely novel or known to specialists but not yet published."

---

## Next: Actual Search Begins

Will proceed systematically through Strategies 1–6 above. 
Updates will be honest: "found promising lead" or "this doesn't apply" with explicit reasons.

No more false bridges.
