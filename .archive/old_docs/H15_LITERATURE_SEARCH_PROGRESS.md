# H15 Literature Search: Progress Log
## Finding Actual Theorems (Not Inventing Them)

**Status**: Corrected approach initiated  
**Last updated**: 2026-07-13  
**Search goal**: Locate primary theorem on reciprocal-phase Möbius sum bounds

---

## Initial Directions Identified

### Search 1: Vaaler's Reciprocal-Phase Work ⏳ TO VERIFY
**Papers identified**:
- Vaaler (1985) "Some extremal functions in Fourier analysis" 
- Vaaler (1982) "The Gram determinant of real periodic functions"

**What we need**: Does Vaaler explicitly bound $\sum \mu(k) B_1(A/k)$?

**Status**: NOT YET READ. Requires direct access to the papers.

---

### Search 2: Estermann Zeta & Mellin Inversion ⏳ TO VERIFY
**Papers identified**:
- Estermann (1928) original paper on autocorrelation
- Montgomery–Vaughan book (Multiplicative NT) Chapter 13 on Mellin transforms

**What we need**: Can Mellin inversion recover a reciprocal-phase bound from zeta-function estimates?

**Status**: NOT YET VERIFIED. The connection between Mellin domain and original sum is unclear.

---

### Search 3: Farey-Cell Reciprocal Bounds ⏳ TO VERIFY
**Papers identified**:
- Hasse, Heilbronn (classical Farey series)
- Graham & Kolesnik (1991) on sums over Farey neighbors
- Nowak (2014+) on Farey-partition sums in analytic NT

**What we need**: Do these papers bound $\sum_{|ad-bc|=1} \mu(k) B_1(A/k)$ or an equivalent form?

**Status**: NOT YET CHECKED. Graham–Kolesnik is most likely to be relevant.

---

### Search 4: Fourier Decomposition Strategy ⏳ TO VERIFY
**Structure**: 
$$B_1(x) = \sum_{j \ne 0} \frac{e^{2\pi i jx}}{2\pi i j}$$

When inserted into the Möbius sum:
$$\sum_k \mu(k) B_1(A/k) = \sum_j \frac{1}{2\pi i j} \sum_k \mu(k) e^{2\pi i jA/k}$$

**What we need**: 
1. Bounds on $\sum_k \mu(k) e(jA/k)$ for fixed $j$
2. Does summing over $j$ with the Fourier decay $1/j$ yield $O(1/\log^2 N)$?

**Status**: NOT YET WORKED OUT. This is a plausible route but requires explicit calculation.

---

### Search 5: Character Sum Extensions ⏳ TO VERIFY
**Papers identified**:
- Harper–Klurman–Mangerel (2022+) on character correlations
- Matomäki (2023+) on averaged correlations

**What we need**: Do modern character-sum techniques handle reciprocal phases?

**Status**: LIKELY NOT DIRECTLY. These papers focus on linear phases or linear correlations.

---

## What to Do Next

### Phase 0: Paper Access
- [ ] Obtain Vaaler (1985) paper
- [ ] Obtain Graham–Kolesnik (1991) if available
- [ ] Check Montgomery–Vaughan book (likely in university library)

### Phase 1: Direct Verification (This week)
For each paper above:
- [ ] Does it treat $\sum \mu(k) e(jA/k)$ or $\sum \mu(k) B_1(A/k)$ explicitly?
- [ ] If yes: extract the exact theorem, parameters, bound rate
- [ ] If no: does it contain techniques that could extend to this case?

### Phase 2: Transformation Analysis (1–2 weeks)
- [ ] For the Fourier decomposition route: calculate whether $\sum_j (1/j)^2 \cdot (\text{bound on j-sum})$ gives the desired rate
- [ ] For Farey cells: check if non-modular reciprocal structure (our case) relates to classical results
- [ ] For Mellin inversion: understand whether the inversion formula can recover original-domain bounds

### Phase 3: Expert Consultation (2–4 weeks)
If no primary theorem found after Phase 1–2, contact:
- Analytic number theorists specializing in reciprocal sums
- Experts in Farey-partition techniques
- Specialists in Estermann's autocorrelation method

---

## Known Constraints

❌ **NOT applicable**:
- MRT mollified Chowla (linear phases, not reciprocal)
- Generic Abel/harmonic summation (doesn't solve the outer mode cancellation)
- DFI character sums with modular inverses (different structure)
- Weyl's equidistribution (gives $O(\sqrt{N} \log N)$, too weak)

✓ **Still promising**:
- Vaaler's exact reciprocal-phase bounds (if they exist)
- Estermann zeta + Mellin inversion (if the inversion recovers the sum)
- Farey-cell non-modular reciprocal bounds (if they're in the literature)
- Fourier decomposition + j-summation (if rates work out)

---

## Honest Interim Report

**As of 2026-07-13**:
- The H15 reciprocal-phase Möbius-sawtooth bound has no **known published primary theorem** that directly applies
- Four promising directions identified, all requiring verification
- No formalization will proceed until a primary source is verified

**If verification fails**: The bound will be formally declared as an open problem, with three candidate proof routes documented and awaiting expert judgment.

---

## Success Criteria

**Found theorem** (Phase 1 outcome):
> "Vaaler (1985) Theorem X: $|\sum_{k \le N} \mu(k) B_1(A/k)| \le C/\log^2(N)$ for [conditions]"

**Transformation succeeds** (Phase 2 outcome):
> "Fourier decomposition + j-summation yields $C/\log^2(N)$ from known character-sum bounds"

**No theorem found** (Phase 3 outcome):
> "Consulted [expert names]. Verdict: H15 reciprocal-phase bound appears novel; recommend collaborative formalization of new theorem"

---

## References for Search

**Papers to obtain and review**:
1. Vaaler (1985) "Some extremal functions in Fourier analysis"
2. Graham & Kolesnik (1991) "A Tauberian theorem and applications"
3. Montgomery & Vaughan (2007) "Multiplicative Number Theory I: Classical Theory"
4. Estermann (1928) "Über die Fourier-Entwicklung gewisser automorphen Funktionen"

**Key authors to check for reciprocal-phase results**:
- Vaaler (Fourier & reciprocals)
- Nowak (Farey sums)
- Soundararajan (moment bounds)
- Klurman (character & reciprocal sums)

---

**Next**: Begin Phase 0 (paper access) and Phase 1 (direct verification).

