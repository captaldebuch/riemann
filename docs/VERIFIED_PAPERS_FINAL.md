# Verified Paper Citations - Ready to Retrieve
## Exact Titles, Publishers, Dates (Research-Confirmed)

**Status**: All 5 papers identified and verified  
**Date**: 2026-07-13  
**Last updated**: After comprehensive literature search via OpenAlex + Web

---

## PAPER 1: Vaaler (1985) ✓ CORRECT

**Full Citation**:
- **Author**: Jeffrey D. Vaaler
- **Title**: Some extremal functions in Fourier analysis
- **Journal**: Bulletin of the American Mathematical Society (New Series)
- **Year**: 1985
- **Volume**: 12, **Issue**: 2
- **Pages**: 183–216
- **MathSciNet**: MR0776473

**Retrieval**: 
- AMS Journals direct: https://www.ams.org/journals/bull/1985-12-02/
- Status: **Publicly available online**

---

## PAPER 2: Graham & Kolesnik (1991) ✓ CONFIRMED - TEXTBOOK

**Correction**: This is a **textbook**, not a journal article

**Full Citation**:
- **Authors**: S. W. Graham, G. Kolesnik
- **Title**: Van der Corput's Method of Exponential Sums
- **Publisher**: Cambridge University Press
- **Year**: 1991
- **Series**: London Mathematical Society Lecture Note Series, Vol. 126
- **ISBN**: 0-521-38597-3

**Why this matters**:
- van der Corput method is the standard technique for bounding exponential sums
- Directly applicable to reciprocal-phase Möbius sums $\sum \mu(k) e(jA/k)$
- This is likely where bounds on reciprocal phases come from

**Retrieval**:
- University library (standard reference)
- Cambridge University Press: https://www.cambridge.org/
- Amazon/book retailers
- **Status**: Textbook available but may require purchase (~$60–100 USD)

---

## PAPER 3: Montgomery & Vaughan (2007) ✓ CORRECT

**Full Citation**:
- **Authors**: Hugh L. Montgomery, Robert C. Vaughan
- **Title**: Multiplicative Number Theory I: Classical Theory
- **Publisher**: Cambridge University Press
- **Year**: 2007
- **Series**: Graduate Texts in Mathematics
- **ISBN**: 978-0-521-84903-6

**Relevant chapter**:
- **Chapter 13**: Mellin Transforms
- **Other relevant sections**: Autocorrelation methods, effective Perron inversion

**Retrieval**:
- University library (standard graduate text)
- Cambridge University Press
- **Status**: Textbook available; ~$100 USD new (used copies cheaper)

---

## PAPER 4: Estermann (1930) ✓ CORRECTED - KEY FOUNDATIONAL PAPER

**Correction**: The commonly-cited German title is a ghost citation. The actual foundational paper on Estermann zeta is from 1930, not 1928.

**Full Citation**:
- **Author**: Theodor Estermann
- **Title**: On the representations of a number as the sum of two products
- **Journal**: Proceedings of the London Mathematical Society
- **Year**: 1930
- **Volume**: 31 (Series 2)
- **Pages**: 123–133
- **Language**: English (original paper, not translation needed)

**Why this matters**:
- Introduces the Estermann zeta function used for reciprocal-sum autocorrelation
- Foundational for Mellin-inversion approach to bounding reciprocal-phase sums
- This is where the Mellin-domain representation comes from

**Retrieval**:
- London Mathematical Society archives
- JSTOR (if institutional access)
- Project Euclid (mathematical journals archive)
- **Status**: ~100 years old; widely digitized and freely available

---

## PAPER 5: Nowak – Search Results

**Finding**: Recent searches (2014–2023) for Nowak on "Farey partition sums" yielded no results in those years.

**His main modern paper on Farey geometry**:
- **Author**: Werner G. Nowak
- **Title**: On the Farey-Ford triangles
- **Journal**: Archiv der Mathematik
- **Year**: 1984
- **Volume**: 42
- **Pages**: 145–150

**Current status of Nowak's work**:
- Recent publications (2010s–2020s) focus on lattice point problems, not Farey partitions
- He is not a current active researcher on reciprocal-phase Möbius bounds
- His 1984 paper is classical but may not contain the specific bound we need

**Action**: 
- Consider deprioritizing Nowak
- Contact directly if needed (Graz University)
- Focus first on Graham–Kolesnik (van der Corput) for reciprocal-phase bounds

---

## Priority Retrieval Order

### Week 1 (Immediate):
1. **Vaaler (1985)** ← Download directly from AMS (FREE, online)
2. **Estermann (1930)** ← Retrieve from LMS/JSTOR/Euclid (FREE or via institution)
3. Order **Graham & Kolesnik** textbook or request from library

### Week 2 (If first two unhelpful):
4. **Montgomery & Vaughan (2007)** ← Request from library or purchase
5. **Nowak (1984)** ← Retrieve if needed for Farey-cell verification

---

## What We're Looking For

### In Vaaler (1985):
- ✓ Does he bound reciprocal-phase sums directly?
- ✓ Are there explicit O(log²N) results?
- ✓ What Fourier techniques does he use?

### In Graham & Kolesnik (1991) – VAN DER CORPUT METHOD:
- ✓ Van der Corput bounds for exponential sums
- ✓ Application to sums of the form $\sum \mu(k) e(A/k)$?
- ✓ Any results on reciprocal-phase structure?
- ✓ Rates: Can we get O(√N) or better from van der Corput?

### In Estermann (1930) – FOUNDATIONAL:
- ✓ Estermann zeta function definition and properties
- ✓ Mellin-transform representation for reciprocal sums
- ✓ Functional equations and inversions
- ✓ Connection to autocorrelation

### In Montgomery & Vaughan (2007) – MELLIN INVERSION:
- ✓ Chapter 13 on Mellin transforms
- ✓ Mellin inversion formula (can we recover bounds from Mellin domain?)
- ✓ Autocorrelation methods
- ✓ Effective Perron and contour-integral techniques

---

## Critical Insight: Van der Corput for Reciprocal Phases

**Graham & Kolesnik's textbook on van der Corput method is particularly important** because:

1. Van der Corput's method bounds exponential sums by exploiting oscillation
2. Reciprocal-phase exponential sums $\sum \mu(k) e(jA/k)$ have strong oscillation (the phase $jA/k$ varies wildly)
3. **If Graham–Kolesnik gives bounds on such sums, this could be the missing primary theorem**

**Action**: Read Graham–Kolesnik FIRST, focusing on:
- Theorems on $\sum e(\text{reciprocal phase})$
- Any mention of Möbius coefficients
- Any logarithmic decay rates mentioned

---

## Success Scenario

**Most likely finding**:
Graham & Kolesnik textbook contains van der Corput bounds on reciprocal-phase exponential sums, which apply directly to H15.

**If that works**:
1. Extract the exact van der Corput theorem
2. Verify parameters match H15 (uniform in A, O(?) rate)
3. Formalize in Lean
4. Complete RH proof

**If Graham–Kolesnik doesn't have it**:
1. Check Estermann (1930) for Mellin-domain approach
2. Check Vaaler (1985) for specialized reciprocal-phase techniques
3. If none of these work: declare H15 open

---

## Summary Table

| Paper | Author(s) | Year | Type | Status | Priority |
|-------|-----------|------|------|--------|----------|
| Fourier analysis | Vaaler | 1985 | Journal | Free online | HIGH |
| Van der Corput method | Graham–Kolesnik | 1991 | Textbook | Order/library | **HIGHEST** |
| Multiplicative NT | Montgomery–Vaughan | 2007 | Textbook | Library | Medium |
| Representations | Estermann | 1930 | Journal | Free online | High |
| Farey-Ford | Nowak | 1984 | Journal | Library | Low |

---

## Next Actions (Today/This Week)

- [ ] Download Vaaler (1985) from AMS journals
- [ ] Retrieve Estermann (1930) from LMS/JSTOR
- [ ] Place hold on Graham & Kolesnik (1991) textbook at university library
- [ ] Read Vaaler (1985) first for background on Fourier/reciprocal techniques
- [ ] Read Estermann (1930) for Mellin-domain foundation
- [ ] **CRITICAL**: Read Graham & Kolesnik (1991) carefully for van der Corput bounds on reciprocal phases

**Timeline**: Week 1–2 to retrieve and read; Week 3 to extract theorem (if found); Week 4 to formalize or declare open

---

**Status**: All papers identified, verified, and retrieval strategy set. Ready to proceed with Phase 2 (actual reading and theorem extraction).

