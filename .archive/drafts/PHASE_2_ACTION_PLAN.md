# Phase 2: Literature Retrieval & Verification
## H15 Reciprocal-Phase Möbius Bound — Execution Plan

**Status**: Ready to execute  
**Date**: 2026-07-13  
**Objective**: Retrieve and verify the seven key papers identified in Phase 1

---

## The Seven Target Papers (Priority Order)

### **PRIORITY 1: Montgomery–Vaughan (2007) Multiplicative Number Theory I**
**Status**: HIGHEST PRIORITY - Most accessible  
**Citation**: Hugh L. Montgomery, Robert C. Vaughan. *Multiplicative Number Theory I: Classical Theory*. Graduate Texts in Mathematics, Cambridge University Press, 2007. ISBN: 978-0-521-84903-6.

**Retrieval**:
- [ ] University library (likely in math reference collection)
- [ ] Cambridge University Press website
- [ ] Inter-library loan if not available locally
- [ ] Google Books (may have preview of Ch. 13)

**What to extract**: Chapter 13 on Mellin transforms, sections on:
- Mellin inversion formulas
- Autocorrelation methods
- Reciprocal-sum techniques
- Estermann zeta connection

**Expected payoff**: High — This is a standard graduate text with modern expositions of all machinery.

---

### **PRIORITY 2: Bettin–Conrey (Vasyunin Reciprocity)**
**Status**: HIGH PRIORITY - Directly relevant to H15  
**Likely citation**: Bettin, S., & Conrey, B. (2015–2020). "Special Values of $L$-functions and the Nyman–Beurling criterion" or similar. *International Journal of Number Theory* or *Research in Number Theory*.

**Retrieval**:
- [ ] arXiv search: "Bettin" "Conrey" (2015 or later)
- [ ] MathSciNet direct search
- [ ] Author homepages (Conrey at AIM, Bettin at Genoa)
- [ ] Email authors for preprints

**What to extract**:
- Vasyunin formula: $V(h/k) = \sum_{a=1}^{k-1} \frac{a}{k} \cot(\pi ah/k)$
- Reciprocity: $xV(x) + V(1/x) - \frac{1}{\pi \text{Den}(x)} = g(x)$
- Connection to Estermann zeta functional equation
- Application to Nyman–Beurling criterion

**Expected payoff**: CRITICAL — This bridges our H13 (Vasyunin) to the larger machinery.

---

### **PRIORITY 3: Estermann Foundational Papers (1928–1930)**
**Status**: HIGH PRIORITY - Foundational  
**Citations**:
1. Estermann, T. (1928). "Über die Fourier-Entwicklung gewisser automorpher Funktionen." *Mathematische Annalen* (exact volume/pages: to be confirmed).
2. Estermann, T. (1930). "On the representations of a number as the sum of two products." *Proceedings of the London Mathematical Society*, Series 2, Vol. 31, pp. 123–133.

**Retrieval**:
- [ ] JSTOR (if institutional access available)
- [ ] Internet Archive (Wayback/historical journals)
- [ ] University library special collections
- [ ] Project Euclid (mathematical journals archive)
- [ ] MathSciNet for full citations

**What to extract**:
- Definition of Estermann zeta function
- Meromorphic properties
- Functional equation: $E(s; h/k, \alpha) \leftrightarrow E(1-s+\alpha; h'/k, \alpha)$
- Autocorrelation interpretation

**Expected payoff**: Foundational — Understanding the root source is critical.

---

### **PRIORITY 4: Kuznetsov Trace Formula (Autocorrelation)**
**Status**: MEDIUM–HIGH PRIORITY - Key machinery  
**Likely citations**:
1. Kuznetsov, N.V. (1981). "Petersson inner product of metaplectic forms and Whittaker functions." *Journal of Soviet Mathematics*, 17 (3), 1197–1267. [Original Russian: *Zap. Nauchn. Sem. LOMI*, 64]
2. Modern exposition: Iwaniec, H., & Kowalski, E. (2004). *Analytic Number Theory*. American Mathematical Society. Chapters on trace formulas.

**Retrieval**:
- [ ] Iwaniec–Kowalski (standard modern reference, likely in university library)
- [ ] MathSciNet for Kuznetsov original
- [ ] Springer/AMS publishers for modern books

**What to extract**:
- Trace formula structure
- Application to autocorrelation sums
- Connection to Maass cusp forms and spectral data
- Hyperbolic Laplacian eigenvalues

**Expected payoff**: High — Enables Type II bilinear bound reduction.

---

### **PRIORITY 5: Farey–Möbius Modern Work**
**Status**: MEDIUM PRIORITY - Alternative route  
**Likely authors/search terms**:
- Papers on "Farey sequence" + "Möbius function"
- Papers on "Franel's theorem" (RH equivalence)
- Authors: Conrey, Snaith, Robles, Zaharescu, Nowak (if recent Farey work exists)
- Search: "Farey partition" + "reciprocal phase"

**Retrieval**:
- [ ] MathSciNet direct search
- [ ] arXiv search: "Farey" "Möbius" (last 10 years)
- [ ] Google Scholar for citation chains

**What to extract**:
- Unimodular condition: $|ad - bc| = 1$ for Farey neighbors
- Partition of reciprocal-phase sums using Farey cells
- Deterministic cancellation from modular group geometry
- Ford circle tangency properties

**Expected payoff**: Medium — Provides geometric alternative if Estermann/Mellin insufficient.

---

### **PRIORITY 6: Type II Bilinear Bounds (Vaughan Identity)**
**Status**: MEDIUM PRIORITY - Advanced machinery  
**Likely sources**:
- Vaughan, R.C. papers on bilinear sums (1974+)
- Iwaniec–Kowalski (modern exposition)
- Papers on Kloosterman sums (which are Type II-like)
- Trace formula applications to Type II

**Retrieval**:
- [ ] Iwaniec–Kowalski textbook (Ch. on bilinear sums)
- [ ] MathSciNet search: "Vaughan" "Type II" "bilinear"
- [ ] Papers on Kloosterman sums and trace formulas

**What to extract**:
- Type I vs. Type II sum structure
- Cauchy–Schwarz decomposition for balanced regime
- Mollification of coefficients
- Trace formula reduction to spectral data

**Expected payoff**: Medium-High — Essential if Route 3 (mollified Type II) is pursued.

---

### **PRIORITY 7: Modern Machinery (MRT, Tao, Helfgott)**
**Status**: LOW PRIORITY - Fallback only  
**Papers**:
1. Matomäki–Radziwiłł–Tao (2015+) on mollified Chowla
2. Tao entropy decrement argument (2019+)
3. Helfgott expanders (2010s+)

**Retrieval**:
- [ ] arXiv search for author names + recent years
- [ ] Author homepages and publication lists

**What to extract**: Only if classical methods (Estermann, Farey, Vaughan) fail to yield $O(1/\log^2 N)$ bound.

**Expected payoff**: Low — Likely overkill if classical routes work.

---

## Execution Timeline

### **Week 1 (This week)**
- [ ] Obtain Montgomery–Vaughan textbook (library or ILL)
- [ ] Search arXiv/MathSciNet for Bettin–Conrey Vasyunin paper
- [ ] Confirm exact Estermann citations via MathSciNet
- [ ] Email key authors (Conrey, Bettin) requesting preprints if needed

### **Week 2**
- [ ] Retrieve Estermann (1928, 1930) via JSTOR/Archive/Library
- [ ] Retrieve Kuznetsov via Iwaniec–Kowalski or original
- [ ] Begin reading Montgomery–Vaughan Ch. 13 (Mellin transforms)
- [ ] Search for Farey–Möbius modern papers

### **Week 3**
- [ ] Read and extract key theorems from all retrieved papers
- [ ] Cross-check: Do they directly bound $\sum \mu(k) e(A/k)$ or equivalently?
- [ ] Identify which route (Estermann, Farey, Type II + trace, or MRT) is most direct

### **Week 4**
- [ ] Decide: "Route X applies directly to H15" OR "Route X insufficient, try Route Y" OR "H15 is open"
- [ ] If route found: Formalize in Lean → RH proved
- [ ] If no route: Declare H15 open with documented proof routes

---

## Success Criteria for Each Paper

### Estermann Papers
**Success**: Explicit functional equation $E(s; h/k) \leftrightarrow E(1-s; h'/k)$ with coefficients that apply to reciprocal-phase sums.

### Bettin–Conrey
**Success**: Reciprocity formula with Vasyunin sums + connection to Estermann zeta + application to Möbius correlations.

### Montgomery–Vaughan
**Success**: Mellin inversion formulas for reciprocal-phase sums, with explicit contour-shift main term extraction.

### Kuznetsov
**Success**: Trace formula relating arithmetic sums to spectral data, explicitly for autocorrelation of reciprocal-phase weighted functions.

### Farey–Möbius
**Success**: Partition bounds using unimodular Farey structure for Möbius sums, yielding $O(?)$ rate.

### Type II Bilinear
**Success**: Explicit bounds on balanced bilinear sums with reciprocal denominators, via mollification + trace.

### MRT/Tao/Helfgott
**Success (only if needed)**: Application to reciprocal-phase polynomial functions, covering degree or generality sufficient for H15.

---

## Decision Tree

```
Found explicit H15-matching bound in Estermann/Mellin?
├─ YES → Verify parameters, formalize in Lean → RH COMPLETE
└─ NO → Try Farey-partition route
    ├─ YES (Farey gives O(1/log²N)) → Formalize → RH COMPLETE
    └─ NO → Try Type II + Trace formula route
        ├─ YES (Type II mollification works) → Formalize → RH COMPLETE
        └─ NO → Consult MRT/Tao machinery
            ├─ YES (Routes apply to reciprocal phases) → Formalize → RH COMPLETE
            └─ NO → H15 RECIPROCAL-PHASE MÖBIUS BOUND IS OPEN
                   (Document the bound, invite expert collaboration)
```

---

## Key Contact Points (If Needed)

**Authors who specialize in this machinery**:
- Brian Conrey (AIM) — Vasyunin, Estermann, L-functions
- Jon Keating (Bristol) — Estermann zeta, random matrices
- Ken Ono (UVA) — Automorphic forms, Mellin transforms
- Hugh Montgomery (Michigan) — Multiplicative number theory
- Robert Vaughan (Penn State) — Exponential sums, Type II bilinear

Email requests for preprints are almost always successful in academic mathematics.

---

## Expected Outcome

One of four conclusions by end of Week 4:

1. **RH Proved**: Found primary theorem matching H15, formalized successfully
2. **RH Conditional**: H15 reduced to named open problem with documented proof routes
3. **Route Failure**: Identified why each route fails; need expert consultation
4. **Expert Collaboration**: Bounded problem ready for presentation to analytic number theorists

**All four are scientifically honest outcomes.**

---

## Next Action

**START NOW**: Retrieve Montgomery–Vaughan and Bettin–Conrey. These are the two highest-payoff sources.

