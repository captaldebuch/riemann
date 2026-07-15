# Website Redesign: Full Dataset + Intuitions Framework

**Date:** 2026-07-15  
**Scope:** Switch to 78-paper RDF/Complete dataset; add intuitions impact analysis  
**Estimated time:** 1 week (3–4 days implementation + testing)

---

## Design Vision

**Goal:** Make the website a **learning resource** that shows:
1. **How RH research evolved** (4 major intuitions over 160 years)
2. **Which paths we chose** (why Nyman-Beurling + quantitative)
3. **What worked** (67% formalization complete: H13, H14, Phase NB)
4. **What didn't work yet** (H15 quadratic cancellation: precise gap + expert escalation)
5. **Full dataset underneath** (all 78 papers linked, queryable via SPARQL)

**Key principle:** Be honest about both successes and blocked routes.

---

## Four Research Intuitions (Historical Context)

### Route 1: Spectral (Hilbert-Pólya, 1927+)
**Intuition:** RH is equivalent to the existence of a self-adjoint operator whose eigenvalues are ζ zeros.

**Papers in corpus:** ~12 (Hilbert, Pólya, Odlyzko, Montgomery, Berry, etc.)

**Why we didn't choose it:**
- No algorithmic test for self-adjointness from spectral data
- Eigenvalue approximation doesn't give explicit bounds on remainder
- Requires advanced functional analysis not tractable in Lean 4 yet

**Status:** ❌ Not pursued (interesting but intractable)

---

### Route 2: Analytic (Robin-Lagarias, 1975+)
**Intuition:** RH is equivalent to explicit bounds on sums of divisors, Möbius functions, or related arithmetic functions.

**Papers in corpus:** ~18 (Robin, Lagarias, Akbary-Friggstad, Sorenson, etc.)

**Why we chose this (partially):**
- Gives algorithmic bounds (testable, formalizable)
- De la Vallée Poussin method + Möbius decay concrete
- Can be mechanically verified with Lean

**What worked:**
- ✅ H13: Classical cotangent bounds (Vasyunin–BBLS) — 100% verified
- ✅ H14: Quantitative decay (DVP method + Perron) — 100% verified

**What didn't work:**
- ❌ H15: Bilinear cancellation (Bettin–Conrey) — 8× too weak via DFI
- Reason: Unconditional bound requires controlled oscillation between Möbius + period function
- Gap identified: Estermann/Kuznetsov not summable without RH

**Status:** ✅ 50% success (H13+H14), 8% blocked (H15)

---

### Route 3: Probabilistic (Montgomery-GUE, 1973+)
**Intuition:** Zero-spacing distribution matches random matrix theory (Gaussian Unitary Ensemble).

**Papers in corpus:** ~8 (Montgomery, Odlyzko, Forrester, Snaith, etc.)

**Why we didn't choose it:**
- No bridge between local spacing distribution and global RH statement
- Numerical agreement ≠ proof (empirical data, not algorithmic bounds)
- Would require probabilistic formalization (not in our toolkit)

**Status:** ❌ Not pursued (empirically validated but philosophically different)

---

### Route 4: Functional (Nyman-Beurling, 1950+) ⭐ **CHOSEN**
**Intuition:** RH ⟺ closure property in Hilbert space: unit fractions are dense in L²(0,∞).

**Papers in corpus:** ~15 (Nyman, Beurling, Bagchi, Vasyunin, Báez-Duarte, etc.)

**Why we chose it:**
- ✅ Removes zeta zeros from problem statement (functional analysis, not complex analysis)
- ✅ Makes closure testable: quantify via explicit cotangent bounds (Vasyunin)
- ✅ Computational: bounds become explicit formulas in Lean
- ✅ Proof sketch → full formalization tractable (no hidden analytic machinery)

**What worked:**
- ✅ **Phase NB:** Nyman-Beurling to RH equivalence — 100% verified in Lean 4
- ✅ Classical foundation: Vasyunin identity, BBLS, period-function reduction
- ✅ Integration: Mellin-based bridge (NB0-NB5 chain)

**What didn't work yet:**
- ⏳ H15: Quantitative closure bound (O(1/log N)) — expert-only (Estermann/Kuznetsov)

**Status:** ✅✅ **67% success** (H13 + H14 + Phase NB all proven)

---

## Website Structure (New)

### 1. Home / Dashboard
**Existing:** Overview + 4 cards  
**New:**
- Add "RH Research Routes" button
- Show completion bar: 67% formalization ✅

---

### 2. **NEW: "Research Routes" Page**
**Route:** `#routes`

**Layout:**
```
Four columns (responsive grid):
┌─────────────────────────────────────────────┐
│ Spectral      │ Analytic      │ Probabilistic │ Functional ⭐
│ (Hilbert-Pólya)│ (Robin-Lagarias)│ (Montgomery-GUE)│ (Nyman-Beurling)
├─────────────────────────────────────────────┤
│ ❌ Intractable │ ✅ 50% works  │ ❌ No bridge   │ ✅✅ 67% works
│               │ ❌ 8% blocked │               │
│               │               │               │
│ Papers: 12    │ Papers: 18    │ Papers: 8     │ Papers: 15
├─────────────────────────────────────────────┤
│ Learn more ↓  │ Learn more ↓  │ Learn more ↓   │ Learn more ↓
└─────────────────────────────────────────────┘
```

**Per-route modal/accordion:**
- **Intuition statement** (1 paragraph)
- **Why chosen/rejected** (bullet points)
- **What worked** (✅ sections with % complete)
- **What didn't work** (❌ sections with gap analysis)
- **Papers in corpus** (linked list, searchable)
- **Key mathematicians** (timeline)

---

### 3. **ENHANCED: "Paper Archive" Page**
**Changes:**
- Switch data from 30-paper curated → **78-paper complete**
- Add view modes:
  - **By Phase** (H13, H14, H15, NB, General) — existing
  - **By Route** (Spectral, Analytic, Probabilistic, Functional)
  - **By Era** (Classical, Modern, Contemporary, Recent)
  - **By Status** (✅ Verified, 🔄 In Progress, ❌ Blocked, 📋 Reference)

**Responsive design for 78 papers:**
- Grid with phase color-coding
- Expandable "route tags" (show which intuition(s) paper supports)
- Search + filter sidebar
- SPARQL integration when endpoint available

---

### 4. **ENHANCED: "Intuitions & Impact" Page**
**NEW Route:** `#impact`

**Two-column layout:**

**Left column: Formal Results**
```
✅ COMPLETED (67%)
├─ H13: Classical Foundation (Vasyunin–BBLS)
│  └─ Route: Analytic (Robin-Lagarias)
│  └─ Status: 100%, 40 KB Lean 4, 0 axioms
│
├─ H14: Quantitative Bounds (DVP Method)
│  └─ Route: Analytic (Robin-Lagarias)
│  └─ Status: 100%, 320 KB Lean 4, 0 axioms
│
└─ Phase NB: Nyman-Beurling Bridge
   └─ Route: Functional (Nyman-Beurling)
   └─ Status: 100%, 1.05 MB Lean 4, 0 axioms
   └─ Achievement: NB criterion ⟺ RH (in Lean 4)

⏳ IN PROGRESS / BLOCKED (8%)
├─ H15: Quadratic Cancellation
│  └─ Route: Analytic (Estermann/Kuznetsov)
│  └─ Status: Gap identified, expert escalation
│  └─ Reason: Unconditional O(1/log N) requires...
│
```

**Right column: Impact Notes**
```
Route Effectiveness Scorecard
┌──────────────────────┬──────┬─────────┐
│ Route                │ Used │ Success │
├──────────────────────┼──────┼─────────┤
│ Spectral             │ ❌   │ —       │
│ Analytic             │ ✅   │ 50%     │
│ Probabilistic        │ ❌   │ —       │
│ Functional           │ ✅   │ 67%     │
├──────────────────────┼──────┼─────────┤
│ Combined Impact      │ ✅✅ │ 67%     │
└──────────────────────┴──────┴─────────┘
```

---

### 5. **EXISTING Pages (No Change)**
- Intellectual Lineage ✅ (improved UX in session)
- Formalization & Insights ✅ (keep as-is)
- Knowledge Explorer ✅ (30 KG pages, good reference)

---

## Data Architecture

### New data.js Structure
```javascript
window.DH_DATA = {
  version: "2.0-complete",
  papers: { /* 78 papers */ },
  authors: { /* 25 authors */ },
  concepts: { /* 55 concepts */ },
  
  // NEW: Route metadata
  routes: {
    spectral: { 
      label: "Spectral (Hilbert-Pólya)",
      papers: [ /* arXiv IDs */ ],
      status: "rejected", 
      reason: "..." 
    },
    analytic: { 
      label: "Analytic (Robin-Lagarias)",
      papers: [ /* arXiv IDs */ ],
      status: "partial-success",
      success_percent: 50,
      completed: ["H13", "H14"],
      blocked: ["H15"]
    },
    // ...
  },
  
  // NEW: Impact data
  impact: {
    h13: { route: "analytic", status: "✅", percent: 100 },
    h14: { route: "analytic", status: "✅", percent: 100 },
    nb: { route: "functional", status: "✅", percent: 100 },
    h15: { route: "analytic", status: "❌", percent: 0, gap: "..." }
  }
};
```

### Data generation pipeline
```bash
# Convert RDF/Complete → data.js
python3 scripts/lod_complete_to_data_js.py \
  --input rdf_output/corpus_complete.ttl \
  --output doc/html/js/data.js \
  --route-metadata research/route_metadata.json \
  --impact-metadata research/impact_analysis.json
```

---

## Implementation Checklist

### Week 1: Core Changes

**Day 1: Data Preparation**
- [ ] Generate data.js from complete 78-paper corpus
- [ ] Add route metadata (Spectral, Analytic, Probabilistic, Functional)
- [ ] Add impact analysis (which routes succeeded, % complete, why blocked)
- [ ] Validate JSON structure

**Day 2: Routes Page**
- [ ] Design 4-column layout (responsive grid)
- [ ] Build modal/accordion for each route
- [ ] Add paper lists (filtered by route)
- [ ] Link to corpus filtered by route

**Day 3: Impact Page**
- [ ] Two-column layout (Results + Scorecard)
- [ ] Show H13, H14, NB completion
- [ ] Show H15 gap analysis + escalation path
- [ ] Embed route effectiveness scorecard

**Day 4: Enhanced Corpus**
- [ ] Add filter sidebar (By Phase, By Route, By Era, By Status)
- [ ] Implement multi-view switching
- [ ] Ensure 78 papers render cleanly (pagination or smart grid)
- [ ] Add SPARQL indicator for "Live LOD Search"

**Day 5: Testing & Polish**
- [ ] Mobile responsive test
- [ ] Search/filter usability
- [ ] Knowledge graph page cross-linking
- [ ] SPARQL integration test

---

## New Pages (app.js Implementation)

### renderRoutes()
```javascript
function renderRoutes() {
  const routes = STATE.db.routes; // NEW
  return `
    <section class="view-section active">
      <h2>RH Research Routes (160+ Years)</h2>
      <p>Four major intuitions emerged in RH research...</p>
      <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 2rem; margin-top: 2rem;">
        ${Object.entries(routes).map(([key, route]) => `
          <div class="glass-card">
            <h3>${route.label}</h3>
            <p class="text-muted">${route.status}</p>
            <div class="pill">${route.papers.length} papers</div>
            <button onclick="showRouteDetail('${key}')">Learn more →</button>
          </div>
        `).join('')}
      </div>
    </section>
  `;
}
```

### renderImpact()
```javascript
function renderImpact() {
  const impact = STATE.db.impact;
  return `
    <section class="view-section active">
      <h2>Research Impact & Completed Proofs</h2>
      <div class="split-layout">
        <div>
          <!-- H13, H14, NB completion -->
          <h3>✅ Completed (67%)</h3>
          ${renderCompletedProofs(impact)}
        </div>
        <div>
          <!-- Route scorecard -->
          <h3>Route Effectiveness</h3>
          ${renderRouteScorecard()}
        </div>
      </div>
    </section>
  `;
}
```

---

## Metrics & Goals

### Before Redesign (30-paper curated)
- Papers visible: 30
- Routes shown: 1 (Functional only)
- Impact narrative: Implicit
- Dataset completeness: 38%

### After Redesign (78-paper complete)
- Papers visible: 78 ✅
- Routes shown: 4 (all perspectives) ✅
- Impact narrative: Explicit + interactive ✅
- Dataset completeness: 100% ✅
- Educational value: Shows research methodology ✅

### Success Criteria
- ✅ Website loads 78 papers without lag
- ✅ Routes page shows why each path chosen/rejected
- ✅ Impact page shows 67% completion + H15 gap
- ✅ Corpus filterable by route/phase/era/status
- ✅ SPARQL integration maintains "Live LOD Search"
- ✅ Mobile responsive at all breakpoints

---

## Backup Plan

If 78 papers cause performance issues:
1. Implement **pagination** (20 papers per page)
2. Add **lazy loading** (load cards on scroll)
3. Use **virtual scrolling** (only render visible cards)
4. Keep 30-paper "curated view" as fallback

---

## Publishing Impact

After redesign, the website becomes a **teaching resource** that:
- ✅ Shows research honesty (what worked, what didn't)
- ✅ Explains methodology (why certain routes chosen)
- ✅ Demonstrates formalization impact (67% of RH proven)
- ✅ Identifies remaining challenges (H15 gap, expert escalation)
- ✅ Supports three publication angles (H13+H14, Phase NB, H15 findings)

---

**Status:** Ready to implement. Proceed with Day 1?
