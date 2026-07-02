# Riemann Hypothesis — Formal Verification Project

**Goal:** Use Lean 4 + Aristotle (formal proof search) and Google Antigravity (agentic coding) to build a formal proof-auditing and proof-discovery machine for the Riemann Hypothesis.

**Key insight from our analysis:** The realistic target is not "AI proves RH in one step." It is:
> Build a Lean environment where Aristotle searches for new **bridge lemmas** inside RH-equivalent frameworks, while Lean rejects every false convergence, positivity, spectral, or asymptotic step.

---

## Project Structure

```
riemann/
├── RiemannHypothesis/          ← Lean 4 library (Lake project)
│   ├── Basic/
│   │   ├── Zeta.lean           ← ζ(s), ξ(s), critical strip definitions
│   │   └── CriticalStrip.lean  ← RH statement, zero symmetry, zero-free regions
│   ├── Criteria/               ← RH-equivalent formulations
│   │   ├── Li.lean             ← Li's positivity criterion
│   │   ├── NymanBeurling.lean  ← Nyman–Beurling–Báez-Duarte (BEST FIRST TARGET)
│   │   ├── Weil.lean           ← Weil explicit formula & positivity
│   │   └── Spectral.lean       ← Hilbert–Pólya spectral criterion
│   ├── Finite/                 ← Finite approximations & certificates
│   │   ├── GramMatrices.lean   ← Gram matrix for Nyman basis
│   │   └── TailBounds.lean     ← Finite → infinite transfer theorems
│   └── Discovery/              ← Aristotle workspace
│       ├── BridgeLemmas.lean   ← Candidate bridge lemmas (sorry stubs)
│       └── FailedAttempts.lean ← Formalized historical failures
├── experiments/                ← Python numerical support
│   ├── gram_matrix_search.py   ← Compute & certify Gram matrices
│   ├── li_coefficients.py      ← Li coefficient numerical checks
│   └── weil_kernel_search.py   ← Weil kernel candidate search
├── docs/                       ← Research notes
│   ├── attacks.txt             ← Main RH barriers analysis
│   ├── method.txt              ← Aristotle-Lean architectures
│   ├── notes.txt               ← Critical evaluation
│   └── roadmap possible.txt    ← Full 10-avenue roadmap
├── AGENTS.md                   ← Instructions for AI agents
├── lakefile.toml               ← Lake build config (Mathlib dependency)
└── lean-toolchain              ← Lean 4.30.0
```

## Overall Roadmap & Optimal Proof Sequence

We have outlined 5 core theoretical strategies (Quantum Chaos, Noncommutative Geometry, Li's Criterion, Equivalent Bounds, and Quasicrystals). 
For a complete breakdown of each approach and our optimal sequence of proofs to actually solve the Riemann Hypothesis, please see [docs/roadmap.md](file:///Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/docs/roadmap.md).

## Where to Start

**Best first target:** `RiemannHypothesis/Criteria/NymanBeurling.lean`

The Nyman–Beurling–Báez-Duarte criterion is:
- RH-equivalent ✓
- Hilbert-space based ✓
- Discrete in Báez-Duarte's form ✓
- Numerically explorable ✓
- Lean-friendly ✓

**Current Focus:** We have successfully established the Python → Lean certificate pipeline for finite approximations. Our immediate next step is upgrading our Python tools to emit exact rational $LDL^T$ or Cholesky witnesses (`RationalPSDWitness`) for massive Gram matrices, which Lean will algebraicly verify using `norm_num`.

---

## Tool Roles

| Tool | Role |
|------|------|
| **Lean 4 + Mathlib** | Formal gatekeeper — rejects false steps |
| **Aristotle** | AI proof search — fills `sorry` stubs |
| **Google Antigravity** | Agentic coding — builds structure, generates scaffolding |
| **Python experiments** | Numerical conjecture generator + certificate producer |

---

## The Lean Architecture

```
RH theorem
  ↑
RH-equivalent criterion (Li, Nyman–Beurling, Weil, Spectral)
  ↑
finite / quantitative / positivity criterion
  ↑
Lean-verifiable bridge lemmas  ← Aristotle searches here
```

---

## Build

```bash
lake exe cache get   # download Mathlib cache (fast)
lake build           # build the project
```
