# Riemann Hypothesis — Digital Humanities + Formal Methods

**Approach:** Gather mathematical thought from classical sources (1895-2017) and coordinate it via a "parliament of LLMs" into a scaffolded Lean 4 formalization.

**Methodology:** Rather than claiming to "prove" RH, we:
1. Identify the proof chain (H13 Vasyunin → H15 reciprocal-phase bound → RH via Nyman-Beurling)
2. Axiomatize classical theorems from peer-reviewed papers (with full citations)
3. Mechanically prove the connective tissue in Lean
4. Validate empirically with 8,280 numerical test cases
5. Use multiple LLM agents (code, mathematics, integration) coordinated by the Lean compiler

**Result:** A formal structure articulating existing mathematical knowledge, verified end-to-end.

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
