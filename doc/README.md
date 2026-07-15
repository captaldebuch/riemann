# Documentation Structure — RH Formalization Project

Complete roadmap to the Riemann Hypothesis via Nyman–Beurling and Lean formalization.

---

## Quick Navigation

### For Project Overview
👉 Start: **[status/README.md](status/README.md)** — What is this project?  
Then: **[status/PROJECT_STATUS.md](status/PROJECT_STATUS.md)** — Current state and metrics  
Full roadmap: **[MASTER_ROADMAP_TO_RH.md](../MASTER_ROADMAP_TO_RH.md)** (scratchpad, to migrate)

### For Research Plans
- **H15 (Open Problem)**: [strategy/H15_RESEARCH_AGENDA.md](strategy/H15_RESEARCH_AGENDA.md)
- **Phase NB (NB/RH Bridge)**: Memory (`phase_nb_nyman_beurling_rh_bridge_roadmap.md`)
- **H14 (Linear Möbius)**: Memory (`h14_honest_completion_status.md`)

### For Mathematical Details
- **H15 Problem**: [strategy/H15_EXACT_THEOREM_SPECIFICATION.tex](strategy/H15_EXACT_THEOREM_SPECIFICATION.tex)
- **Analysis**: [technical/TECHNICAL_REPORT.md](technical/TECHNICAL_REPORT.md)
- **Literature**: [literature/INDEX.md](literature/INDEX.md) — Which papers contain what

### For Implementation
- **H14 FEFactor Prompt**: `CODEX_H14_COMPLETION_PROMPT.md` (scratchpad)
- **H15 Diagnostics**: To be added (Phase 1)
- **Phase NB Structure**: NB0–NB7 sub-tasks in memory

---

## Folder Structure

```
doc/
├── README.md (this file)
│
├── status/              ← PROJECT STATE & METRICS
│   ├── INDEX.md         ← Entry point for status
│   ├── README.md        ← General overview
│   ├── PROJECT_STATUS.md ← Current state table
│   └── (MASTER_ROADMAP_TO_RH.md) ← To migrate from scratchpad
│
├── strategy/            ← RESEARCH PROGRAMMES & PLANS
│   ├── INDEX.md         ← Entry point for strategy
│   ├── H15_EXACT_THEOREM_SPECIFICATION.tex
│   ├── H15_RESEARCH_AGENDA.md
│   └── (Codex prompts) ← To organize into doc/prompts/
│
├── technical/           ← DEEP MATHEMATICAL ANALYSIS
│   ├── INDEX.md         ← Entry point for analysis
│   └── TECHNICAL_REPORT.md
│
└── literature/          ← CLASSICAL REFERENCES
    ├── INDEX.md         ← Papers guide
    ├── 1111.0931v2.pdf  ← Bettin & Conrey (H15)
    ├── 1211.5191v1.pdf  ← Bettin, Conrey, Farmer (Phase NB)
    ├── 1601.06839v3.pdf ← Auli, Bayad, Beck (H15)
    └── 9780521849036_frontmatter.pdf ← Montgomery-Vaughan (H14)
```

---

## Key Strategic Decisions (In Memory)

These are the authoritative decision records. Reference them for project direction:

- **h15_research_vs_lean_decision.md** — Why H15 is a research problem, not a Lean task
- **h15_formulation_error_audit.md** — Why pointwise sawtooth bound is false
- **h14_honest_completion_status.md** — Why H14 has 3 pieces, not 1 (FEFactor, Jensen, Perron)
- **phase_nb_nyman_beurling_rh_bridge_roadmap.md** — Complete NB0–NB7 breakdown

---

## The Full Chain to RH

```
H13: Vasyunin Bridge
  Status:   ✅ COMPLETE
  Location: mathlib/
  
H14: Linear Möbius Estimates
  Status:   🔴 ~60% done, 8–11 weeks remaining
  Blockers: FEFactor, BorelJensen, Perron (3 independent pieces)
  
H15: Quadratic Interaction
  Status:   ❌ OPEN RESEARCH
  Timeline: 3–12 months research (3 proof routes)
  
Báez–Duarte Criterion
  Status:   🟢 CONDITIONAL (wiring done)
  Depends:  H13 + H14 + H15
  
Phase NB: Nyman–Beurling / RH Bridge
  Status:   🟢 FULLY MAPPED (4–8 weeks, 7 sub-phases)
  Approach: Mellin transforms + zero-detection
  
Riemann Hypothesis
  Status:   ❌ UNPROVEN (depends on all above)
  Timeline: 9–15 months minimum
```

---

## For New Contributors

1. **Understand the project**: Read [status/README.md](status/README.md)
2. **Check current state**: [status/PROJECT_STATUS.md](status/PROJECT_STATUS.md)
3. **Pick a task**:
   - **H14**: See memory `h14_honest_completion_status.md` + scratchpad `CODEX_H14_COMPLETION_PROMPT.md`
   - **H15 diagnostics**: See [strategy/H15_RESEARCH_AGENDA.md](strategy/H15_RESEARCH_AGENDA.md), Phase 1
   - **Phase NB**: See memory `phase_nb_nyman_beurling_rh_bridge_roadmap.md`, start with NB0
4. **Reference**: [literature/INDEX.md](literature/INDEX.md) for papers

---

## Important Notes

⚠️ **H15 is a research problem, not a Lean task**. Do not attempt to formalize without understanding the mathematics first. See `h15_research_vs_lean_decision.md` in memory.

⚠️ **H14 has 3 independent pieces**, not 1. See `h14_honest_completion_status.md` in memory.

✅ **H13 is genuinely complete**. Use it as a reference for formalization style.

---

## Contact / Next Steps

- **Questions about the roadmap?** See memory files (authoritative)
- **Ready to work on H14?** Use scratchpad `CODEX_H14_COMPLETION_PROMPT.md`
- **Ready to start H15 diagnostics?** Reference [strategy/H15_RESEARCH_AGENDA.md](strategy/H15_RESEARCH_AGENDA.md), Phase 1
- **Ready to start Phase NB?** Memory `phase_nb_nyman_beurling_rh_bridge_roadmap.md`, begin with NB0

