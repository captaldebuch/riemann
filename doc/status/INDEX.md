# Project Status — Roadmaps and Current State

Overall project state, timelines, and roadmaps.

**Current audited branch map:** `ACTIVE_BRANCHES.md` (15 July 2026).

---

## README.md
General project overview and quick-start guide.

---

## PROJECT_STATUS.md
Detailed metrics and completion estimate:

| Component | Status | Details |
|-----------|--------|---------|
| H13 (Vasyunin bridge) | ✅ Complete | Substitution axiom discharged and merged in `24f44cc`. |
| H14 (Linear Möbius) | ✅ Complete in reference branch | Audited at `b499bf2`; classical unconditional Mertens decay, not a square-root bound. |
| H15 (Quadratic interaction) | ❌ Open research | BCF amplitude diagonalized; centered Estermann/Kuznetsov main-term theorem remains missing. |
| NB2 | ✅ Complete in active package | Unconditional base Mellin formula and dilations. |
| NB Fields 1–2 | ✅ Historical proofs audited | Core endpoints clean; active-package port still required. |
| NB forward bridge | 🟡 Conditional | Current wrapper still depends on `RH.Basic.zero_symmetry`. |
| **RH completion percentage** | **Not assigned** | H15 and the remaining NB bridge contain genuine mathematical gaps. |

---

## Master Roadmap (To Be Moved Here)

**File**: `MASTER_ROADMAP_TO_RH.md` (currently in scratchpad)

Complete chain from H13 to RH:
```
H13 (done) → H14 (done) → H15 (open) → Criterion → NB3–NB5 → RH
```

With exact timelines and effort estimates for each piece.

---

## Memory References

Core strategic decisions are stored in memory:

- `h15_formulation_error_audit.md` — Why uniform sawtooth is false
- `h15_research_vs_lean_decision.md` — Decision to shift H15 to research
- `h14_honest_completion_status.md` — Three pieces, not one (FEFactor, Jensen, Perron)
- `phase_nb_nyman_beurling_rh_bridge_roadmap.md` — Complete NB0–NB7 breakdown

These are the authoritative decisions. Refer to them for project direction.

---

## Codex Prompts (To Be Moved Here)

Pre-written, ready-to-use prompts for Codex:

- `CODEX_H14_COMPLETION_PROMPT.md` — FEFactor (Routes A/B/C)
- (H15 diagnostics prompt — to be written once Phase 1 ready)

Location: Scratchpad (to be organized into `doc/prompts/`)

---

## How to Use This Folder

1. **Start here** for the big picture (README.md → PROJECT_STATUS.md)
2. **Check memory** for strategic decisions (h14_honest_... , h15_research_vs_...)
3. **Go to doc/strategy/** for detailed research plans
4. **Go to doc/technical/** for the mathematics analysis
5. **Go to doc/literature/** for the papers
