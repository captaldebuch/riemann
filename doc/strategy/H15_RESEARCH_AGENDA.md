# H15 Research Agenda — Shifting from Lean Formalization to Analytic Problem

**Decision Date**: 2026-07-14  
**Reason**: H15 is a pure research problem, not a Lean completion task

---

## What Changed

### Before (Lean-Centric):
- Treat H15 as "complete the axiom proof in Lean"
- Use sawtooth proxies and uniform bounds
- Try standard tools (Vaughan, van der Corput)
- Hope for incremental Lean progress

### After (Research-Centric):
- Treat H15 as a pure analytic problem
- Work with exact centered bilinear structure
- Map three deep proof routes
- Aim for either proof OR honest conjecture + conditional theorem

---

## The Problem in One Sentence

**Can one prove that the centered Möbius-weighted bilinear quadratic Vasyunin/BBLS residual is $O(1/\log N)$?**

This is genuinely hard. It may require new ideas. But it must be attacked honestly—not via false simplifications.

---

## What This Means for the Project

### ✅ H13 Remains Valid
- Fully proved in Lean
- Can be cited as genuine result
- Not affected by H15 status

### 🟡 H14 Remains Valid (Mostly)
- ~80% complete in Lean
- Clear remaining piece (Z3: zeta vertical growth)
- Not dependent on H15

### ❌ H15 Transitions to Research
- Remove from Lean "proof tasks"
- Archive current Lean code as scaffolding
- Focus on mathematical understanding
- Target: prove or rigorously formulate as conjecture

### 🟢 Criterion Wiring Remains Valid
- Conditional theorem is correct
- Will apply once H13+H14+H15 are settled
- No changes needed

---

## The Next Steps

### Immediate (This Week):
1. **Freeze exact problem** (`H15_EXACT_PROBLEM.tex`)
2. **Run diagnostics** (`H15_Cancellation_Atlas.ipynb`) — 7 decompositions
3. **Identify cancellation structure** — which decomposition reveals it?

### Medium-term (2–4 weeks):
4. **Formulate Route 1** (Estermann remainder) precisely
5. **Locate Route 2** (Bettin–Drappeau reciprocity) in literature
6. **Derive Route 3** (Dirichlet-polynomial energy identity)

### Long-term (4–12 weeks):
7. **Pursue most promising route** with domain experts
8. **Either prove H15 or formalize as open conjecture**
9. **Publish conditional theorem** regardless of outcome

---

## Why This Is the Right Approach

**Mathematical integrity:**
- The problem deserves honest treatment, not Lean shortcuts
- False simplifications (sawtooth, uniform bounds, gcd strata) have been ruled out by derivation
- The real cancellation is global, signed, and centered

**Intellectual honesty:**
- Admit that this is hard and may be open
- Document what's known and what's unknown
- Share the problem with experts rather than hide it in Lean

**Research value:**
- Even if H15 remains unproven, the exact formulation + diagnostics are contributions
- The three proof routes provide a research map for the community
- The conditional theorem stands regardless: "H13+H14+H15 ⟹ RH"

**Realistic timeline:**
- Lean proof search without understanding: months, likely futile
- Collaborative research with understanding: 4–12 weeks for breakthrough, or honest conjecture

---

## Lean Code Status

The current Lean code is **research scaffolding**, not a proof path:

```
mathlib/NBMellinTools/H15_RouteA.lean (201 lines)
├─ 1 partial theorem (with sorry)
├─ 10 axioms (research goals)
└─ 0 proofs of H15
```

**This code will NOT become a proof.** Instead:

1. Archive it as example/reference
2. Keep it compiling to show the structure
3. Use it as a Lean formalization of the exact problem
4. Update it once analytic proof is in hand (if ever)

---

## Expert Consultation

Prepare a document for experts:

**"The H15 Cancellation Problem: A Precise Open Question in Analytic Number Theory Arising from the Nyman–Beurling Criterion"**

Send to specialists in:
- Vasyunin cotangent sums
- Estermann zeta function
- Dirichlet polynomial approximation
- Möbius-weighted averages
- Bilinear multiplicative-function estimates

Ask:
1. Have you seen this problem before?
2. Which of the three routes (Estermann, reciprocity, Dirichlet) looks most promising?
3. What are the key references we're missing?

---

## Final Status

| Component | Where It Stands |
|-----------|-----------------|
| H13 | ✅ Proved (Lean) — archived, complete |
| H14 | 🟡 ~80% (Lean) — clear remaining piece |
| H15 | ❌ Open (Analytic) — research in progress |
| Bridge | ❌ Open (Analytic) — separate problem |
| Criterion | 🟢 Conditional (Lean) — correct, stands as-is |

**The Nyman–Beurling route to RH via H13+H14+H15 is structurally sound but mathematically incomplete.**

The project's role: Map the problem precisely and provide conditional theorems. Leave the hardest part (H15) to research collaboration.

