# Aristotle Pipeline: AI-Guided Proof Search for RH Formalization

**Decision Date:** 2026-07-14  
**Rationale:** Replace manual Codex prompts with systematic Aristotle-style proof search pipeline

---

## The Pipeline (Why It's Better)

### Current: Manual Codex Approach
```
Human writes Codex prompt
  ↓
Claude/Codex suggests Lean tactics
  ↓
Human reviews + iterates
  ↓
Eventually: proof (or gives up)
```

**Problems:**
- Slow (human in the loop at each iteration)
- Depends on developer intuition
- May miss non-obvious proof strategies
- Hard to know when to stop trying a route

---

### New: Aristotle-Style Automated Search
```
1. FORMALIZE (human mathematical work)
   State theorem precisely in Lean
   Include all lemmas, bounds, quantifiers
   Ensure semantic correctness
   
2. SPECIFY (automated preparation)
   Lean parser confirms syntax
   Extract proof structure (which lemmas are needed)
   Generate proof search context
   
3. EXPLORE (AI-guided search)
   RL-trained model explores tactic space
   Uses Lean's tactic language as search grammar
   Explores thousands of candidate proofs
   Learns from successful sub-proofs
   
4. VERIFY (Lean kernel)
   Candidate proof submitted to Lean
   Kernel checks correctness in ~1 minute
   No human judgment needed
   
5. EXTRACT (human translation)
   If successful: parse tactic proof
   Translate back to human-readable math
   Document key insights
   Publish
```

**Advantages:**
- ✅ Automated exploration (no human in the loop)
- ✅ Exhaustive within search space (doesn't miss strategies)
- ✅ Verification is mechanical (can't fake correctness)
- ✅ Can run in parallel on multiple sub-proofs
- ✅ Natural breakpoints (succeed/fail clearly)

---

## Why This Applies to Our Project

### H14 FEFactor (Already Proven, Now Formalizing)
**Current:** "Write Codex prompt, manually port proof to Lean"  
**Better:** "Specify FEFactor bound in Lean, run Aristotle to find tactics"

The *mathematics* is done (verified proof exists on branch `codex/h14-vertical-growth-proof`).  
The problem is: *find Lean tactics that express this mathematics*.  
This is **exactly what Aristotle does well**.

---

### H14 Borel-Jensen & Perron (Classical, Not Yet Fully Formalized)
**Current:** "Codex writes Lean, hope it works"  
**Better:** "Formalize classical bounds precisely, Aristotle finds proof"

Both are classical theorems (exist in literature).  
Formalize them rigorously in Lean → run Aristotle → verify.

---

### H15 (Open Research, Needs Diagnostics First)
**Current:** "Hope Lean search finds a new proof"  
**Better:** "Phase 1: identify structure via diagnostics. Phase 2: formalize that structure. Phase 3: run Aristotle."

H15 is hard because we don't know the *right* structure yet.  
But once Phase 1 diagnostics clarify it, formalize it precisely, then Aristotle can search systematically.

---

### Phase NB (Formalization, Not Research)
**Current:** "Codex writes Lean"  
**Better:** "Formalize classical machinery, Aristotle fills in routine lemmas"

Phase NB is mostly "combine existing classical results into one narrative."  
This is formalization work (not proving new theorems).  
Aristotle is overkill here, but Codex-style assistance is still useful.

---

## Integration Strategy

### Immediate (H14 FEFactor Reconstruction)
1. ✅ Formalize H14 FEFactor bound precisely in Lean (already have the math)
2. 🔄 Instead of manual Codex, use **Aristotle-style proof search**:
   - Submit spec to Aristotle (or equivalent: Claude + reinforcement learning)
   - Let it explore tactic space
   - Verify successful proofs in Lean kernel
   - Extract human-readable version

### Medium-term (H14 Borel-Jensen & Perron)
1. Formalize classical bounds precisely
2. Use Aristotle pipeline for each piece
3. Run in parallel (3 pieces simultaneously)

### H15 Research → Formalization
1. Phase 1–2: Diagnostics + route selection (human mathematical work)
2. Phase 3a: Formalize the winning structure precisely
3. Phase 3b: **Aristotle searches** for proof within that structure
4. Phase 4: Extract & publish

### Phase NB (Lower Priority for Aristotle)
- Classical, well-understood formalization
- Codex prompts are fine here
- Aristotle overkill unless we hit blockers

---

## What "Aristotle" Means for This Project

We have three options:

### Option A: Use Harmonic's Actual Aristotle
**Pros:** Purpose-built, proven track record (Erdős problems)  
**Cons:** Proprietary, expensive, limited access  
**Timeline:** 6 months to licensing deal (uncertain)

### Option B: Build an Aristotle-Like System
**Using:** Claude + reinforcement learning over Lean proof corpus + systematic search  
**Pros:** Open-source, we control the pipeline, can adapt to our theorems  
**Cons:** Engineering effort (4–8 weeks to implement)  
**Timeline:** Ready in 2–3 months

### Option C: Hybrid (Recommended)
**Now:** Use Codex prompts + manual tactics for H14 FEFactor  
**Parallel:** Build lightweight Aristotle-equivalent using Claude + Lean tactic search  
**Future:** Transition H14/H15 to automated pipeline once ready

---

## Codex Prompt Redesign

### Current H14 FEFactor Prompt
```
"Port this proof from historical branch to modern main.
Here's what needs to be proved:
[mathematical statement]
Here's the approach:
[tactic sketch]
Make sure: no new axioms, complete proof, passes verify.sh"
```

**Problem:** Assumes human will fill in tactic details.

---

### New Aristotle-Oriented Prompt
```
FORMALIZATION SPEC (for automated search):
=====================================
Theorem zetaFEFactor_normalized_interior_bound:
  [precise Lean 4 statement]
  [all quantifiers explicit]
  [dependencies listed]

PROOF SKETCH (search constraints):
=====================================
High-level structure:
  1. Apply Phragmén–Lindelöf three-lines
  2. Bound left boundary via Stirling
  3. Bound right boundary via target exponent
  4. Interpolate

Key lemmas required:
  - norm_Gamma_le_real_Gamma_re
  - norm_cos_le_exp_abs_im
  - frozenPLFunction_diffContOnCl
  [...]

SEARCH CONTEXT:
=====================================
Goal: Find tactic proof of the above.
Available lemmas: [Mathlib + local defs]
Success criteria: 
  - Proof is complete (no sorry)
  - No new axioms (other than Classical.choice, propext, Quot.sound)
  - Passes `lake build` and `./scripts/verify.sh`
  - Matches original mathematical bound exactly

CONSTRAINTS:
- Do NOT weaken the bound
- Preserve the constant C = 2
- Preserve quantifier order
- Preserve exponent 1/2 - σ
```

**This is submittable to Aristotle** (or any RL-trained proof search system).  
Human doesn't need to guess tactics—system explores systematically.

---

## Why This Matters for H15

H15 is currently "open research" because we don't know the right proof structure.  
**But once Phase 1 diagnostics identify the structure**, we can:

1. Formalize it precisely in Lean (with sorry placeholders)
2. Ask Aristotle to fill in the sorry proofs
3. Verify in Lean kernel

This is much more efficient than:
1. Manually trying different Lean approaches
2. Hoping one works
3. Giving up if it doesn't

---

## Timeline Impact

### Manual Codex Pipeline
- H14 FEFactor: 2–3 weeks of human Lean work
- H14 Borel-Jensen: 3–4 weeks
- H14 Perron: 3–4 weeks
- **Total: 8–11 weeks**

### Aristotle Pipeline
- H14 FEFactor: 1 week formalization + 1 day search + 1 day verification = **2 days actual work**
- H14 Borel-Jensen: 3 days formalization + 3 days search = **1 week**
- H14 Perron: 3 days formalization + 3 days search = **1 week**
- **Total: ~3 weeks** (including overhead, parallel work)

**2–3× speedup**, and you get systematic exploration instead of guesswork.

---

## Risks & Mitigation

### Risk 1: "Aristotle outputs unreadable proofs"
**Real:** Erdős #728 proof is 4,300 lines of dense tactics  
**Mitigation:** Phase 5 (extract) translates back to math. If readable proof emerges, great. If not, we have a verified proof anyway.

### Risk 2: "Search doesn't find proof"
**Real:** H15 is genuinely hard; Aristotle can only search what's in Mathlib  
**Mitigation:** This tells us *when to stop trying this structure*. Phase 1 diagnostics then suggests alternative structure.

### Risk 3: "We don't have Aristotle access"
**Real:** Harmonic's Aristotle is proprietary  
**Mitigation:** Build lightweight equivalent using Claude + RL tactic search (doable in 4–8 weeks)

---

## Recommended Next Steps

### Phase 1: Pilot (H14 FEFactor)
1. Take existing proof (from `codex/h14-vertical-growth-proof` branch)
2. Formalize into clean Lean 4 (1 week)
3. Write Aristotle-style spec (1 day)
4. **Choice point:**
   - Option A: Submit to Harmonic's Aristotle (if we can)
   - Option B: Use Claude + tactic search (simpler, immediate)
   - Option C: Manual Codex for now, build Aristotle for later

### Phase 2: Scale (H14 Borel-Jensen + Perron)
1. Formalize both theorems
2. Write search specs
3. Run in parallel on Aristotle system
4. Verify + extract

### Phase 3: H15 (Once Phase 1 Diagnostics Clear)
1. Phase 1: Identify winning structure
2. Formalize that structure in Lean
3. Use Aristotle to fill in proofs
4. Or: use failure to identify next structure to try

---

## Decision Point

**Current project trajectory:** Manual Codex + manual Lean work (8–11 weeks)  
**Better trajectory:** Aristotle pipeline + systematic search (3 weeks + parallelization)

**Recommendation:** Adopt Aristotle as standard pipeline for all Lean work starting with H14 FEFactor.

This aligns with modern formal verification best practices and makes the project "proof-search first, manual tactics second."

---

**Last updated:** 2026-07-14
