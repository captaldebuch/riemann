# Codex: Port H14 FEFactor Proof to Current Main

## Context

**Historical state:** Branch `codex/h14-vertical-growth-proof` (commit `51c10f6`) contains a complete, verified proof of the FEFactor vertical interpolation bound for H14. The proof is **mathematically complete, axiom-free (no new axioms introduced), and builds successfully** (8,639-job lake build, all checks passed).

**Current main state:** Main branch has archived the full `RiemannHypothesis` library and now builds only `NBMellinTools`. This was a deliberate architectural decision to focus on the Nyman–Beurling bridge machinery.

**Task:** Port the FEFactor proof into a clean, self-contained Lean 4 module that:
1. Works on current `main` branch (integrates with NBMellinTools context)
2. Preserves all mathematical content from the historical proof
3. Uses identical lemma names, theorem statements, and proof structure
4. Introduces **zero new axioms** (verify with `#print axioms`)
5. Passes `lake build` and `./scripts/verify.sh`
6. Stands alone as proof-of-concept for H14 reconstruction

## The Historical Proof (What to Port)

**File:** `.worktrees/h14-vertical-growth-proof/RiemannHypothesis/Criteria/NymanBeurling/H14FEFactorPL.lean` (474 lines)

**Key components:**
- **Namespace:** `RH.Criteria.NymanBeurling.H14ZetaFETransport`
- **Main theorem:** `zetaFEFactor_normalized_interior_bound` (the result)
- **Supporting theorems:**
  - `zetaFEFactor_normalized_half_norm`
  - `zetaFEFactor_normalized_neg_half_norm`

**Mathematical content:**
- Normalizes the FE factor `zetaFEFactor(σ+it) / (|t|+2)^(1/2-σ)` by applying Phragmén–Lindelöf three-lines
- Introduces a frozen height Gaussian normalization to preserve holomorphicity
- Bounds both boundary (left: `|t|` growth, right: Stirling) and interior (interpolation)
- Preserves the original target bound with exponent `1/2-σ` and constant `C=2`

**Dependencies (from the historical file):**
```lean
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import RiemannHypothesis.Criteria.NymanBeurling.H14FEFactorBound
```

Note: `H14FEFactorBound` is a helper module (also on historical branch). You may need to inline its definitions or create it as a companion file.

## Deliverable Structure

Create a new file:
```
mathlib/NBMellinTools/H14FEFactorReconstruction.lean
```

This file should contain:
1. All necessary imports (from Mathlib; adapt for current structure)
2. The complete `H14ZetaFETransport` namespace with all lemmas
3. The three main theorems (half_norm, neg_half_norm, interior_bound)
4. Proof by proof from the historical version
5. **No `sorry` statements**
6. **No new axioms** beyond what's already in the repo

### Integration checklist:
- [ ] File compiles standalone: `lake build mathlib.NBMellinTools.H14FEFactorReconstruction`
- [ ] No new axioms: `#print axioms` output matches baseline (propext, Classical.choice, Quot.sound only)
- [ ] All three main theorems type-check and have complete proofs
- [ ] Can be imported into a test file without errors

## Strategy

### Phase 1: Direct Port (80% of work)
Copy the proof verbatim from the historical file. Adjust imports as needed for current Mathlib versions.

**Key points:**
- The proof uses `Complex.HadamardThreeLines`, which should be in current Mathlib
- Lemmas on `Real.Gamma`, `Complex.cos`, `Complex.exp` are stable
- `DiffContOnCl` and `verticalStrip` defs may need checking—verify they exist in current Mathlib or in NBMellinTools

### Phase 2: Dependency Resolution
Check what's in `H14FEFactorBound` (the helper module). If it's complex:
- **Option A:** Port it as `H14FEFactorBoundCompanion.lean` first
- **Option B:** Inline critical defs (e.g., `zetaFEFactor` def, `verticalStrip` def) directly into the new file

### Phase 3: Verification
```bash
lake build
./scripts/verify.sh HEAD
```

Ensure:
- Zero axiom additions
- Zero `sorry` statements in the file
- All imports resolved

## Success Criteria

✅ **Minimum (proof-ready):**
- File compiles without errors
- All three main theorems present and complete
- `lake build` passes (8,000+ jobs)

✅ **Full (publication-ready):**
- Above, plus
- `./scripts/verify.sh HEAD` passes all checks
- Axiom count unchanged from baseline
- Can be merged to main as a feature branch

## Reference Materials

**Historical proof location:**
```
/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/.worktrees/h14-vertical-growth-proof/RiemannHypothesis/Criteria/NymanBeurling/H14FEFactorPL.lean
```

**Companion file (if needed):**
```
/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/.worktrees/h14-vertical-growth-proof/RiemannHypothesis/Criteria/NymanBeurling/H14FEFactorBound.lean
```

**Current NBMellinTools structure:**
```
mathlib/NBMellinTools/
├── LogPullback.lean
├── MellinEvaluation.lean
├── BaezDuarteTail.lean
└── (new) H14FEFactorReconstruction.lean
```

## Notes

- This is a **proof port, not a redesign.** Preserve the historical structure, lemma organization, and proof approaches.
- The goal is **not** to complete H14 (Borel–Jensen and Perron remain open). This is one of three pieces, scoped and finite.
- Treat this as a **worked example** of how classical analytic proofs fit into Lean 4. Once complete, it can guide the other two pieces.
- If you encounter new Mathlib API changes (e.g., namespace renames, lemma deprecations), adapt minimally. Document any changes in comments.

---

**Start date:** 2026-07-14  
**Estimated duration:** 1–2 weeks (proof porting + dependency resolution + verification)  
**Owner:** Codex / Human collaboration  
**Status:** Ready for handoff

