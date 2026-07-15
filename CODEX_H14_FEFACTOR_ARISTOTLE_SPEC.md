# H14 FEFactor: Aristotle-Style Proof Search Specification

**Status:** Ready for automated proof search (Aristotle or equivalent)  
**Based on:** Verified proof from historical branch `codex/h14-vertical-growth-proof` (commit `51c10f6`)  
**Approach:** Formalization specification for RL-guided tactic search + Lean kernel verification  

---

## FORMALIZATION SPEC (Machine-Readable)

### Primary Theorem

```lean
theorem zetaFEFactor_normalized_interior_bound :
    ∀ σ t : ℝ, σ ∈ Set.Ioo (-1/2 : ℝ) (1/2 : ℝ) →
    t ≠ 0 →
    |zetaFEFactor (σ + Complex.I * t)| ≤ 
      (2 : ℝ) * (|t| + 2) ^ ((1 / 2 : ℝ) - σ)
```

### Boundary Conditions (Auxiliary Theorems)

```lean
theorem zetaFEFactor_normalized_half_norm (t : ℝ) (ht : t ≠ 0) :
    |zetaFEFactor (-1/2 + Complex.I * t)| ≤ 
      (2 : ℝ) * (|t| + 2) ^ 1
```

```lean
theorem zetaFEFactor_normalized_neg_half_norm (t : ℝ) (ht : t ≠ 0) :
    |zetaFEFactor (1/2 + Complex.I * t)| ≤ 
      (2 : ℝ) * (|t| + 2) ^ 0
```

---

## PROOF STRATEGY (High-Level Sketch for Search)

### Step 1: Normalize via Phragmén–Lindelöf Three-Lines
The key insight: to avoid the non-holomorphic `|t|` term in the normalization, use a **frozen-height Gaussian substitution**.

**Approach:**
- Define `frozenPLFunction(t, z) = zetaFEFactor(z) * exp(holomorphic_correction_factor)`
- This function is **holomorphic in z** for each fixed t
- The exponential correction has a **frozen base** (independent of Im z)
- Gaussian damping cancels the `|t|` growth at the boundary

**Formalization anchor:** `frozenPLFunction_diffContOnCl`

---

### Step 2: Bound Left Boundary (Re(s) = -1/2)
At the left edge `z = -1/2 + it`:
- The zeta FE factor grows like `|t|` (from Stirling's formula)
- The frozen normalization exactly compensates
- Result: `|frozenPLFunction| ≤ C * |t|` on left boundary

**Lemmas needed:**
- `zetaFEFactor_norm_le_on_closedStrip`
- `norm_Gamma_le_real_Gamma_re`
- `norm_cos_le_exp_abs_im`

---

### Step 3: Bound Right Boundary (Re(s) = 1/2)
At the right edge `z = 1/2 + it`:
- Zeta FE factor is bounded (Stirling)
- The frozen exponent contributes `exp(small_negative_exponent)`
- Result: `|frozenPLFunction| ≤ C` (polynomial in |t| with negative exponent)

**Lemmas needed:**
- `zetaFEFactor_norm_le_on_closedStrip` (right side)
- `exp_one_sixteenth_le`
- `plBase_log_shift_nonneg`

---

### Step 4: Apply Phragmén–Lindelöf
Standard interpolation theorem from complex analysis:
- Interior analytic function
- Bounds on both boundaries
- Interpolate to interior

**Lean machinery:** `Complex.HadamardThreeLines`

---

### Step 5: Back Out (Remove Frozen Normalization)
From `frozenPLFunction` bounds, recover bounds on `zetaFEFactor`:
- Divide out the exponential correction
- Verify exponent is preserved

**Key fact:** The Gaussian damping in the exponential exactly vanishes at `Im(z) = t`, leaving only the frozen base contribution.

---

## DEPENDENCIES & LEMMAS

### Existing (To Import/Use)
- `Mathlib.Analysis.Complex.Hadamard` — Phragmén–Lindelöf three-lines theorem
- `Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq` — Gaussian/exponential lemmas
- `RiemannHypothesis.Criteria.NymanBeurling.H14FEFactorBound` — Helper definitions

### To Prove (Proof Search Target)

```lean
-- Norm bounds for zeta FE factor on boundaries
private lemma zetaFEFactor_norm_le_on_closedStrip :
    ∀ z : ℂ, z ∈ verticalClosedStrip (-1/2) (1/2) →
    |zetaFEFactor z| ≤ (boundary_bound z : ℝ)
```

```lean
-- Gamma function bound (classical)
private lemma norm_Gamma_le_real_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re
```

```lean
-- Cosine bound on complex plane
private lemma norm_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im|
```

```lean
-- Positivity properties of the frozen base
private lemma plBase_pos (t : ℝ) :
    0 < plBase t

private lemma plBase_three_halves_le {t : ℝ} (ht : 1 ≤ |t|) :
    (3 / 2 : ℝ) ≤ plBase t

private lemma plBase_log_shift_nonneg {t : ℝ} (ht : 1 ≤ |t|) :
    0 ≤ Real.log (plBase t) - 1 / 16
```

```lean
-- Exponential bound (numerical verification)
private lemma exp_one_sixteenth_le :
    Real.exp (1 / 16 : ℝ) ≤ 16 / 15
```

```lean
-- Holomorphic continuation
private lemma frozenPLFunction_diffContOnCl (t : ℝ) :
    DiffContOnCl ℂ (frozenPLFunction t) 
      (verticalStrip (-1/2) (1/2))
```

```lean
-- Norm of the frozen function (norm computation)
private lemma norm_frozenPLFunction (t : ℝ) (z : ℂ) :
    ‖frozenPLFunction t z‖ =
      ‖zetaFEFactor z‖ *
        Real.exp ((z.re - 1 / 2) * (Real.log (plBase t) - 1 / 16)) *
        Real.exp ((z.re ^ 2 - (z.im - t) ^ 2) / 16 - 1 / 64)
```

```lean
-- Boundary estimates
private lemma frozenPLFunction_left_boundary (t : ℝ) (ht : 1 ≤ |t|) (z : ℂ) :
    z.re = -1/2 → ‖frozenPLFunction t z‖ ≤ boundary_left_bound t

private lemma frozenPLFunction_right_boundary (t : ℝ) (z : ℂ) :
    z.re = 1/2 → ‖frozenPLFunction t z‖ ≤ boundary_right_bound t
```

---

## SEARCH CONSTRAINTS & SUCCESS CRITERIA

### ✅ SUCCESS: Proof is Complete When
1. **All three theorems above are proved** (no `sorry` statements)
2. **No new axioms introduced** beyond:
   - `Classical.choice`
   - `propext`
   - `Quot.sound`
   - (Verify with `#print axioms zetaFEFactor_normalized_interior_bound`)
3. **Build passes:** `lake build RiemannHypothesis` completes successfully
4. **Verification passes:** `./scripts/verify.sh` reports all checks passed
5. **Mathematical equivalence:** Constants and exponents are **exactly**:
   - Constant: `C = 2` (not `2.1` or `3`)
   - Exponent: `(1/2 - σ)` (not `(1/3 - σ)`)
   - Bound form: `≤ C * (|t| + 2) ^ exponent` (not big-O or asymptotic)

### ❌ FAILURE: Reject Proofs That
- Introduce new axioms (other than the 3 above)
- Weaken the bound (e.g., change `≤` to weaker inequality)
- Use `sorry` anywhere in the three main theorems
- Change exponent order or quantifier structure

### 🚦 EVIDENCE-BASED PRUNING
- If a proof search branch explores >1000 tactics without progress: abandon and backtrack
- If a sub-lemma requires machinery not in Mathlib: mark as blocker and report
- If boundary computation diverges: suggest alternative parameterization

---

## REFERENCE: Historical Proof Exists

The proof that should guide this search exists at:
```
/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/
  .worktrees/h14-vertical-growth-proof/
  RiemannHypothesis/Criteria/NymanBeurling/H14FEFactorPL.lean
```

**Use this as a reference for:**
- Tactic sequence (not verbatim, but structure)
- Lemma names and definitions
- Proof organization

**Do NOT:**
- Copy-paste tactics wholesale (learn the structure, find your own tactics)
- Assume tactic names are stable across Lean versions
- Use deprecated Mathlib lemmas

---

## INTEGRATION NOTES

### For Aristotle (or Equivalent RL System)
1. Submit this spec to the proof search engine
2. Provide the lemma list + Mathlib context
3. Let it explore tactic space
4. Collect all candidate proofs with success metrics
5. Return best proof + search cost metrics

### For Fallback (Manual Codex)
1. Use this spec as the **formalization skeleton**
2. Ask Claude/Codex to fill in one lemma at a time
3. Verify each lemma independently
4. Combine into final proof

### For Verification
```bash
# Build and verify
lake build RiemannHypothesis

# Check axioms (should see only Classical.choice, propext, Quot.sound)
lean --print-axioms RiemannHypothesis.Criteria.NymanBeurling.H14FEFactorPL

# Run project verification gate
./scripts/verify.sh HEAD
```

---

## Timeline

**Automated search (Aristotle):**
- Formalization spec: 1 day (already done)
- Search: 1–3 days (depending on search depth)
- Verification: 1 day
- Extraction: 1 day
- **Total: ~1 week**

**Manual fallback (Codex):**
- Formalization: 1 week
- Proof writing: 2–3 weeks
- Verification: 1 week
- **Total: 4–5 weeks**

---

**This specification is machine-readable and human-auditable.**  
It is ready for submission to any proof search system that understands Lean 4 tactic syntax.

