# Building & Verifying Lean Proofs

## Prerequisites

- **Lean 4** — See [Lean installation guide](https://lean-lang.org/lean4/doc/quickstart.html)
- **Lake** — Lean package manager (included with Lean 4)
- **Git** — For cloning and managing code

## Quick Start

```bash
# Clone the repository
git clone https://github.com/xavierfresquet/riemann-hypothesis.git
cd riemann-hypothesis

# Build the Lean library
lake build NBMellinTools

# Verify proofs
mathlib/verify.sh
```

## Build Steps

### 1. Install Lean 4
```bash
# macOS
brew install elan-init
elan init  # Follow prompts, choose Lean 4

# Linux
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan init

# Windows
# Download installer from https://lean-lang.org/lean4/doc/quickstart.html
```

### 2. Set Lean Version
```bash
cd riemann-hypothesis
elan override set $(cat lean-toolchain)
# This ensures you're using the same Lean 4 version as the project
```

### 3. Build the Library
```bash
lake build NBMellinTools

# Output should end with:
# ✓ NBMellinTools
# ✓ Tests  (if included)
```

### 4. Run Tests (if available)
```bash
lake test NBMellinTools
```

---

## Verifying Axioms & Sorries

**Critical:** All formalized proofs should have:
- **Zero new axioms** (only Lean.Prelude + Mathlib foundations)
- **Zero `sorry` statements** (incomplete proofs)

### Check for Axioms
```bash
# Search for any axiom declarations in proofs
grep -r "^axiom " proofs/

# Should return only standard Lean/Mathlib axioms via:
grep -r "axiom" .lake/build/lib/lean/NBMellinTools/*.olean | head

# Expected (safe) axioms:
# - Lean.Prelude
# - Mathlib.Logic.Equiv (propext, choice, Quot.sound)
```

### Check for Sorries
```bash
# Search for incomplete proofs
grep -r "sorry" proofs/

# Should return NOTHING if fully verified
# If found, those files are still under development
```

### Run Full Verification Suite
```bash
# Run all checks including:
# - Build verification
# - Axiom audit
# - Syntax checking
./mathlib/verify.sh

# Output should show:
# ✓ Build successful
# ✓ No new axioms
# ✓ No sorries
```

---

## Understanding the Project Structure

```
proofs/
├── NBMellinTools/           # Main library
│   ├── LogPullback.lean     # NB0-NB1: Mellin foundations
│   ├── MellinEvaluation.lean # NB2: Base formula
│   ├── BaezDuarteTail.lean  # NB3-NB5: Hardy analysis, zero detection
│   └── H15BCF/              # Phase 7b: BCF asymptotic formalization
│       ├── Definitions.lean
│       ├── Phase 1-7 modules (list below)
│       └── Phase 7b modules (list below)
└── lakefile.toml           # Build configuration
```

## H15 Phase Breakdown

### Phases 1–7 (Complete)
- **Phase 1:** Dirichlet polynomial definitions
- **Phase 2–3:** Zeta interpolation & contour analysis
- **Phase 4–5:** Boundary estimates & residue extraction
- **Phase 6:** Multi-hole rectangle theorem & disk assembly
- **Phase 7:** Limit assembly & normalized asymptotic

### Phase 7b (In Progress)
**What's proved:**
- ✅ Finite structures (multiplicities, truncations, products)
- ✅ Weierstrass bridge (majorants → convergence)
- ✅ Hadamard endpoint special values
- ✅ Final analytic assembly (logical chain)
- ✅ Genus-one majorant reduction

**What remains:**
- ❌ Riemann–von Mangoldt inverse-square bounds
- ❌ Logarithmic-derivative convergence
- ❌ ξ factorization identification
- ❌ Integrated BCF cancellation

---

## Building Individual Modules

```bash
# Build a specific module
lake build NBMellinTools:H15BCF.GenusOneMajorantReduction

# Import a module for exploration
lake env lean
#> import NBMellinTools.H15BCF.GenusOneMajorantReduction
#> #check GenusOneMajorantReduction
```

---

## Troubleshooting

### Build Fails: "Unknown package"
```bash
# Update dependencies
lake update
lake build NBMellinTools
```

### Build Fails: "Lean version mismatch"
```bash
# Check your Lean version
lean --version

# Should match: cat lean-toolchain

# Fix version
elan override set $(cat lean-toolchain)
```

### Build Fails: "Out of memory"
```bash
# Reduce parallel jobs
lake build NBMellinTools -j 2
```

### Proof Shows `sorry`
This means the proof is incomplete. Search for which file:
```bash
grep -n "sorry" proofs/NBMellinTools/H15BCF/*.lean
```

Contact the maintainers with the file and commit hash.

---

## Development Workflow

### Contributing a New Proof

1. **Create a feature branch**
```bash
git worktree add .worktrees/feature-name
cd .worktrees/feature-name
```

2. **Develop in a new module**
```lean
-- proofs/NBMellinTools/H15BCF/NewTheorem.lean
import NBMellinTools.H15BCF.Definitions

theorem new_result : ∃ x, property x := by
  sorry  -- develop here
```

3. **Build and test**
```bash
lake build NBMellinTools
# Iterate until sorry is replaced with proof
```

4. **Verify no new axioms**
```bash
./mathlib/verify.sh
```

5. **Merge back to main**
```bash
cd ..
git checkout main
git merge feature-name
git worktree remove feature-name
git push
```

---

## Performance Tips

### Speed Up Builds
```bash
# Use parallel jobs (default: number of CPU cores)
lake build NBMellinTools -j 8

# Cache intermediate results
lake build NBMellinTools --incremental
```

### Explore Proofs Interactively
```bash
lake env lean --stdin
#> import NBMellinTools.H15BCF.GenusOneProduct
#> #check GenusOneProduct
#> #print GenusOneProduct
#> open NBMellinTools.H15BCF in ...
```

---

## Documentation

### In-Code Documentation
Each module starts with:
```lean
/-!
# Module Title
Brief description of what this module proves.

## Key Theorems
- `theorem_name`: What it proves
- `another_theorem`: ...

## References
- Titchmarsh: "The Theory of the Riemann Zeta Function"
- Classical paper citation
-/
```

### Read Generated Docs
```bash
lake build NBMellinTools:docs
open .lake/build/doc/index.html
```

---

## Axiom Audit Details

The axiom audit checks for:

1. **No new axioms** (only system Lean axioms)
   ```lean
   -- OK: Uses Lean.Prelude only
   theorem ok_result : 2 + 2 = 4 := by norm_num
   ```

2. **No unproven hypotheses**
   ```lean
   -- BAD:
   axiom bad_axiom : RiemannHypothesis  -- Don't add!
   
   -- OK:
   theorem uses_rh (h_rh : RiemannHypothesis) : SomeConsequence := by
     exact from_rh h_rh  -- Explicitly hypothesis-dependent
   ```

3. **No sorry (incomplete proofs)**
   ```lean
   -- BAD:
   theorem incomplete : SomeResult := sorry
   
   -- OK:
   theorem complete : SomeResult := by
     exact proof_here  -- or tactic proof
   ```

---

## Publishing Proofs

When ready to publish:

```bash
# Create archive
tar -czf riemann-proofs.tar.gz proofs/ lakefile.toml lean-toolchain BUILD.md

# Verify everything before publishing
./mathlib/verify.sh  # Must pass

# Upload to:
# - Zenodo (for DOI/archival)
# - GitHub release
# - ACM/IEEE (if submitting paper)
```

---

## Support & Questions

- **Issues:** [GitHub Issues](https://github.com/xavierfresquet/riemann-hypothesis/issues)
- **Discussions:** [GitHub Discussions](https://github.com/xavierfresquet/riemann-hypothesis/discussions)
- **Email:** xavier.fresquet@sorbonne.ae

---

**Last updated:** July 17, 2026
