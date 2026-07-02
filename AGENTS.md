# Agent Instructions

Instructions for AI agents (Google Antigravity, Claude Code, etc.) working on this project.

## What this project is

A Lean 4 formal verification project targeting the Riemann Hypothesis.
The goal is **not** to prove RH in one shot, but to:
1. Formalize RH-equivalent criteria
2. Identify the exact "missing lemma" in each approach
3. Let Aristotle search for bridge lemmas between criteria

## Key files to know

- `RiemannHypothesis/Basic/CriticalStrip.lean` — defines `RiemannHypothesis` as a Lean `Prop`
- `RiemannHypothesis/Criteria/NymanBeurling.lean` — **best first target**, has the key sorry stubs
- `RiemannHypothesis/Discovery/BridgeLemmas.lean` — where Aristotle tries to fill sorries
- `experiments/gram_matrix_search.py` — generates numerical Gram certificates

## Coding conventions

- Every `sorry` is intentional — it marks a genuine open mathematical problem
- Use `conjecture` (which is `theorem` with `sorry`) for candidate lemmas under investigation
- Do not remove `sorry` unless you have a real Lean proof
- Keep axioms minimal — prefer `sorry` in theorem body over `axiom` declarations
- Add mutation comments when weakening a statement: `-- REPAIR: added compact-support hypothesis`

## Workflow for adding a new bridge lemma

1. State the lemma in `Discovery/BridgeLemmas.lean`
2. Lean type-check: does the statement parse?
3. Run counterexample search: `python experiments/gram_matrix_search.py --N 20`
4. Send the sorry stub to Aristotle
5. If Aristotle fails: mutate the statement (weaker hypothesis or stronger conclusion)
6. When proved: move to the appropriate `Criteria/` or `Finite/` file

## Priority order

1. `NymanBeurling.lean` — `rh_from_verified_approximation_rate`
2. `Finite/TailBounds.lean` — `finite_positivity_plus_tail_control_implies_RH`
3. `Criteria/Li.lean` — `total_positivity_implies_li_positive`
4. `Finite/GramMatrices.lean` — `gram_positive_semidefinite` (needs SDP certificate)

## What NOT to do

- Do not try to prove `RiemannHypothesis` directly in one theorem
- Do not add axioms without a comment explaining why the axiom is expected to be true
- Do not use `native_decide` on large computations
- Do not replace `sorry` with `trivial` to make the build pass

## Aristotle-specific instructions

When sending files to Aristotle:
- Send individual `.lean` files from `Discovery/` or `Criteria/`
- Ask it to "fill the sorry" for one specific theorem at a time
- If it produces a proof, verify with `lake build` before accepting
- If it fails, note which tactic it got stuck on — that identifies the missing infrastructure
