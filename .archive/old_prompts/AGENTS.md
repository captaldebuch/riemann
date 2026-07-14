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

## Multi-tool coordination protocol

This project is worked on by multiple AI tools (Gemini/Google Antigravity, Codex, Claude Code)
across separate sessions, plus a human. On 2026-07-02, a tool committed directly to `main`
with a change that looked complete ("built, verified, committed") but silently altered the
declared numeric value of several pre-existing constants, breaking files elsewhere in the repo
that depended on those exact values. The tool's own success claim did not catch this. This
section exists so that never happens silently again, regardless of which tool is working.

**Rule: only one tool works on the repo at a time. Never run two tools' sessions concurrently
against the same working tree or a shared build cache** — a symlinked/shared `.lake` between
two concurrent sessions also caused real build corruption the same day.

### Workflow

1. **Start every session from a tagged, verified commit.** Look for the most recent
   `verified-*` git tag (`git tag -l 'verified-*' --sort=-creatordate`) and start your branch
   there, not from whatever `main` happens to be if it hasn't been tagged since the last change.
2. **Work on a dedicated branch or git worktree, never directly on `main`.**
   `git worktree add <path> -b <branch-name>` gives a tool its own working directory without
   duplicating the git history. If a tool can't use worktrees, a plain `git checkout -b`
   dedicated branch is the fallback — just don't work with an unclean/mixed working tree.
3. **If using a worktree, copy `.lake` — never symlink it.** Each worktree needs its own real
   copy of the ~15GB build cache (`cp -R <main-repo>/.lake .lake`) or it will either try to
   rebuild Mathlib from scratch (hours) or, if symlinked, silently corrupt the shared cache when
   two sessions touch it around the same time.
4. **Commit after every logically-complete, buildable chunk.** Never leave a large amount of
   work uncommitted for long — this project has lost real work twice from an agent's own
   careless `git reset`/branch-rename sequence. Never run `git reset`, `git clean`, `checkout --`,
   or a branch rename unless `git status --short` is already clean.
5. **Before merging to `main`, run `./scripts/verify.sh`** (compares against the latest
   `verified-*` tag by default). It must exit 0. It checks: full build success, whether any
   pre-existing `def`'s declared value changed (the exact failure mode from 2026-07-02),
   axiom/sorry/native_decide counts, and runs `#print axioms` on every new theorem to catch a
   silent `sorryAx` dependency.
6. **Only merge (fast-forward when possible) after `verify.sh` passes.** Tag meaningful
   milestones: `git tag verified-<short-description> <commit>`.
7. **The next tool's session starts from that new tag**, not from an unreviewed branch.

Do not trust a tool's own "done / verified / built successfully" claim as sufficient — it must
be corroborated by actually running `./scripts/verify.sh` (or the equivalent manual checks)
against the live repository before anything merges to `main`.
