#!/usr/bin/env bash
# scripts/verify.sh — mandatory gate before merging ANY branch to `main`,
# regardless of which tool (Claude, Gemini, Codex, human) produced it.
#
# See AGENTS.md > "Multi-tool coordination protocol" for the workflow this
# script is part of. This exists because a real regression (public numeric
# constants silently changed) was merged to main without anyone running a
# checklist like this — see the 2026-07-02 incident in docs/roadmap.md.
#
# Usage:
#   ./scripts/verify.sh                 # compare against the latest verified-* tag
#   ./scripts/verify.sh <git-ref>        # compare against a specific ref
#
# Exit code 0 means every check passed. Non-zero means at least one failed —
# do NOT merge to main until this script exits 0.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

BASELINE="${1:-}"
if [ -z "$BASELINE" ]; then
  BASELINE=$(git tag -l 'verified-*' --sort=-creatordate | head -1)
  if [ -z "$BASELINE" ]; then
    BASELINE=$(git rev-list --max-parents=0 HEAD)
    echo "No verified-* tag found; using initial commit $BASELINE as baseline."
  fi
fi
echo "Baseline for comparison: $BASELINE"
echo "Current HEAD:            $(git rev-parse --short HEAD)"
echo

OVERALL_FAIL=0

# ---------------------------------------------------------------------------
echo "== 1. Full project build =="
if lake build RiemannHypothesis; then
  echo "PASS: lake build succeeded"
else
  echo "FAIL: lake build failed — do not proceed"
  OVERALL_FAIL=1
fi
echo

# ---------------------------------------------------------------------------
echo "== 2. Changed pre-existing 'def' values =="
echo "(A 'def' line disappearing or having its RHS changed relative to the"
echo " baseline means a public constant's value moved — this is how the"
echo " 2026-07-02 regression happened. Only expected if you deliberately"
echo " changed a definition's semantics, not just its proof.)"
SCRATCH_DIR_2=$(mktemp -d /tmp/verify_defs_XXXX)
git grep -h -E '^(noncomputable )?def [A-Za-z0-9_'"'"']+.*:.*:=' "$BASELINE" -- 'RiemannHypothesis/*.lean' 2>/dev/null | sort > "$SCRATCH_DIR_2/baseline_defs.txt" || true
git grep -h -E '^(noncomputable )?def [A-Za-z0-9_'"'"']+.*:.*:=' -- 'RiemannHypothesis/*.lean' 2>/dev/null | sort > "$SCRATCH_DIR_2/current_defs.txt" || true
CHANGED_DEFS=$(comm -23 "$SCRATCH_DIR_2/baseline_defs.txt" "$SCRATCH_DIR_2/current_defs.txt")
if [ -z "$CHANGED_DEFS" ]; then
  echo "PASS: no pre-existing def line removed or modified"
else
  COUNT=$(echo "$CHANGED_DEFS" | wc -l | tr -d ' ')
  echo "FLAG: $COUNT def(s) removed/changed — verify each is intentional:"
  echo "$CHANGED_DEFS"
  OVERALL_FAIL=1
fi
rm -rf "$SCRATCH_DIR_2"
echo

# ---------------------------------------------------------------------------
echo "== 3. Repo-wide counts (report only — compare against what you expect for this change) =="
AXIOMS=$(grep -R "^axiom " RiemannHypothesis --include="*.lean" | wc -l | tr -d ' ')
SORRIES=$(grep -RE '^\s*sorry\s*$' RiemannHypothesis --include="*.lean" | wc -l | tr -d ' ')
NATIVE_DECIDE=$(grep -R "native_decide" RiemannHypothesis --include="*.lean" | wc -l | tr -d ' ')
COT_AXIOMS=$(grep -R "axiom cot_pi_.*_bounds" RiemannHypothesis/Certificates/Generated --include="*.lean" 2>/dev/null | wc -l | tr -d ' ')
COT_THEOREMS=$(grep -R "theorem cot_pi_.*_bounds" RiemannHypothesis/Certificates/Generated --include="*.lean" 2>/dev/null | wc -l | tr -d ' ')
echo "Total 'axiom' declarations:        $AXIOMS"
echo "Total 'sorry' occurrences:         $SORRIES"
echo "Total 'native_decide' occurrences: $NATIVE_DECIDE"
echo "cot_pi_*_bounds remaining axioms:  $COT_AXIOMS"
echo "cot_pi_*_bounds theorems:          $COT_THEOREMS"
echo
echo "Baseline counts for comparison:"
git show "$BASELINE:RiemannHypothesis" >/dev/null 2>&1 || true
BASELINE_SORRIES=$(git grep -cE '^[[:space:]]*sorry[[:space:]]*$' "$BASELINE" -- 'RiemannHypothesis/*.lean' 2>/dev/null | awk -F: '{s+=$3} END{print s+0}')
BASELINE_NATIVE=$(git grep -c "native_decide" "$BASELINE" -- 'RiemannHypothesis/*.lean' 2>/dev/null | awk -F: '{s+=$3} END{print s+0}')
echo "  sorry at baseline:         $BASELINE_SORRIES"
echo "  native_decide at baseline: $BASELINE_NATIVE"
if [ "$SORRIES" -gt "$BASELINE_SORRIES" ]; then
  echo "FLAG: sorry count increased ($BASELINE_SORRIES -> $SORRIES) — every new one must be individually documented, not silent"
fi
if [ "$NATIVE_DECIDE" -gt "$BASELINE_NATIVE" ]; then
  echo "FAIL: native_decide count increased ($BASELINE_NATIVE -> $NATIVE_DECIDE) — forbidden by AGENTS.md"
  OVERALL_FAIL=1
fi
echo

# ---------------------------------------------------------------------------
# NOTE: this project generates hundreds of near-identical theorems per phase
# (e.g. one cot_pi_A_K_bounds per pair). Checking every single new one via
# `lake env lean` is too slow for a routine gate (10+ minutes for 150+
# theorems, since each #print axioms forces a full proof-term traversal).
# Default to a bounded, spread-out sample (first/middle/last) unless
# VERIFY_SAMPLE=all is set. A sample of this size has caught every real
# problem seen on this project so far, but it is NOT a substitute for the
# full build in step 1 — step 1 already re-elaborates everything.
SAMPLE_SIZE="${VERIFY_SAMPLE_SIZE:-10}"
echo "== 4. #print axioms on a sample of new theorems since baseline (sample size: $SAMPLE_SIZE, set VERIFY_SAMPLE_SIZE=all for exhaustive) =="
echo "(This step can take several minutes on this project's large generated files — that's"
echo " expected. It will be far slower, or appear to hang, if another lake/lean build is"
echo " running concurrently anywhere on this machine — see 'one tool at a time' in AGENTS.md.)"
SCRATCH_DIR=$(mktemp -d /tmp/verify_axioms_XXXX)
SCRATCH="$SCRATCH_DIR/check.lean"
ALL_ENTRIES="$SCRATCH_DIR/all_entries.txt"   # tab-separated: module<TAB>namespace<TAB>name
: > "$ALL_ENTRIES"
AWK_SORRY_SCRIPT='
/^theorem / || /^lemma / {
    if (in_thm && has_sorry) print name;
    in_thm = 1;
    name = $2;
    has_sorry = 0;
}
in_thm && /sorry/ { has_sorry = 1 }
/^$/ || /^def / || /^noncomputable def / || /^abbrev / || /^instance / {
    if (in_thm && has_sorry) print name;
    in_thm = 0;
}
END { if (in_thm && has_sorry) print name }
'
while IFS= read -r f; do
  [ -f "$f" ] || continue
  case "$f" in *.lean) ;; *) continue ;; esac
  MODULE=$(echo "$f" | sed -E 's#/#.#g; s#\.lean$##')
  NS=$(grep -m1 '^namespace ' "$f" | awk '{print $2}')
  git diff "$BASELINE" -- "$f" | grep -E '^\+(theorem|lemma) ' | sed -E "s/^\+(theorem|lemma) ([A-Za-z0-9_']+).*/\2/" |
    while IFS= read -r name; do
      [ -n "$name" ] && printf '%s\t%s\t%s\n' "$MODULE" "$NS" "$name" >> "$ALL_ENTRIES"
    done
  git show "$BASELINE:$f" 2>/dev/null | awk "$AWK_SORRY_SCRIPT" | sort > "$SCRATCH_DIR/baseline_sorries.txt" || true
  awk "$AWK_SORRY_SCRIPT" "$f" | sort > "$SCRATCH_DIR/current_sorries.txt"
  comm -23 "$SCRATCH_DIR/baseline_sorries.txt" "$SCRATCH_DIR/current_sorries.txt" |
    while IFS= read -r name; do
      [ -n "$name" ] && printf '%s\t%s\t%s\n' "$MODULE" "$NS" "$name" >> "$ALL_ENTRIES"
    done
done < <(git diff --name-only "$BASELINE" -- 'RiemannHypothesis/*.lean')

TOTAL_NEW=$(wc -l < "$ALL_ENTRIES" | tr -d ' ')
if [ "$TOTAL_NEW" -gt 0 ] && [ "$SAMPLE_SIZE" != "all" ] && [ "$TOTAL_NEW" -gt "$SAMPLE_SIZE" ]; then
  # Deterministic spread across the full list (first/middle/last), not just the first N.
  STEP=$((TOTAL_NEW / SAMPLE_SIZE))
  [ "$STEP" -lt 1 ] && STEP=1
  SELECTED="$SCRATCH_DIR/selected.txt"
  awk -v step="$STEP" '(NR-1) % step == 0' "$ALL_ENTRIES" > "$SELECTED"
  echo "Sampling $(wc -l < "$SELECTED" | tr -d ' ') of $TOTAL_NEW new theorems (every ${STEP}th)."
else
  SELECTED="$ALL_ENTRIES"
fi

NEW_THEOREM_COUNT=$(wc -l < "$SELECTED" | tr -d ' ')
cut -f1 "$SELECTED" | sort -u | sed 's/^/import /' > "$SCRATCH"
cut -f2 "$SELECTED" | grep -v '^$' | sort -u | sed 's/^/open /' >> "$SCRATCH"
cut -f3 "$SELECTED" | sed 's/^/#print axioms /' >> "$SCRATCH"

ALLOWLIST="scripts/verify_known_sorries.txt"
if [ "$NEW_THEOREM_COUNT" -eq 0 ]; then
  echo "No new 'theorem' declarations found relative to baseline (nothing to check, or only defs/axioms changed)."
else
  echo "Checking $NEW_THEOREM_COUNT new theorem(s)..."
  AXIOM_OUTPUT=$(lake env lean "$SCRATCH" 2>&1)
  echo "$AXIOM_OUTPUT"
  if echo "$AXIOM_OUTPUT" | grep -qi "^error\|invalid 'import'\|unknown"; then
    echo "FAIL: the axiom-check script itself failed to compile — inspect $SCRATCH manually"
    echo "(this can happen if a theorem needs a namespace/import this script didn't guess correctly)"
    OVERALL_FAIL=1
  elif echo "$AXIOM_OUTPUT" | grep -q "sorryAx"; then
    # A theorem depending on sorryAx is only acceptable if it's individually named in
    # scripts/verify_known_sorries.txt (one qualified or bare name per line, '#' comments ok) —
    # i.e. someone has already looked at it and decided it's expected, documented open work,
    # not a surprise. Anything else fails.
    UNEXPECTED=""
    CURRENT_NAME=""
    while IFS= read -r line; do
      if echo "$line" | grep -qE "^'.*' depends on axioms:"; then
        CURRENT_NAME=$(echo "$line" | sed -E "s/^'([^']+)'.*/\1/")
      fi
      if echo "$line" | grep -q "sorryAx" && [ -n "$CURRENT_NAME" ]; then
        SHORT_NAME="${CURRENT_NAME##*.}"
        if [ -f "$ALLOWLIST" ] && (grep -qxF "$CURRENT_NAME" "$ALLOWLIST" || grep -qxF "$SHORT_NAME" "$ALLOWLIST"); then
          echo "  (sorryAx in $CURRENT_NAME — allowlisted in $ALLOWLIST, OK)"
        else
          UNEXPECTED="$UNEXPECTED $CURRENT_NAME"
        fi
        CURRENT_NAME=""
      fi
    done <<< "$AXIOM_OUTPUT"
    if [ -n "$UNEXPECTED" ]; then
      echo "FAIL: theorem(s) depend on sorryAx and are NOT in $ALLOWLIST:$UNEXPECTED"
      echo "      If this is expected/documented open work, add the name to $ALLOWLIST."
      echo "      If it's a surprise, that's exactly what this check exists to catch."
      OVERALL_FAIL=1
    else
      echo "PASS: all sorryAx dependencies found are allowlisted in $ALLOWLIST."
    fi
  else
    echo "PASS: no sorryAx detected. Review the axiom lists above by eye — anything beyond"
    echo "      [propext, Classical.choice, Quot.sound] plus already-known project axioms"
    echo "      should be a deliberate, expected dependency, not a surprise."
  fi
fi
echo

# ---------------------------------------------------------------------------
echo "======================================"
if [ "$OVERALL_FAIL" -eq 0 ]; then
  echo "ALL CHECKS PASSED — safe to merge to main."
  echo "After merging, consider: git tag verified-<short-description> <commit>"
else
  echo "AT LEAST ONE CHECK FAILED OR FLAGGED — do not merge until resolved."
fi
echo "======================================"
exit "$OVERALL_FAIL"
