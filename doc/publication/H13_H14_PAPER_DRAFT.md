# Formalizing a Vasyunin–BBLS Autocorrelation Reduction and Unconditional Mertens Decay in Lean 4

**Manuscript draft — 15 July 2026**  
**Authors:** to be supplied before circulation  
**Artifact status:** branch-specific, audited; not a claim about the current default build

## Abstract

We report two components of a Lean 4 formalization motivated by the Nyman–Beurling–Báez-Duarte approach to the Riemann hypothesis. The first component (H13) formalizes the rational Báez-Duarte–Balazard–Landreau–Saias (BBLS) autocorrelation and period-reduction chain leading to Vasyunin's finite cotangent expression. The rational BBLS theorems and the period-reduction theorem have no project-specific axioms in their audited dependency graphs. The final identification of the original Gram integral with the explicit Vasyunin entry, however, still depends on one explicitly declared project axiom: a bounded inversion change-of-variables formula. Thus H13 is a substantial formalization of the rational reduction, but its headline Gram-entry identity is not yet an axiom-free theorem.

The second component (H14) formalizes unconditional linear Möbius cancellation. It proves both the qualitative bound \(M(x)=o(x)\) and an effective estimate

\[
  |M(N)| \le A N\exp\!\bigl(-a\sqrt{\log N}\bigr)
  \qquad (N\ge 3)
\]

for some positive real constants \(A,a\). Its architecture includes a de la Vallée Poussin zero-free input, logarithmic-derivative control, a truncated Perron kernel, contour estimates, and parameter optimization. On the audited H14 branch, the named completion theorems depend only on Lean's standard logical foundations (`propext`, `Classical.choice`, and `Quot.sound`). These results do not prove the Riemann hypothesis, the Nyman–Beurling criterion, or a square-root Mertens bound. We give exact theorem scope, dependency accounting, reproducibility data, and the discrepancies between the historical proof branches and the current default package.

## 1. Scope and contribution

The formal development separates two classical analytic tasks that arise upstream of a proposed quantitative Nyman–Beurling argument:

1. **H13, the local Vasyunin/BBLS bridge.** Evaluate the fractional-part Gram kernel at positive integer indices through a rational autocorrelation identity and a finite cotangent formula.
2. **H14, linear Möbius cancellation.** Establish an unconditional prime-number-theorem-strength estimate for the summatory Möbius function.

The contribution is one of formalization and dependency isolation. No new proof of the Riemann hypothesis is claimed. In particular, the H13 and H14 statements do not supply the separate quadratic-cancellation estimate currently called H15, and they do not close the classical Nyman–Beurling equivalence inside the active package.

This draft treats a Lean declaration as **project-axiom-free** when `#print axioms` reports only the standard foundational constants

```text
propext, Classical.choice, Quot.sound
```

and no declaration introduced by this project. This convention does not mean constructive or choice-free.

## 2. Mathematical statements

### 2.1. The H13 fractional-part kernel

For positive integers \(h,k\), the formalized Gram entry is

\[
  b_{h,k}
  = \int_0^\infty
      \left\{\frac{1}{hx}\right\}
      \left\{\frac{1}{kx}\right\}\,dx.
\]

In Lean this is `baezDuarteGramEntry h k`. The target explicit entry is

\[
\begin{aligned}
  B(h,k)={}&\frac{\log(2\pi)-\gamma}{2}
               \left(\frac1h+\frac1k\right)
       + \frac{k-h}{2hk}\log\frac hk \\
     &-\frac{\pi}{2hk}\bigl(V(h,k)+V(k,h)\bigr),
\end{aligned}
\]

where `cotangentSumVFormula` supplies the finite Vasyunin cotangent sum \(V\). The positivity hypotheses are essential: a formerly hypothesis-free formulation is false at a zero index.

The formal chain establishes, among other results:

- `baezDuarte_prop22_rat`: the rational, coprime specialization of BBLS Proposition 22;
- `bbls_A_one`: \(A(1)=\log(2\pi)-\gamma\) for the BBLS autocorrelation integral;
- `bbls_A_rat`: the closed form of \(A(k/h)\) for arbitrary positive integer \(h,k\), reducing internally by their gcd;
- `bbls_period_unfolding`: the decomposition into periods of length \(\operatorname{lcm}(h,k)\);
- `bbls_tsum_eq_vasyuninBEntry`: the periodized shifted-integral series equals the explicit Vasyunin entry;
- `shiftedIntegralTsum_period_reduction` and `tsum_shifted_integrals_eq_cotangent_sum`: the downstream period-reduction and cotangent-recognition statements.

Fresh axiom inspection reports only the standard foundational constants for the listed rational results. The final declaration

```lean
theorem vasyuninBEntry_correct_axiom
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k = vasyuninBEntry h k
```

is a theorem syntactically, despite its historical name. Its audited dependency graph contains one additional project declaration:

```text
setIntegral_Ioo_inv_substitution_bridge
```

This axiom asserts the expected inversion substitution on a bounded interval, under measurability and integrability assumptions. It is used to pass from the original \(x\)-integral to the transformed integral on which the axiom-free BBLS period reduction operates. Discharging this single change-of-variables declaration is therefore the precise remaining task required to advertise the H13 Gram-entry identity itself as project-axiom-free.

The file also retains a `sorry` in the general-real version `baezDuarte_prop21`. The rational specialization required by `baezDuarte_prop22_rat` is separately proved, and the audited rational theorem graph does not depend on the general-real declaration.

### 2.2. The H14 Mertens statements

Write

\[
  M(x)=\sum_{n\le x}\mu(n)
\]

with the exact endpoint convention encoded by `mertensAt`; `mertensReal` is the natural-number version. The principal qualitative theorems are:

```lean
theorem mertensAt_isLittleO :
  mertensAt =o[atTop] (fun x : ℝ ↦ x)

theorem mertensReal_isLittleO :
  mertensReal =o[atTop] (fun N : ℕ ↦ (N : ℝ))

theorem mertensAt_div_tendsto_zero :
  Tendsto (fun x : ℝ ↦ mertensAt x / x) atTop (nhds 0)

theorem mobiusOverSelf_isLittleO_one :
  (fun x : ℝ ↦ ∑ n ∈ Finset.range ⌊x⌋₊,
      (ArithmeticFunction.moebius n : ℝ) / n)
    =o[atTop] (fun _ ↦ (1 : ℝ))
```

The effective endpoint is:

```lean
theorem mertens_effective_unconditional :
  ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
    ∀ N : ℕ, 3 ≤ N →
      |mertensReal N| ≤
        A * N * Real.exp (-a * Real.sqrt (Real.log N))
```

The qualitative and effective paths coexist. `H14LinearMobiusCompletion.lean` connects the local definitions to the pinned `PrimeNumberTheoremAnd` development, including its zero-free and logarithmic-derivative estimates and `M_isLittleO`. The local effective route packages the needed analytic input explicitly and derives the exponential decay through Perron inversion and optimization.

## 3. Formal architecture

### 3.1. H13 modules

The H13 source of record is historical commit `6eda2ff7f35f561d153deeac56bece3da35809a3`, tagged `verified-h13-complete`. Its relevant modules are:

| Module | Role |
|---|---|
| `VasyuninGram.lean` | Defines the original Gram integral and proves elementary properties. |
| `VasyuninExplicitFormula.lean` | Defines the finite cotangent expression and its symmetry. |
| `VasyuninPeriodReduction.lean` | Formalizes the rational BBLS propositions and finite-sum identities. |
| `BBLSPhiOne.lean` | Supplies the BBLS auxiliary function identities. |
| `BBLSAutocorrelation.lean` | Evaluates \(A(1)\), evaluates \(A(k/h)\), and unfolds the period series. |
| `VasyuninCotangentRecognition.lean` | Develops the analytic cotangent-series recognition tools. |
| `VasyuninBridge.lean` | Connects the original Gram integral to the transformed periodized expression. |

One important correction is built into this architecture. The intervals \([1/(m+1),1/m]\) tile \((0,1]\), not \((0,\infty)\). The development therefore rejects the false identity equating their sum directly with the full Gram integral, proves a decomposition with the missing \((1,\infty)\) tail, and only then performs the corrected reduction.

### 3.2. H14 modules

The audited H14 source of record is branch `codex/h14-corrected-aristotle-specs` at commit `b499bf27777845504c3b4b72c8172a11b6253179`:

| Module | Role |
|---|---|
| `H14DVPFoundation.lean` | de la Vallée Poussin analytic foundation and supporting zeta estimates. |
| `H14BorelJensenCompletion.lean` | Completes the zero-free/logarithmic-derivative input used downstream. |
| `H14PerronKernel.lean` | Bounds the truncated Perron kernel. |
| `H14PerronMertens.lean` | Relates Perron integrals to the Mertens sum. |
| `H14PerronUnconditionalV2.lean` | Packages contour shift and unconditional Mertens estimates. |
| `H14EffectiveMertens.lean` | Optimizes the parameters and states the effective bound. |
| `H14LinearMobiusCompletion.lean` | Exposes the qualitative \(o(x)\), ratio, and weighted boundary API. |
| `H14LinearMobiusCompletionAudit.lean` | Prints axiom dependencies for the qualitative API. |
| `H14EffectiveMertensAudit.lean` | Prints axiom dependencies for the effective API. |

The pinned external dependency is `PrimeNumberTheoremAnd` at commit `80c12dfd932e99874e004d65537c57ef6421ff2b`; the Lean toolchain is `leanprover/lean4:v4.30.0`.

## 4. Dependency and axiom accounting

The following table records theorem-level dependency audits, rather than merely counting `axiom` or `sorry` tokens in the repository.

| Result group | Project-specific axioms in audited graph | Status |
|---|---:|---|
| H13 `baezDuarte_prop22_rat` | 0 | Proved for the rational/coprime specialization. |
| H13 `bbls_A_one` | 0 | Proved. |
| H13 `bbls_A_rat` | 0 | Proved for arbitrary positive integer indices. |
| H13 period unfolding and cotangent reduction | 0 | Proved in the audited rational chain. |
| H13 `vasyuninBEntry_correct_axiom` | 1 | Depends on `setIntegral_Ioo_inv_substitution_bridge`. |
| H14 qualitative Mertens completion API | 0 | All audited declarations report standard Lean foundations only. |
| H14 effective Mertens API | 0 | All audited declarations report standard Lean foundations only. |
| H14 RH–square-root-Mertens equivalence file | 2 explicit `Prop` hypotheses | Conditional theorem, not an unconditional completion result. |

The H14 build emits warnings for unrelated declarations containing `sorry` in the broad imported dependency tree, including parts of the external `PrimeNumberTheoremAnd` package and the local exploratory H15 file. The dedicated H14 audit files show that those declarations are not dependencies of the named H14 endpoints. Conversely, the large historical H13 tree contains many declarations outside H13; repository-wide counts are not evidence for or against the specific H13 theorem graphs.

## 5. Verification record

This record reports checks performed on 15 July 2026 and intentionally distinguishes a fresh check from a historical tag.

| Artifact | Fresh result | Interpretation |
|---|---|---|
| H14 commit `b499bf2` | `bash mathlib/verify.sh` completed successfully after 8,521 build jobs; both H14 audit files ran. | Full branch verification passed. Each named H14 completion theorem printed only `propext`, `Classical.choice`, and `Quot.sound`. |
| H13 commit `6eda2ff` | Relevant H13 modules built successfully; a targeted `#print axioms` audit ran successfully. | Rational BBLS results are project-axiom-free; final Gram bridge has the one substitution axiom described above. |
| H13 full historical verifier | Began successfully but was interrupted while compiling the much larger generated certificate corpus. | The tag `verified-h13-complete` records an earlier historical verification, but this audit does not present it as a fresh end-to-end pass. |
| Current default branch `b65f11c` | Default package builds, with an H15 `sorry` warning. `mathlib/verify.sh` fails because `NBMellinTools/Audit.lean` is absent. | The current default branch is not a reproducible source of the H13/H14 completion claims. It archives most of that library and imports exploratory H15 material. |

These facts imply two release tasks before submission: (i) discharge or explicitly retain and document the H13 inversion-substitution axiom, and (ii) assemble a clean artifact branch that imports H13 and H14 without H15 and has one passing top-level verification command.

## 6. Limitations and explicit nonclaims

1. **No proof of the Riemann hypothesis.** Neither H13 nor H14 establishes RH.
2. **No unconditional square-root Mertens bound.** The effective H14 result is the classical zero-free-region bound \(N\exp(-a\sqrt{\log N})\), not \(O(N^{1/2+\varepsilon})\). The latter would have RH-level consequences.
3. **Conditional RH-equivalence wrapper.** `H14MertensRHEquivalenceV2.lean` proves

   ```lean
   RiemannHypothesis ↔ MertensSqrtBound
   ```

   only after receiving `PerronMertensGap` and `MobiusContinuationGap` as explicit hypotheses. It is not an unconditional equivalence closure.
4. **One H13 project axiom remains on the headline path.** The rational BBLS chain is clean, but the original Gram-integral identification requires `setIntegral_Ioo_inv_substitution_bridge`.
5. **The general-real BBLS Proposition 21 is not complete.** A `sorry` remains there; the completed rational specialization is the theorem used by the audited H13 path.
6. **H15 is out of scope.** No quadratic Möbius–Vasyunin cancellation theorem is claimed here.
7. **Active-main packaging is presently inconsistent with publication.** Passing checks must be reproduced from the source commits named above until a clean release branch is assembled.

## 7. Reproducibility

### 7.1. H14

From the repository root, create a detached worktree at the audited commit and run its verifier:

```bash
git worktree add --detach ../riemann-h14-artifact \
  b499bf27777845504c3b4b72c8172a11b6253179
cd ../riemann-h14-artifact
bash mathlib/verify.sh
```

The expected final audit output lists the qualitative and effective H14 declarations with only the three standard Lean foundational constants.

### 7.2. H13

Create a detached worktree at the historical tagged commit:

```bash
git worktree add --detach ../riemann-h13-artifact \
  6eda2ff7f35f561d153deeac56bece3da35809a3
cd ../riemann-h13-artifact
```

Build the relevant modules and inspect the key dependencies:

```bash
lake build \
  RiemannHypothesis.Criteria.NymanBeurling.VasyuninPeriodReduction \
  RiemannHypothesis.Criteria.NymanBeurling.BBLSPhiOne \
  RiemannHypothesis.Criteria.NymanBeurling.BBLSAutocorrelation \
  RiemannHypothesis.Criteria.NymanBeurling.VasyuninCotangentRecognition \
  RiemannHypothesis.Criteria.NymanBeurling.VasyuninBridge
```

An audit file importing `VasyuninBridge` and `BBLSAutocorrelation` should contain at least:

```lean
#print axioms baezDuarte_prop22_rat
#print axioms bbls_A_one
#print axioms bbls_A_rat
#print axioms bbls_tsum_eq_vasyuninBEntry
#print axioms shiftedIntegralTsum_period_reduction
#print axioms tsum_shifted_integrals_eq_cotangent_sum
#print axioms vasyuninBEntry_correct_axiom
```

The first six audited endpoints are expected to show only standard foundations; the last additionally shows `setIntegral_Ioo_inv_substitution_bridge`. Exact namespaces may be required when running this outside the original audit file.

For a publication artifact, these commands should be converted into a checked-in, non-stale audit module and a single verifier that fails on unexpected axioms, `sorry`, or `native_decide` in the declared scope.

## 8. Publication plan

The mathematical exposition can be divided into two papers or one two-part artifact paper. A defensible first release should:

1. state the H13 rational BBLS formalization as the main H13 result;
2. either prove the standard inversion substitution in Lean or label it prominently as the sole remaining H13 project axiom;
3. present H14 as an unconditional formalization of classical Mertens decay, with the effective theorem as the principal endpoint;
4. include generated `#print axioms` output for every advertised endpoint;
5. exclude H15 and conditional RH wrappers from the release library's default import;
6. pin Lean, Mathlib, and `PrimeNumberTheoremAnd` revisions in an artifact manifest; and
7. archive a fresh full build log and machine-readable theorem inventory.

The strongest accurate headline at the current audited state is:

> A project-axiom-free Lean formalization of the rational BBLS/Vasyunin period-reduction chain, with one explicit classical substitution axiom at the original Gram bridge, together with a project-axiom-free formalization of unconditional qualitative and effective Mertens decay.

## References

1. L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*, Atti Accad. Naz. Lincei Rend. Lincei Mat. Appl. **14** (2003), 5–11.
2. L. Báez-Duarte, M. Balazard, B. Landreau, and E. Saias, *Étude de l'autocorrélation multiplicative de la fonction « partie fractionnaire »*, Ramanujan J. **9** (2005), 215–240; arXiv:math/0306251.
3. V. I. Vasyunin, *On a biorthogonal system associated with the Riemann hypothesis*, Algebra i Analiz **7** (1995); English translation, St. Petersburg Math. J. **7** (1996), 405–419.
4. H. Davenport, *Multiplicative Number Theory*, 3rd ed., revised by H. L. Montgomery, Graduate Texts in Mathematics 74, Springer, 2000.
5. G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Graduate Studies in Mathematics 163, American Mathematical Society, 2015.
6. The Mathlib Community, *The Lean Mathematical Library*, Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs, 2020, 367–381.
7. L. de Moura and S. Ullrich, *The Lean 4 theorem prover and programming language*, Automated Deduction—CADE 28, Lecture Notes in Computer Science 12699, 2021, 625–635.
8. A. Kontorovich et al., *PrimeNumberTheoremAnd*, Lean 4 formalization repository, pinned here at commit `80c12dfd932e99874e004d65537c57ef6421ff2b`.

