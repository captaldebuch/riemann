# H15 BCF LOGARITHMIC-TAPER RESEARCH PROTOCOL

## Status and guardrail

This protocol supersedes `H15_RESEARCH_PROMPT_CORRECTED.md`.

The arithmetic linear taper `1 - n/(N+1)` is retired. H15 now uses the
Bettin--Conrey--Farmer logarithmic taper. This remains a paper-level research
investigation: do not change or add Lean declarations until the analytic target
and theorem matching have survived expert review.

## Exact objects

For `N >= 2`, define

\[
w_N^{\mathrm{BCF}}(n)=1-\frac{\log n}{\log N},\qquad
c_N^{\mathrm{BCF}}(n)=-\mu(n)w_N^{\mathrm{BCF}}(n),\qquad 1\le n\le N.
\]

Define

\[
A_N^{\mathrm{BCF}}(s)=
\sum_{n\le N}\mu(n)w_N^{\mathrm{BCF}}(n)n^{-s}.
\]

The Gram/Vasyunin kernel is independent of the coefficient taper and therefore
does **not** change:

\[
K(h,k)=\frac{k-h}{2hk}\log\frac hk
-\frac{\pi}{2hk}\bigl(V(h,k)+V(k,h)\bigr),
\]

where the actual finite Vasyunin sum is

\[
V(p,q)=\sum_{a=1}^{q-1}
\left\{\frac{ap}{q}\right\}\cot\frac{\pi a}{q}.
\]

The earlier Bernoulli integral presented as the definition of `V` is divergent
at zero and must not be reused.

Set

\[
Q_N^{\mathrm{BCF}}=
\sum_{h,k\le N}c_N^{\mathrm{BCF}}(h)c_N^{\mathrm{BCF}}(k)K(h,k).
\]

The exact energy is

\[
E_N^{\mathrm{BCF}}
=\left\|\chi-\sum_{n\le N}c_N^{\mathrm{BCF}}(n)\rho_n\right\|_2^2
=\frac1{2\pi}\int_{\mathbb R}
\frac{|1-\zeta(\tfrac12+it)A_N^{\mathrm{BCF}}(\tfrac12+it)|^2}
{\tfrac14+t^2}\,dt.
\]

## Authoritative H15 target

The new target is the total-energy statement

\[
\boxed{E_N^{\mathrm{BCF}}\le \frac{C}{\log N}\quad(N\ge N_0).}
\]

Do not replace this by a sum of separate absolute bounds for the smooth,
log-ratio, cotangent, and linear pieces. Bettin--Conrey--Farmer control the
total centered energy. Separate absolute values can destroy the cancellation
and impose a strictly stronger, possibly false target.

An unconditional proof of this target would prove RH. The published BCF result
is a conditional benchmark, not an unconditional input: it assumes RH and

\[
\sum_{|\Im\rho|\le T}\frac1{|\zeta'(\rho)|^2}
\ll T^{3/2-\delta}
\]

for some `delta > 0`, and obtains

\[
E_N^{\mathrm{BCF}}\sim
\frac{2+\gamma-\log(4\pi)}{\log N}.
\]

Primary source: https://arxiv.org/abs/1211.5191

## Why the BCF taper passes the validation gate

Mellin inversion gives

\[
A_N^{\mathrm{BCF}}(s)=
\frac1{\log N}\frac1{2\pi i}
\int_{(c)}\frac{N^w}{\zeta(s+w)w^2}\,dw.
\]

For a simple nontrivial zero `rho`, the residue is

\[
\frac1{\log N}\frac{N^{\rho-s}}
{\zeta'(\rho)(\rho-s)^2}.
\]

The global `1/log N` factor and double-pole kernel are precisely the damping
missing from the retired arithmetic linear taper.

## New empirical anchors

The following values use the unchanged exact Gram kernel with the BCF
coefficient vector. They are diagnostics, not proof.

| N | Q_N^(BCF) | E_N^(BCF) | E_N^(BCF) log N | coprime part | non-coprime part |
|---:|---:|---:|---:|---:|---:|
| 100 | 0.81320955 | 0.17847527 | 0.82190900 | -0.10051287 | 0.91372242 |
| 300 | 0.87079603 | 0.11687045 | 0.66660363 | -0.42016551 | 1.29096154 |
| 1000 | 0.88080300 | 0.08128997 | 0.56153123 | -0.58347382 | 1.46427682 |
| 2000 | 0.91164739 | 0.06742115 | 0.51246157 | -0.49944354 | 1.41109093 |

The energy now decreases at the tested scales, unlike the linear-taper
plateau. The values are still far from the BCF asymptotic constant, so no
finite-range rate should be inferred.

## Exact phase conversion retained from the previous investigation

For `(p,q)=1`, let `p_bar` denote the inverse of `p` modulo `q`. The finite
cotangent transform gives

\[
\sum_{a=1}^{q-1}\cot\frac{\pi a}{q}\,e(an/q)=i(q-2n)
\]

and hence

\[
V(p,q)=\frac{i}{q^2}\sum_{r,n=1}^{q-1}
r(q-2n)e(-nr\bar p/q).
\]

Thus the nonzero-frequency part of `K(p,q)` has genuine modular-inverse phases
`e(-nr p_bar/q)`. The conversion is exact and has zero remainder. Also,

\[
V(gp,gq)=gV(p,q),\qquad K(gp,gq)=\frac1gK(p,q),
\]

so every gcd stratum can be retained exactly. Since `K` is symmetric, never
write `K(p,q)+K(q,p)` as though it were a new object; it is `2K(p,q)`.

Primary cotangent source: https://arxiv.org/abs/1111.0931

## Current DFI/Bettin--Chandee blocker

The phase has the correct Kloosterman shape, but existing theorems do not yet
give the required aggregate bound.

On a block `p,q,r,n ~ Q`, the transformed numerator has length `A ~ Q^2` and
is constrained by `a = nr`. Grouping by `a` produces coefficients coupled to
the modulus cutoff, rather than a clean product `alpha_p beta_q nu_a`. Even in
an optimistic dyadic separation, substituting `A ~ Q^2` and `M ~ N ~ Q` into
the Bettin--Chandee bound leaves a majorant of size

\[
Q^{15/8+\varepsilon},
\]

not `O(1/log N)`. The logarithmic zero-frequency component must also remain
paired with the oscillatory terms; DFI does not control that cancellation.

Primary theorem: https://arxiv.org/abs/1502.00769

The 2026 Dong--Robles--Zeindler improvement still treats fixed-numerator,
separable bilinear forms and does not remove this coupling:
https://arxiv.org/abs/2601.00292

## Sequential research phases

### Phase 1: BCF validation -- complete

1. Exact Mellin--Plancherel identity established on paper.
2. BCF logarithmic taper confirmed to have the required zero-residue damping.
3. Conditional BCF theorem supplies the correct `1/log N` benchmark.
4. Exact Gram diagnostics show decreasing energy at the tested scales.

### Phase 2: Re-express the total centered energy -- complete

Derive one exact expression for `E_N^(BCF)` in which the smooth, logarithmic,
and cotangent pieces remain combined. Insert the exact modular-inverse Fourier
formula only after this centering. Do not estimate `Q_N`, the smooth product,
or the logarithmic mode separately.

Required deliverable:

\[
E_N^{\mathrm{BCF}}=
\text{one centered modular-inverse sum} + \text{explicit controlled tails}.
\]

All endpoint conventions, gcd strata, and coefficient norms are explicit in
`H15_BCF_CENTERED_ENERGY_DERIVATION.md`.  The resulting algebraic tail is
exactly zero.  The first analytic gap is the modulus-dependent joint amplitude
`beta_q(b)`, which must remain centered with the log-ratio and scalar terms.

### Phase 3: Theorem matching

For every dyadic block:

1. identify the exact DFI/Bettin--Chandee variables;
2. calculate all `L^2` coefficient norms;
3. include the numerator length `A`, gcd factor `g`, and boundary coupling;
4. retain cross-block cancellation where the centered identity requires it;
5. sum the resulting majorants before claiming a logarithmic bound.

If the total is larger than `C/log N`, stop. Do not hide a positive power of
`N` in an unspecified constant or epsilon.

### Phase 4: Expert escalation if Phase 3 remains blocked

Send specialists the exact BCF-weighted centered expression and ask:

> Is there a transformation or Kloosterman-fraction estimate that controls the
> total BCF-centered Vasyunin energy without separating its logarithmic mode,
> when the inverse phase is `e(-nr p_bar/q)`, the numerator is the coupled
> product `nr`, and all gcd strata carry the exact factor `1/g`? Existing
> Bettin--Chandee norms leave `Q^(15/8+epsilon)` on a balanced block; can the
> BCF logarithmic coefficients or the symmetric centering supply the missing
> cancellation?

## Success criteria before any Lean work

1. A complete paper proof of the centered BCF aggregate identity.
2. Exact theorem matching, including all ranges and coefficient norms.
3. A summed bound of `C/log N` with no unproved cancellation assertion.
4. Independent expert review of the new analytic step.
5. Only then design a new Lean API; do not retrofit the retired linear-taper
   declarations silently.
