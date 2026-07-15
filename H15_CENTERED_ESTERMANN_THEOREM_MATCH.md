# H15 centered Estermann theorem match

**Date:** 15 July 2026

**Status:** paper-level research only; no H15 Lean formalization

**Verdict:** the primitive Estermann insertion is exact, but the cited
cotangent reciprocity does not produce the BCF main term.  The main term in
the published BCF theorem comes from residues at zeros of the Riemann zeta
function, under RH and a reciprocal zeta-derivative moment hypothesis.

## 1. Decision reached

The next H15 step should not be an unconditional Kuznetsov or componentwise
DFI estimate.  There are two mathematically honest continuations:

1. **Conditional BCF route:** formalize the exact Mellin identity and then the
   Bettin--Conrey--Farmer theorem under its stated hypotheses (RH, simple
   zeros, and the reciprocal `zeta'` moment bound).
2. **RH-equivalence route:** keep the unconditional `O(1 / log N)` estimate as
   an explicitly open H15 goal.  Any proof of it for the BCF approximants
   would imply RH through the Nyman--Beurling criterion.

The current sources do not justify a third route that removes those
hypotheses.

## 2. Exact Estermann insertion

Use the notation of `H15_BCF_CENTERED_ENERGY_DERIVATION.md`.  For coprime
`p,q`, the primitive phase is

\[
 \sum_{b\bmod q}\beta_q(b)e(-b\bar p_q/q)
 =-iV(p,q).
 \tag{1}
\]

With

\[
 D(0,h/q)=\frac14+\frac{i}{2}c_0(h/q),
 \qquad
 V(p,q)=-c_0(\bar p_q/q),
\]

the Fourier formula becomes

\[
 \sum_{b\bmod q}\beta_q(b)e(-b\bar p_q/q)
 =\frac12-2D(0,-\bar p_q/q).
 \tag{2}
\]

Consequently the complete modular-inverse part of the centered energy is

\[
 \boxed{
 \begin{aligned}
 \mathfrak P_{N,g}
  =\operatorname{Re}\Bigg(2\pi i
  \sum_{q=2}^{M_g}\frac{\alpha_{N,g}(q)}q
  \sum_{\substack{p\le M_g\\(p,q)=1}}
       \frac{\alpha_{N,g}(p)}p
  D(0,-\bar p_q/q)\Bigg).
 \end{aligned}}
 \tag{3}
\]

This follows by substituting (2) in equation (19) of the centered-energy
note.  The constant `1/2` in (2) contributes only a purely imaginary term
after multiplication by `-pi i`, so its real part is zero.  In particular,
the scalar centering term `C_N` and the logarithmic term
`mathfrak L_{N,g}` do **not** appear automatically from the pointwise
Estermann special value.  They would have to arise from a subsequent global
summation or contour argument.

Equation (3) is the exact requested insertion.  It introduces no remainder
and makes no analytic estimate.

## 3. Why the cotangent reciprocity does not match the BCF pair

Bettin--Conrey prove

\[
 c_0(h/k)+\frac{k}{h}c_0(k/h)-\frac1{\pi h}
 =\frac{i}{2}\psi_0(h/k).
 \tag{4}
\]

To transform `V(p,q)` one must set `h=bar p_q` and `k=q`.  The companion in
(4) is then

\[
 c_0(q/\bar p_q),
\]

whereas the symmetric BCF kernel contains

\[
 V(q,p)=-c_0(\bar q_p/p).
\]

These are not the same rational argument.  For example, `p=2,q=5` gives
`bar p_q=3`; reciprocity pairs `c_0(3/5)` with `c_0(5/3)=c_0(2/3)`, while
the BCF companion is `c_0(1/2)`.  Thus (4) does not turn
`V(p,q)+V(q,p)` into the log-ratio and scalar terms of the Gram kernel.

The period function `psi_0` in (4) is also an exact analytic remainder, not a
bound summable to `o(1 / log N)` for the Mobius logarithmic weights.  The
reciprocity formula is valuable structural information, but it is not the
missing H15 estimate.

## 4. Where the published BCF main term actually comes from

Define the BCF Dirichlet polynomial

\[
 V_N(s)=\sum_{n\le N}
 \left(1-\frac{\log n}{\log N}\right)\frac{\mu(n)}{n^s}.
 \tag{5}
\]

The exact Mellin transform of the BCF approximation error is

\[
 \mathcal M f_N(s)=\frac{1-\zeta(s)V_N(s)}s,
 \qquad 0<\Re s<1.
 \tag{6}
\]

Mellin--Plancherel therefore identifies the finite Gram energy with

\[
 E_N^{\mathrm{BCF}}
 =\frac1{2\pi}\int_{-\infty}^{\infty}
   |1-\zeta(1/2+it)V_N(1/2+it)|^2
   \frac{dt}{1/4+t^2}.
 \tag{7}
\]

BCF Lemma 2 expands the polynomial by shifting the contour in

\[
 V_N(s)=\frac1{\log N}\frac1{2\pi i}
 \int_{(2)}\frac{N^w}{\zeta(s+w)w^2}\,dw.
\]

Their exact result has the form

\[
 V_N(s)=\frac1{\zeta(s)}
 \left(1-\frac1{\log N}\frac{\zeta'}{\zeta}(s)\right)
 +\frac1{\log N}\sum_\rho R_N(\rho,s)
 +\frac1{\log N}F_s(1/N),
 \tag{8}
\]

where `R_N(rho,s)` is the residue at a nontrivial zero and `F_s` is the
explicit trivial-zero contribution.  After (8) is inserted into (7), the
surviving cross term is evaluated by shifting across the zeta zeros.  Its
residues give

\[
 \frac1{\log N}\sum_\rho\frac1{|\rho|^2}
 +O\left(\frac1{\log^2 N}\right).
 \tag{9}
\]

Under RH and simplicity,

\[
 \sum_\rho\frac1{|\rho|^2}=2+\gamma-\log(4\pi),
\]

which is exactly the constant previously requested from a hypothetical
spectral diagonal.  The published source therefore identifies the diagonal:
it is a **zeta-zero residue term**, not a diagonal extracted from the
pointwise cotangent reciprocity.

The error estimate in this argument uses RH and

\[
 \sum_{|\Im\rho|\le T}\frac1{|\zeta'(\rho)|^2}
 \ll T^{3/2-\delta}
 \tag{10}
\]

for some `delta>0`; (10) also entails that the zeros under consideration are
simple.  The resulting theorem is the conditional asymptotic

\[
 E_N^{\mathrm{BCF}}
 \sim\frac{2+\gamma-\log(4\pi)}{\log N}.
 \tag{11}
\]

## 5. Audit of the proposed automorphic sources

Two corpus records proposed for the GL(2)/trace-formula continuation are
misidentified:

- arXiv `1503.05121` is Matomaki--Radziwill--Tao, *An averaged form of
  Chowla's conjecture*, not *Fourier Analysis on GL(2)*;
- arXiv `1807.08249` is Martin Kilbinger's astrophysics habilitation on weak
  cosmological lensing, not *L-Functions and Modular Forms*.

The checked paper `1601.06839` concerns Bettin--Conrey cotangent reciprocity
and Estermann special values, not a Kuznetsov trace formula.  The current
corpus therefore contains no verified trace theorem with the normalization
required by (3).

A genuinely relevant nearby source is Bettin--Chandee--Radziwill,
arXiv `1411.7764`, on mean squares of zeta times Dirichlet polynomials.  It
controls certain finite-length regimes via Kloosterman-fraction estimates,
but its strongest general trilinear input is conjectural and is stated to
imply Lindelof.  It does not turn (11) into an unconditional theorem.

## 6. Formalization gate

The mathematics is settled enough for the following **conditional** work
package, but not for an unconditional H15 proof:

1. define `bcfDirichletPolynomial` and the finite BCF approximation error;
2. use the existing theorems `mellin_chi01` and `mellin_rhoBD` to prove (6);
3. supply a Mellin--Plancherel theorem and prove (7);
4. state RH, zeta-zero simplicity, and (10) explicitly;
5. formalize the contour/residue expansion (8) and derive (11).

Steps 3--5 require substantial analytic infrastructure not present in the
current `NBMellinTools` layer.  In particular, the project currently has the
elementary Mellin evaluation but no project theorem implementing the needed
Mellin--Plancherel isometry or the reciprocal zeta-derivative zero sum.

No unconditional theorem, no new axiom, and no H15 Lean placeholder should
be introduced in their place.

## 7. Recommended next action

Mark the centered Estermann/Kuznetsov route as **audited but not discharged**.
Then choose explicitly between:

- a conditional BCF formalization starting with the exact algebraic Mellin
  identity (6); or
- leaving H15 as the open quantitative input in the already formalized
  Nyman--Beurling-to-RH implication.

The first option faithfully reconstructs a published conditional theorem.
The second preserves the project as an honest RH-equivalence framework.
Neither should be described as an unconditional completion of H15.
