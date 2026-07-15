# H15 character-sum route audit

**Date:** 15 July 2026

**Status:** paper-level research only; no Lean formalization authorized

**Verdict:** exact diagnostic decomposition, not a route to the required bound

## 1. Executive conclusion

Multiplicative characters do diagonalize the restriction of the BCF amplitude
`beta_q` to the unit group.  The resulting formula is exact and may be useful
for checking normalizations or identifying odd spectral components.  It does
not close H15 for four independent reasons:

1. characters modulo `q`, extended by zero, do not see the non-unit residue
   strata of the complete amplitude;
2. after expanding the additive H15 phase, the remaining `p`-sum is
   Mobius-twisted, whereas classical character-sum estimates control an
   untwisted character sum;
3. the moduli vary with the BCF truncation, so there is no fixed character
   Parseval identity across the complete centered energy;
4. bounds for individual character components do not produce the explicit
   scalar and logarithmic main terms that must cancel in the centered BCF
   identity.

Angle 1 should therefore be retained as a finite spectral diagnostic and not
ranked above the centered Estermann/Kuznetsov main-term problem already
isolated in `H15_BCF_BETA_AMPLITUDE_ANALYSIS.md`.

## 2. Source audit

### 2.1 Misidentified arXiv record

The corpus entry for arXiv `1409.1634` is incorrect.  The PDF and the official
arXiv record are

> Jean Bourgain and Ciprian Demeter, *Decouplings for curves and
> hypersurfaces with nonzero Gaussian curvature*.

It is not a Beck paper and contains no Dirichlet-character-sum theorem for
H15.  The corpus title `Dirichlet Character Sums`, the placeholder author, the
H13 role, and the character tags must not be used as mathematical evidence.
The bad record is duplicated in the root legacy, complete, and cleaned JSON
databases and their `doc/html` mirrors; generated knowledge-graph and RDF
artifacts may therefore inherit it.  This research branch records the error
but does not silently regenerate that broader data pipeline.

### 2.2 Auli--Bayad--Beck

ArXiv `1601.06839` is correctly the paper

> Juan S. Auli, Abdelmejid Bayad, and Matthias Beck, *Reciprocity Theorems for
> Bettin--Conrey Sums*.

Its content is cotangent-sum reciprocity, period functions of Eisenstein
series, Hurwitz zeta, and Estermann special values.  It contains no
multiplicative-character decomposition and no Polya--Vinogradov-type bound.
It supports the Estermann route, not the proposed character-bound route.

### 2.3 A relevant character paper

A genuinely relevant Beck source is

> Matthias Beck and Mary Halloran, *Finite Trigonometric Character Sums Via
> Discrete Fourier Analysis*, arXiv `0804.0645`.

It proves exact finite identities by discrete Fourier convolution for real,
primitive, often odd characters.  Those identities support the finite
factorization below.  They do not estimate the varying-modulus,
Mobius-weighted BCF aggregate at the scale `O(1 / log N)`.

## 3. Exact character factorization on the unit stratum

Let `q > 2`, let

\[
 U_q=(\mathbb Z/q\mathbb Z)^\times,
\]

and use least positive representatives in every sum.  From the divisor
formula in `H15_BCF_BETA_AMPLITUDE_ANALYSIS.md`, if `(b,q)=1` then only the
divisor `d=1` occurs, so

\[
 \beta_q(b)=\frac1{q^2}\sum_{u\in U_q}(q-2u)[b\bar u]_q.
 \tag{1}
\]

For a multiplicative character `chi` of `U_q`, define

\[
 S_q(\chi)=\sum_{u\in U_q}u\,\overline{\chi(u)}
\]

and the unnormalized multiplicative transform

\[
 \mathcal M\beta_q(\chi)
 =\sum_{b\in U_q}\beta_q(b)\overline{\chi(b)}.
\]

Substitute (1), put `v=b u^{-1}`, and use multiplicativity.  This gives the
exact product

\[
 \mathcal M\beta_q(\chi)
 =\frac1{q^2}
 \left(\sum_{u\in U_q}(q-2u)\overline{\chi(u)}\right)
 \left(\sum_{v\in U_q}v\overline{\chi(v)}\right).
 \tag{2}
\]

The principal component is zero because the reduced residues pair as
`u` and `q-u`.  For a nonprincipal character, character orthogonality removes
the constant part of the first factor, so

\[
 \boxed{
 \mathcal M\beta_q(\chi)=-\frac2{q^2}S_q(\chi)^2.}
 \tag{3}
\]

If `chi` is even, pairing `u` with `q-u` also gives `S_q(chi)=0`.  Thus only
odd nonprincipal characters occur, and character inversion yields

\[
 \boxed{
 \beta_q(b)=
 -\frac{2}{q^2\varphi(q)}
 \sum_{\substack{\chi\bmod q\\
                  \chi\ne\chi_0,\ \chi(-1)=-1}}
 S_q(\chi)^2\chi(b),
 \qquad (b,q)=1.}
 \tag{4}
\]

Equations (1)--(4) are finite algebra.  They require no analytic estimate.
A direct floating-point enumeration for primes `3, 5, 7, 11, 13, 17, 19`
and composite cyclic-unit cases `9, 10, 14, 18` reconstructed every unit
value from (4), with maximum numerical discrepancies between `5e-17` and
`1.1e-14`.  This is a normalization check, not a proof.

## 4. What happens to the H15 additive phase

Insert (4) into the unit contribution to the primitive additive phase.  One
obtains Gauss sums:

\[
 \sum_{b\in U_q}\beta_q(b)e(-b\bar p/q)
 =-\frac{2}{q^2\varphi(q)}
 \sum_{\chi\ \mathrm{odd}}S_q(\chi)^2
 \sum_{b\in U_q}\chi(b)e(-b\bar p/q).
 \tag{5}
\]

For a primitive character the inner sum is a Gauss sum times a character
value at `p`; imprimitive characters require their usual conductor
corrections.  After the outer BCF sum over `p`, the new analytic object is of
the form

\[
 \sum_{p\le N}\frac{\mu(p)w_N(p)}p\chi(p),
 \tag{6}
\]

up to the exact coefficients and dyadic cutoffs.

Polya--Vinogradov estimates `sum chi(n)`.  It does not estimate (6), because
partial summation cannot remove the Mobius factor.  Uniform cancellation in
(6) for moduli as large as the truncation is controlled by reciprocal
Dirichlet `L`-functions and their zero-free information.  Treating it as an
automatic consequence of character orthogonality would simply hide the
original hard problem in a new notation.

There is a second loss: (4) covers only `(b,q)=1`.  The complete amplitude has
non-unit gcd strata.  They can be decomposed into characters at several
quotient moduli, but this is precisely the conductor mixing already captured
more cleanly by the additive decomposition

\[
 \widehat\beta_q(a)=iV(\bar a_0,q/(a,q)).
\]

At the primitive H15 frequency, that additive decomposition selects the top
conductor and reconstructs the original Vasyunin sum.  Multiplicative
characters do not create an additional average there.

## 5. Bound and normalization audit

The conditional proposal

\[
 |\beta_q(b)|\le B/\sqrt q
\]

has the wrong normalization.  The proven prime second moment is

\[
 \sum_{b\bmod p}|\beta_p(b)|^2
 =\left(\frac5{36}+o(1)\right)p^2.
\]

Consequently the root-mean-square size of the unnormalized amplitude is

\[
 \left(\frac1p\sum_b|\beta_p(b)|^2\right)^{1/2}
 \sim\frac{\sqrt5}{6}\sqrt p,
\]

not `p^(-1/2)`.  The normalized quantity `beta_p(b)/p` has root-mean-square
size of order `p^(-1/2)`.  Any conditional numerical experiment must state
which normalization it is testing.

Even an optimal norm bound for the normalized amplitude is insufficient by
itself: the balanced-block calculation in
`H15_BCF_BETA_AMPLITUDE_ANALYSIS.md` still leaves a positive power.  H15 needs
an asymptotic with a matching diagonal or polar main term, not only a smaller
absolute-value estimate.

## 6. Lean feasibility audit

The checked Mathlib version contains Dirichlet-character definitions and
orthogonality relations.  It does not contain a theorem identifiable as
Polya--Vinogradov or Burgess.  Therefore:

- formalizing equations (1)--(4): high feasibility, but premature and not a
  solution to H15;
- formalizing the analytic bounds proposed in Angle 1: low feasibility until
  a mathematically sufficient theorem is first identified and proved on
  paper;
- current decision: make no H15 Lean changes.

## 7. Revised ranking and next experiment

1. **Primary:** centered Estermann/Kuznetsov reciprocity with an explicit
   diagonal or polar main term matching the scalar and log-ratio pieces.
2. **Diagnostic:** multiplicative-character expansion, used to identify odd
   components and verify finite normalizations.
3. **Fallback:** conditional and numerical work with the corrected
   normalization, while explicitly preserving the complete centered energy.
4. **Deferred:** a general GL(2) formulation until an exact automorphic object
   for the complete BCF kernel, rather than only an analogy, is exhibited.

The next paper-level question is:

> After inserting the primitive Estermann spectrum into the exact centered
> BCF identity, which reciprocity or trace formula produces the scalar and
> logarithmic terms as its diagonal/polar contribution, and what is the total
> off-diagonal remainder for the exact Mobius logarithmic weights?

That question preserves the cancellation H15 needs.  Character orthogonality
alone does not.
