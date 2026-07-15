# H15 BCF centered-energy derivation

## Scope and status

This note derives the complete finite energy for the Bettin--Conrey--Farmer
logarithmic taper.  Every displayed identity through the DFI-ready form is
exact.  No analytic estimate, RH assumption, limiting interchange, or Lean
formalization is used.  At this algebraic stage the tail term is **exactly
zero**: all sums are finite.

The derivation also audits and confirms the sign of the log-ratio term in
`H15_BCF_LOG_TAPER_RESEARCH_PROTOCOL.md`.  The exact Vasyunin formula in
`.archive/old_riemann_folder/Criteria/NymanBeurling/VasyuninExplicitFormula.lean`
and the numerical Gram implementation both use

\[
 \frac{k-h}{2hk}\log\frac{h}{k},
\]

and not \(\frac{k-h}{2hk}\log(k/h)\).  For example, the exact \((h,k)=(1,2)\)
entry has the contribution \(\frac14\log(1/2)\), fixing the sign
unambiguously.

## 1. Definitions and coefficient sign

Fix an integer \(N\ge 2\), and write

\[
 L=\log N,\qquad
 w_N(n)=1-\frac{\log n}{L},\qquad
 a_N(n)=\mu(n)w_N(n) \quad (1\le n\le N).
\]

The coefficient in the Nyman--Beurling approximation is

\[
 c_N(n)=-a_N(n).
\]

Thus the error function is

\[
 \chi-\sum_{n\le N}c_N(n)\rho_n
 =\chi+\sum_{n\le N}a_N(n)\rho_n.
\]

This plus sign is important in the linear cross term below.  The endpoint
\(n=N\) may be included because \(w_N(N)=0\).  No convention at \(N=1\) is
needed because the logarithmic taper is only used for \(N\ge2\).

Put

\[
 \lambda=\log(2\pi)-\gamma,
 \qquad
 \ell(n)=\frac{\log n+1-\gamma}{n}.
\]

The exact inner products are

\[
 \langle\chi,\rho_n\rangle=\ell(n)
\]

and, for positive integers \(h,k\),

\[
 \begin{aligned}
 B(h,k):=\langle\rho_h,\rho_k\rangle
 ={}&\frac{\lambda}{2}\left(\frac1h+\frac1k\right)
     +\frac{k-h}{2hk}\log\frac hk\\
 &-\frac{\pi}{2hk}\bigl(V(h,k)+V(k,h)\bigr),
 \end{aligned}
 \tag{1}
\]

where

\[
 V(p,q)=\sum_{u=1}^{q-1}
 \left\{\frac{up}{q}\right\}\cot\frac{\pi u}{q}.
 \tag{2}
\]

In particular, \(V(h,h)=0\), \(B(h,h)=\lambda/h\), and the nonsmooth
kernel

\[
 K(h,k)=B(h,k)-\frac{\lambda}{2}
 \left(\frac1h+\frac1k\right)
 \tag{3}
\]

satisfies \(K(h,h)=0\).  Both \(B\) and \(K\) are symmetric.

## 2. Complete energy before any phase expansion

Expanding the squared norm with the sign convention above gives

\[
 \boxed{
 E_N^{\mathrm{BCF}}
 =1+2\sum_{n\le N}a_N(n)\ell(n)
   +\sum_{h,k\le N}a_N(h)a_N(k)B(h,k).
 }
 \tag{4}
\]

Equation (4), rather than a separate bound for any of its components, is the
authoritative centered finite expression.

For a second useful form, define

\[
 S_0=\sum_{n\le N}a_N(n),\qquad
 S_1=\sum_{n\le N}\frac{a_N(n)}n,\qquad
 S_{\log}=\sum_{n\le N}\frac{a_N(n)\log n}{n}.
\]

The rank-two smooth part of the Gram sum collapses exactly:

\[
 \sum_{h,k\le N}a_N(h)a_N(k)
 \frac{\lambda}{2}\left(\frac1h+\frac1k\right)
 =\lambda S_0S_1.
\]

Consequently

\[
 \boxed{
 E_N^{\mathrm{BCF}}=C_N+
 \sum_{h,k\le N}a_N(h)a_N(k)K(h,k),
 }
 \tag{5}
\]

where the entire scalar centering term is

\[
 \boxed{
 C_N=1+2S_{\log}+2(1-\gamma)S_1+\lambda S_0S_1.
 }
 \tag{6}
\]

Equivalently, if
\(A_N(s)=\sum_{n\le N}a_N(n)n^{-s}\), then

\[
 C_N=1-2A_N'(1)+2(1-\gamma)A_N(1)
       +\lambda A_N(0)A_N(1).
\]

The cancellation between \(C_N\) and the \(K\)-quadratic form must be kept.
Taking absolute values of these two quantities separately does not follow
from, and is stronger than, the desired energy estimate.

## 3. Exact gcd stratification

Write

\[
 h=gp,\qquad k=gq,\qquad (p,q)=1,
 \qquad M_g=\left\lfloor\frac Ng\right\rfloor.
\]

The endpoint ranges are
\(1\le g\le N\) and \(1\le p,q\le M_g\).  The finite cotangent definition
implies

\[
 V(gp,gq)=gV(p,q),qquad
 B(gp,gq)=\frac1gB(p,q),qquad
 K(gp,gq)=\frac1gK(p,q).
 \tag{7}
\]

For coprime \(p,q\), Möbius multiplicativity with the possible zero cases
retained gives

\[
 \mu(gp)\mu(gq)
 =\mu(g)^2\mu(p)\mu(q)
   \mathbf 1_{(g,p)=1}\mathbf 1_{(g,q)=1}.
 \tag{8}
\]

Define the exact fixed-stratum coefficient

\[
 \alpha_{N,g}(p)=
 \mathbf 1_{p\le M_g}\mathbf 1_{(p,g)=1}\,
 \mu(p)\left(1-\frac{\log g+\log p}{L}\right).
 \tag{9}
\]

Then the complete, pre-Fourier, gcd-stratified identity is

\[
 \boxed{
 \begin{aligned}
 E_N^{\mathrm{BCF}}={}&1+2\sum_{n\le N}a_N(n)\ell(n)\\
 &+\sum_{g\le N}\frac{\mu(g)^2}{g}
   \sum_{\substack{p,q\le M_g\\(p,q)=1}}
   \alpha_{N,g}(p)\alpha_{N,g}(q)\\
 &\quad\times\left[
   \frac{\lambda}{2}\left(\frac1p+\frac1q\right)
   +\frac{q-p}{2pq}\log\frac pq
   -\frac{\pi}{2pq}\bigl(V(p,q)+V(q,p)\bigr)
   \right].
 \end{aligned}
 }
 \tag{10}
\]

Everything in the square bracket is still paired.  Formula (10) includes the
diagonal correctly: under \((p,q)=1\), the only diagonal pair is
\((p,q)=(1,1)\), and its bracket is \(B(1,1)=\lambda\).  The apparently
degenerate stratum \(g=N\) contributes zero because \(w_N(N)=0\).

There is no gcd remainder and no boundary tail in (10).

## 4. Exact modular-inverse conversion

Let

\[
 e(x)=e^{2\pi i x}.
\]

For \(q\ge2\) and \(1\le \nu\le q-1\), the finite Fourier transform is

\[
 \sum_{u=1}^{q-1}\cot\frac{\pi u}{q}\,e(u\nu/q)
 =i(q-2\nu),
 \tag{11}
\]

while its zero Fourier coefficient is zero.  Fourier inversion therefore
gives

\[
 \cot\frac{\pi u}{q}
 =\frac{i}{q}\sum_{\nu=1}^{q-1}(q-2\nu)e(-u\nu/q).
 \tag{12}
\]

If \((p,q)=1\) and \(q\ge2\), let \(\bar p_q\in\{1,\ldots,q-1\}\) denote
the inverse of \(p\) modulo \(q\).  Substituting
\(r\equiv up\pmod q\) in (2), with \(1\le r\le q-1\), yields

\[
 \boxed{
 V(p,q)=\frac{i}{q^2}
 \sum_{r=1}^{q-1}\sum_{\nu=1}^{q-1}
 r(q-2\nu)e(-\nu r\bar p_q/q).
 }
 \tag{13}
\]

The sign in the exponential and the leading \(+i\) are fixed by (11).  As a
real check, (13) is equivalently

\[
 V(p,q)=\frac1{q^2}
 \sum_{r,\nu=1}^{q-1}r(q-2\nu)
 \sin(2\pi\nu r\bar p_q/q).
\]

For \(q=1\), definition (2) is an empty sum, so \(V(p,1)=0\); no inverse
modulo one is introduced.  This convention also handles every endpoint in
(10).

For direct theorem matching it is useful to compress the product
\(\nu r\) modulo \(q\).  For \(b\in\mathbb Z/q\mathbb Z\), set

\[
 \beta_q(b)=\frac1{q^2}
 \sum_{\substack{1\le r,\nu\le q-1\\r\nu\equiv b\pmod q}}
 r(q-2\nu).
 \tag{14}
\]

Then

\[
 V(p,q)=i\sum_{b\bmod q}\beta_q(b)e(-b\bar p_q/q).
 \tag{15}
\]

The apparent zero phase vanishes exactly:

\[
 \boxed{\beta_q(0)=0.}
 \tag{16}
\]

Indeed, for fixed \(r\), the set of \(\nu\) with \(q\mid r\nu\) is stable
under \(\nu\mapsto q-\nu\), and the weights \(q-2\nu\) cancel in pairs; a
possible fixed point \(\nu=q/2\) has weight zero.

## 5. DFI-ready centered formula

Use symmetry of the \((p,q)\)-range and its coefficient product to combine
the two directed cotangent sums exactly:

\[
 \sum_{\substack{p,q\le M_g\\(p,q)=1}}
 \frac{\alpha_{N,g}(p)\alpha_{N,g}(q)}{2pq}
 \bigl(V(p,q)+V(q,p)\bigr)
 =
 \sum_{\substack{p,q\le M_g\\(p,q)=1}}
 \frac{\alpha_{N,g}(p)\alpha_{N,g}(q)}{pq}V(p,q).
 \tag{17}
\]

Define

\[
 \mathfrak L_{N,g}=
 \sum_{\substack{p,q\le M_g\\(p,q)=1}}
 \alpha_{N,g}(p)\alpha_{N,g}(q)
 \frac{q-p}{2pq}\log\frac pq
 \tag{18}
\]

and

\[
 \begin{aligned}
 \mathfrak P_{N,g}
 =\operatorname{Re}\Bigg(&-\pi i
 \sum_{q=2}^{M_g}\frac{\alpha_{N,g}(q)}q
 \sum_{\substack{p\le M_g\\(p,q)=1}}
       \frac{\alpha_{N,g}(p)}p\\
 &\qquad\qquad\times
 \sum_{\substack{b\bmod q\\b\ne0}}
 \beta_q(b)e(-b\bar p_q/q)\Bigg).
 \end{aligned}
 \tag{19}
\]

The real part in (19) is harmless bookkeeping: by (13)--(15), the complex
quantity inside it is already real after the complete finite summation.

Combining (5)--(6), (7)--(9), and (17)--(19) gives the requested exact
DFI-ready expression:

\[
 \boxed{
 E_N^{\mathrm{BCF}}
 =C_N+\sum_{g\le N}\frac{\mu(g)^2}{g}
 \bigl(\mathfrak L_{N,g}+\mathfrak P_{N,g}\bigr).
 }
 \tag{20}
\]

Equation (20) is one centered identity, not permission to estimate
\(C_N\), \(\mathfrak L_{N,g}\), and \(\mathfrak P_{N,g}\) separately.
Its exact remainder/tail is zero.

The direct DFI/Bettin--Chandee dictionary in (19) is:

| theorem variable | exact H15 variable |
|---|---|
| inverse variable \(m\) | \(p\) |
| modulus \(n\) | \(q\) |
| numerator \(a\) | \(-b\), originally \(-\nu r\) |
| \(m\)-coefficient | \(\alpha_{N,g}(p)/p\) |
| modulus coefficient | \(\alpha_{N,g}(q)/q\) |
| numerator amplitude | \(\beta_q(b)\), which depends on \(q\) |
| outer stratum | \(\mu(g)^2/g\), with \(M_g=\lfloor N/g\rfloor\) |

For fixed \(g\), the elementary coefficient bounds are

\[
 |\alpha_{N,g}(p)|\le1,
 \qquad
 \sum_{p\le M_g}\left|\frac{\alpha_{N,g}(p)}p\right|^2
 \le\sum_{p\ge1}\frac1{p^2}=\zeta(2).
 \tag{21}
\]

In contrast, taking absolute values inside (14) only gives

\[
 \sum_{b\bmod q}|\beta_q(b)|
 \le \frac{q-1}{2q}\sum_{\nu=1}^{q-1}|q-2\nu|
 \asymp q^2.
 \tag{22}
\]

Thus expanding the \((r,\nu)\)-sum and using a triangle inequality destroys
the cancellation that the centered identity needs.

## 6. First genuine theorem gap

All of the following are now exact bookkeeping, not gaps:

1. the BCF coefficient and endpoint convention;
2. the coefficient sign in the norm expansion;
3. the Gram/Vasyunin formula with the corrected log sign;
4. gcd homogeneity and all gcd strata;
5. the finite modular-inverse transform;
6. removal of the apparent zero phase \(\beta_q(0)\);
7. the absence of algebraic tails.

The first genuine theorem gap is a **centered, modulus-dependent
Kloosterman-fraction estimate** proving, for some absolute \(C,N_0\),

\[
 \boxed{
 0\le
 C_N+\sum_{g\le N}\frac{\mu(g)^2}{g}
       \bigl(\mathfrak L_{N,g}+\mathfrak P_{N,g}\bigr)
 \le\frac{C}{\log N}
 \qquad(N\ge N_0).
 }
 \tag{23}
\]

The left inequality is already known from the squared-norm interpretation;
the new analytic content is the upper bound.

Existing fixed-numerator DFI estimates do not apply directly to (19), and
the Bettin--Chandee trilinear coefficient pattern
\(\nu_b\alpha_p\beta_q\) does not match it either: the exact amplitude is
\(\beta_q(b)\), coupled jointly to numerator and modulus.  In the uncompressed
form the numerator is the product \(b=\nu r\), with both factors ranging up
to \(q\).  Moreover, any theorem must retain the cancellation of the phase
sum with the log-ratio term and the global scalar \(C_N\) in (20).

Therefore the next mathematical step is not another componentwise DFI
bound.  It is one of:

1. transform \(\beta_q(b)\) into a separable spectral/Estermann expression
   while tracking (18) and \(C_N\) as its polar or zero-mode terms; or
2. prove a new modulus-dependent Kloosterman-fraction estimate directly for
   the complete combination in (20), with dyadic majorants summing to
   \(O(1/\log N)\).

Until such a theorem is supplied and independently checked, (23) remains an
unproved analytic assertion.  The conditional BCF theorem is a benchmark for
the expected size, not an unconditional discharge of this gap.
