# H15 BCF amplitude analysis: the exact structure of \(\beta_q(b)\)

## Scope and verdict

This note continues the paper-level analysis in
`H15_BCF_CENTERED_ENERGY_DERIVATION.md`.  It makes no Lean changes and assumes
no unproved estimate unless it is explicitly labeled **conditional** or
**heuristic**.

The amplitude

\[
 \beta_q(b)=\frac1{q^2}
 \sum_{\substack{1\le r,\nu\le q-1\\r\nu\equiv b\pmod q}}
 r(q-2\nu)
 \tag{1}
\]

is not an arbitrary modulus-dependent coefficient.  Its additive Fourier
transform is exactly a Vasyunin sum of an exact divisor of \(q\), equivalently
a centered Estermann value at \(s=0\).  This gives a complete conductor
diagonalization and exact \(L^2\)-orthogonality formulae.

This structure does **not** close H15.  In the H15 phase the frequency is
primitive modulo \(q\), so the phase samples only the top-conductor component
and reconstructs \(V(p,q)\).  Existing DFI/Bettin--Chandee estimates still
leave a positive power on balanced blocks.  Moreover, even a hypothetical
matrix-valued DFI estimate with the optimal Frobenius dependence would only
give a power-growing error, not the centered \(O(1/\log N)\) result.

The smallest genuinely sufficient new result is therefore a **centered
asymptotic theorem with an explicit main term**, specialized to the BCF/Möbius
coefficients.  A stronger norm bound for \(\beta_q\) alone is insufficient.

## 1. Elementary symmetries and a divisor formula

Throughout, \(e(x)=e^{2\pi i x}\), residues \(b\pmod q\) are represented by
\(0,\ldots,q-1\), and \([x]_Q\in\{0,\ldots,Q-1\}\) denotes the least residue.

The involution \(\nu\mapsto q-\nu\) in (1) proves

\[
 \boxed{\beta_q(-b)=-\beta_q(b).}
 \tag{2}
\]

Consequently

\[
 \beta_q(0)=0,
 \qquad
 \beta_q(q/2)=0\quad(2\mid q),
 \qquad
 \sum_{b\bmod q}\beta_q(b)=0.
 \tag{3}
\]

There is also an exact formula exposing the gcd structure.  Fix
\(b\in\{1,\ldots,q-1\}\).  Put \(d=(\nu,q)\), \(Q=q/d\), and \(\nu=du\), so
that \(u\in(\mathbb Z/Q\mathbb Z)^\times\).  The congruence in (1) has
solutions only when \(d\mid b\), and then

\[
 r\equiv r_0:=\bigl[(b/d)\bar u\bigr]_Q\pmod Q.
\]

Because \(0<b/d<Q\), one has \(1\le r_0<Q\), and the solutions in
\(1\le r<q\) are \(r_0+jQ\), \(0\le j<d\).  Hence

\[
 \sum_{\substack{1\le r<q\\ru\equiv b/d\pmod Q}}r
 =d r_0+\frac{Qd(d-1)}2.
\]

The progression-mean term disappears after summing over \(u\), since

\[
 \sum_{u\in(\mathbb Z/Q\mathbb Z)^\times}(Q-2u)=0.
\]

This proves the closed divisor formula

\[
 \boxed{
 \beta_q(b)=\frac1{q^2}
 \sum_{d\mid(b,q)}d^2
 \sum_{u\in(\mathbb Z/(q/d)\mathbb Z)^\times}
 \left(\frac qd-2u\right)
 \left[(b/d)\bar u\right]_{q/d}.}
 \tag{4}
\]

Formula (4) is exact.  It is not a Ramanujan expansion: the inner inverse
residue depends on more than \((b,q)\).

## 2. Exact additive Fourier transform

Define the unnormalized transform

\[
 \widehat\beta_q(a)=
 \sum_{b\bmod q}\beta_q(b)e(ab/q).
 \tag{5}
\]

For \(z^q=1\), direct differentiation of the finite geometric series gives

\[
 \sum_{\nu=1}^{q-1}(q-2\nu)z^\nu
 =
 \begin{cases}
  iq\cot(\pi x),&z=e(x),\ z\ne1,\\
  0,&z=1.
 \end{cases}
 \tag{6}
\]

Substitution in (5) yields

\[
 \widehat\beta_q(a)
 =\frac{i}{q}
 \sum_{\substack{1\le r<q\\q\nmid ar}}
 r\cot\frac{\pi ar}{q}.
 \tag{7}
\]

Let \(a\ne0\pmod q\), \(\delta=(a,q)\), \(Q=q/\delta\), and
\(a_0=a/\delta\), so \((a_0,Q)=1\).  Grouping
\(r=u+jQ\) in (7), the constant progression term again vanishes because
the complete cotangent sum is zero.  Therefore

\[
 \widehat\beta_q(a)
 =\frac{i}{Q}\sum_{u=1}^{Q-1}u\cot\frac{\pi a_0u}{Q}
 =iV(\bar a_0,Q).
 \tag{8}
\]

Together with the zero frequency, the full spectral formula is

\[
 \boxed{
 \widehat\beta_q(0)=0,
 \qquad
 \widehat\beta_q(a)=iV(\bar a_0,Q)
 \quad
 \left(Q=\frac q{(a,q)},\ a_0=\frac a{(a,q)}\right).}
 \tag{9}
\]

### Estermann interpretation

For coprime \(h,k\), use the conventions

\[
 c_0(h/k)=-\sum_{m=1}^{k-1}\frac mk\cot\frac{\pi mh}{k},
 \qquad
 V(p,k)=-c_0(\bar p/k).
\]

The Estermann function satisfies

\[
 D(0,h/k)=\frac14+\frac i2c_0(h/k).
\]

Thus (9) is equivalently

\[
 \boxed{
 \widehat\beta_q(a)
 =-i c_0(a_0/Q)
 =\frac12-2D(0,a_0/Q).}
 \tag{10}
\]

The right-hand side of (10) is purely imaginary, consistently with the
oddness of \(\beta_q\).  Equations (9)--(10) are the precise transformation of
\(\beta_q\) into Vasyunin/Estermann data.  The primary normalization source is
S. Bettin and J. B. Conrey, *Period functions and cotangent sums*,
https://arxiv.org/abs/1111.0931.

## 3. Conductor diagonalization and exact orthogonality

For \(Q>1\), define the exact-conductor function on \(\mathbb Z/Q\mathbb Z\)

\[
 \gamma_Q(b)=\frac{i}{Q}
 \sum_{u\in(\mathbb Z/Q\mathbb Z)^\times}
 V(\bar u,Q)e(-ub/Q).
 \tag{11}
\]

Its Fourier transform is supported precisely on primitive frequencies modulo
\(Q\).  Fourier inversion in (9) gives

\[
 \boxed{
 \beta_q(b)=
 \sum_{\substack{Q\mid q\\Q>1}}
 \frac Qq\,\gamma_Q(b\bmod Q).}
 \tag{12}
\]

This is an exact orthogonal conductor decomposition.  Ordinary Möbius
inversion gives the converse

\[
 \boxed{
 \gamma_q(b)=\frac1q
 \sum_{d\mid q}\mu(q/d)d\,\beta_d(b\bmod d).}
 \tag{13}
\]

Here and in (13), \(\beta_1=\gamma_1=0\) by the empty-sum convention.

The components with different exact additive conductors are orthogonal.  In
particular,

\[
 \sum_{b\bmod q}
 \left|\frac Qq\gamma_Q(b)\right|^2
 =\frac1q
 \sum_{u\in(\mathbb Z/Q\mathbb Z)^\times}V(u,Q)^2.
 \tag{14}
\]

There is also an exact correlation formula between different moduli.  If
\(L\) is any common multiple of \(q\) and \(r\), lift both functions
periodically to \(\mathbb Z/L\mathbb Z\).  Then

\[
 \boxed{
 \frac1L\sum_{b\bmod L}\beta_q(b)\beta_r(b)
 =\frac1{qr}
 \sum_{\substack{Q\mid(q,r)\\Q>1}}
 \sum_{u\in(\mathbb Z/Q\mathbb Z)^\times}V(u,Q)^2.}
 \tag{15}
\]

Thus two amplitudes share exactly the conductors dividing \((q,r)\); there is
no unexplained cross-conductor interaction.

## 4. Exact and asymptotic norms

### 4.1 Exact \(L^2\) norm

Parseval applied to (9) gives

\[
 \boxed{
 \|\beta_q\|_2^2
 :=\sum_{b\bmod q}|\beta_q(b)|^2
 =\frac1q
 \sum_{\substack{Q\mid q\\Q>1}}
 \sum_{u\in(\mathbb Z/Q\mathbb Z)^\times}V(u,Q)^2.}
 \tag{16}
\]

This is an exact equality, not a bound.  It reduces every \(L^2\) question
about \(\beta_q\) to second moments of the classical cotangent sum.

For a prime \(p\), only \(Q=p\) occurs:

\[
 \|\beta_p\|_2^2
 =\frac1p\sum_{u=1}^{p-1}c_0(u/p)^2.
 \tag{17}
\]

Known moment equidistribution for \(c_0(u/p)/p\) implies

\[
 \boxed{
 \|\beta_p\|_2^2
 =\left(\frac5{36}+o(1)\right)p^2
 \qquad(p\to\infty\text{ through primes}).}
 \tag{18}
\]

For completeness, the constant can be computed from the limiting function

\[
 g(x)=\sum_{n\ge1}\frac{1-2\{nx\}}n
 =\frac2\pi\sum_{m\ge1}\frac{d(m)}m\sin(2\pi mx).
\]

Indeed,

\[
 \int_0^1\left(\frac{g(x)}\pi\right)^2dx
 =\frac2{\pi^4}\sum_{m\ge1}\frac{d(m)^2}{m^2}
 =\frac2{\pi^4}\frac{\zeta(2)^4}{\zeta(4)}
 =\frac5{36}.
\]

The moment source and its normalization are described in H. Maier and
M. Th. Rassias, *Asymptotics for moments of certain cotangent sums*,
https://arxiv.org/abs/1606.03131.  Equation (18) also agrees with direct finite
computations; that agreement is only a check, not part of the proof.

Without invoking a uniform cotangent-moment theorem, the elementary estimate
\(|V(u,Q)|\ll Q\log(2Q)\) and (16) give

\[
 \|\beta_q\|_2\ll q\log(2q),
 \qquad
 \|\beta_q\|_1\ll q^{3/2}\log(2q).
 \tag{19}
\]

Here one uses
\(\sum_{Q\mid q}Q^3\le q^3\sum_{d\ge1}d^{-3}=\zeta(3)q^3\).
Sharper known moment results can remove the logarithm in important families,
but doing so does not repair the later theorem matching.

### 4.2 Exact \(L^1\) representation and unconditional bounds

There is no Parseval identity for \(L^1\).  Combining oddness with (4) gives
the exact expression

\[
 \boxed{
 \|\beta_q\|_1
 =2\sum_{1\le b<q/2}
 \left|
 \frac1{q^2}\sum_{d\mid(b,q)}d^2
 \sum_{u\in(\mathbb Z/(q/d)\mathbb Z)^\times}
 \left(\frac qd-2u\right)
 \left[(b/d)\bar u\right]_{q/d}
 \right|.}
 \tag{20}
\]

Taking absolute values before the congruence compression gives the explicit
triangle bounds

\[
 \boxed{
 \|\beta_q\|_1\le
 \begin{cases}
 \dfrac{(q-1)(q-2)}4,&2\mid q,\\[6pt]
 \dfrac{(q-1)^3}{4q},&2\nmid q.
 \end{cases}}
 \tag{21}
\]

The spectral Cauchy bound

\[
 \|\beta_q\|_1\le\sqrt q\,\|\beta_q\|_2
 \tag{22}
\]

is much stronger once a second-moment estimate is available.  In particular,
for primes, (18) gives

\[
 \|\beta_p\|_1
 \le\left(\frac{\sqrt5}{6}+o(1)\right)p^{3/2}.
 \tag{23}
\]

Finite computations suggest that \(\|\beta_p\|_1\asymp p^{3/2}\), but this
last two-sided assertion is **heuristic here**; it is not needed below.

## 5. What can and cannot be separated

### 5.1 Ramanujan sums do not diagonalize the amplitude

Every Ramanujan sum \(c_Q(b)\) is even in \(b\).  By (2), \(\beta_q\) is odd.
Therefore \(\beta_q\) is orthogonal to every even gcd-class function and
cannot be represented by a linear combination of ordinary Ramanujan sums.
Formula (4) confirms why: inverse residues, rather than only gcd classes,
remain.

### 5.2 Estermann data diagonalize it exactly

Equations (9)--(12) are a complete additive spectral diagonalization.  At a
fixed prime modulus there is also a multiplicative character diagonalization.
For an odd Dirichlet character \(\chi\pmod p\), direct finite Fourier
calculation gives

\[
 \sum_{h\in(\mathbb Z/p\mathbb Z)^\times}
 c_0(h/p)\overline{\chi(h)}
 =\frac{2p}{\pi}L(0,\chi)L(1,\overline\chi),
 \tag{24}
\]

whereas even characters contribute zero.  This is useful spectral
information, but H15 has varying moduli and an incomplete, Möbius-weighted
sum over \(p\), so (24) does not turn the H15 quadratic form into a fixed
character Parseval identity.

### 5.3 The primitive H15 phase selects only the top conductor

For \((p,q)=1\), the frequency \(-\bar p_q\) is primitive modulo \(q\).
Equation (9) therefore gives

\[
 \boxed{
 \sum_{b\bmod q}\beta_q(b)e(-b\bar p_q/q)
 =-iV(p,q).}
 \tag{25}
\]

All proper-divisor conductor components in (12) are orthogonal to this
primitive frequency.  Thus conductor decomposition does not create an extra
average inside the exact H15 phase: it reconstructs the original Vasyunin
sum at the top conductor.

It also proves that no bounded-rank separation
\(\beta_q(b)=\sum_{j\le J}x_j(q)y_j(b)\), with fixed \(J\), can encode all
moduli.  When the functions are lifted to a common cyclic group, every new
modulus \(q\ge3\) contributes a nonzero exact-conductor component supported on
frequencies not present at proper divisors.  These top-conductor components
are mutually orthogonal.  Nonvanishing follows already from
\(V(1,q)<0\): pairing \(u\) with \(q-u\) leaves terms
\((2u/q-1)\cot(\pi u/q)<0\) for \(1\le u<q/2\).

## 6. Exact DFI/Bettin--Chandee retest

The primary theorem used here is Bettin--Chandee, *Trilinear forms with
Kloosterman fractions*, Theorem 1,
https://arxiv.org/abs/1502.00769.  In its notation,

\[
 \mathcal B(M,N,A)\ll
 \|x\|_2\|y\|_2\|z\|_2
 \left(1+\frac{A}{MN}\right)^{1/2}
 \left((AMN)^{7/20+\varepsilon}(M+N)^{1/4}
 +(AMN)^{3/8+\varepsilon}(A(M+N))^{1/8}\right).
 \tag{26}
\]

### 6.1 Compressed amplitude: fixed-numerator DFI

On a balanced block \(p,q\asymp X\), set

\[
 x_p=\frac{\alpha(p)}p,
 \qquad
 W_{q,b}=\frac{\alpha(q)}q\beta_q(b).
\]

The elementary estimate (19), with logarithms absorbed into \(X^\varepsilon\),
already gives

\[
 \|x\|_2\ll X^{-1/2},
 \qquad
 \|W\|_F^2
 =\sum_{q\asymp X}\frac{|\alpha(q)|^2}{q^2}\|\beta_q\|_2^2
 \ll X^{1+\varepsilon}.
 \tag{27}
\]

Apply the fixed-numerator DFI estimate separately for each \(b\), then use
Cauchy in \(b\):

\[
 \sum_{b\ll X}\|W_{\cdot,b}\|_2
 \le X^{1/2}\|W\|_F\ll X^{1+\varepsilon}.
\]

Since the balanced DFI kernel is \(X^{47/48+\varepsilon}\), the resulting
bound is

\[
 \boxed{X^{71/48+\varepsilon}.}
 \tag{28}
\]

This is even worse than the direct \(O(X\log X)\) bound obtained on the same
block from \(|V(p,q)|\ll q\log(2q)\).  The exact \(L^2\) structure of
\(\beta_q\) therefore does not make fixed-numerator DFI useful after summing
the numerator.

### 6.2 Compressed amplitude: singular-value separation

Any finite matrix \(W_{q,b}\) can be separated by singular-value
decomposition.  Bettin--Chandee must then be summed with the nuclear norm.
From (27),

\[
 \|W\|_*\le\sqrt{\operatorname{rank}W}\,\|W\|_F
 \ll X^{1+\varepsilon}.
\]

In (26), \(A=M=N=X\) gives a dominant kernel \(X^{11/8+\varepsilon}\).
After the factor \(\|x\|_2\|W\|_*\), this is

\[
 \boxed{X^{15/8+\varepsilon}.}
 \tag{29}
\]

Numerical SVDs of the padded matrices \((\beta_q(b)/q)_{X\le q<2X}\) have
full row rank and nuclear norm approximately \(0.17X\) to \(0.22X\) for
\(16\le X\le256\).  This supports the claim that the generic nuclear-norm
loss is real, but these numerical constants are **heuristic**, not a proof.

### 6.3 Uncompressed product numerator

The product numerator can in fact be made separable after dyadic subdivision;
the obstruction is the resulting exponent, not an algebraic impossibility.
On \(r\asymp R\), \(\nu\asymp U\), split

\[
 \frac{r(q-2\nu)}{q^3}
 =\frac r{q^2}-\frac{2r\nu}{q^3}
\]

and group \(a=r\nu\).  The numerator coefficients satisfy

\[
 \left\|\sum_{r\nu=a}r\right\|_2
 \ll R^{3/2}U^{1/2}(RU)^\varepsilon,
 \qquad
 \left\|\sum_{r\nu=a}r\nu\right\|_2
 \ll R^{3/2}U^{3/2}(RU)^\varepsilon.
 \tag{30}
\]

The corresponding modulus norms are \(Q^{-3/2}\) and \(Q^{-5/2}\), and
the inverse-variable norm is \(P^{-1/2}\).  In the worst balanced box

\[
 P=Q=R=U=X,
 \qquad A=RU=X^2,
\]

both products of coefficient norms are \(X^{o(1)}\).  Substitution in (26)
again gives

\[
 \boxed{X^{15/8+\varepsilon}.}
 \tag{31}
\]

Thus the earlier \(15/8\) exponent is confirmed with all coefficient weights
included.  In the boundary boxes, the conditions \(r,\nu<q\) require a
standard Mellin/partial-summation separation of the triangular cutoff.  This
costs logarithms (absorbed in \(X^\varepsilon\)) and does not improve the
worst exponent.

The newer fixed-numerator bilinear improvement of Dong--Robles--Zeindler,
https://arxiv.org/abs/2601.00292, does not address the joint \((q,b)\)
coefficient or the centered main term, so it does not alter this conclusion.

## 7. Why an improved amplitude norm is still insufficient

Suppose, optimistically, that one had a matrix-valued extension of DFI that
used the Frobenius norm \(\|W\|_F\), with no Cauchy or nuclear-norm loss in
the numerator.  Equations (27) and the balanced DFI kernel would still give

\[
 X^{-1/2}\cdot X^{1/2}\cdot X^{47/48+\varepsilon}
 =X^{47/48+\varepsilon}.
 \tag{32}
\]

This would be a genuine power saving over \(O(X)\), but it still grows with
\(X\) and cannot be summed into \(O(1/\log N)\).  Therefore:

\[
 \boxed{\text{Sharpening only the }L^1/L^2\text{ norms of }\beta_q
 \text{ inside existing DFI/BC bounds cannot close H15.}}
 \tag{33}
\]

This is structurally expected.  An unconditional proof of the BCF target
would prove RH.  The published BCF result obtains its main term conditionally
from zeta-zero information; an arbitrary-coefficient Kloosterman estimate has
no mechanism that identifies the scalar and logarithmic terms that must
cancel the cotangent contribution.

## 8. The smallest new estimate actually needed

Let \(\mathcal D\) denote a compatible dyadic decomposition of the exact
centered identity (20) in `H15_BCF_CENTERED_ENERGY_DERIVATION.md`.  For each
block \(D\), let \(\mathfrak P_D\) be its complete modular-inverse part.  What
is needed is not \(|\mathfrak P_D|\ll\cdots\), but an explicit main term
\(\mathcal M_D\) satisfying both

\[
 \boxed{
 \sum_D\mathcal M_D
 =-C_N-\sum_{g\le N}\frac{\mu(g)^2}{g}\mathfrak L_{N,g}
 +\frac{\kappa}{\log N}
 +o\!\left(\frac1{\log N}\right),}
 \tag{34}
\]

and

\[
 \boxed{
 \sum_D(\mathfrak P_D-\mathcal M_D)
 =o\!\left(\frac1{\log N}\right).}
 \tag{35}
\]

For the BCF conditional benchmark,

\[
 \kappa=2+\gamma-\log(4\pi).
\]

Equations (34)--(35) are the smallest global analytic input: (35) deliberately
retains cross-block cancellation.  A more robust but stronger local theorem
could replace its left side by
\(\sum_D|\mathfrak P_D-\mathcal M_D|\).  Either version must use the
BCF/Möbius coefficients and preserve the centering.  A theorem for arbitrary
coefficient sequences is neither presently available nor plausibly the
minimal route.

An expert-facing formulation is:

> Can the primitive Estermann spectrum
> \(\widehat\beta_q(a)=\tfrac12-2D(0,a/q)\), evaluated at
> \(a=-\bar p_q\), be inserted into a Kuznetsov/Estermann reciprocity formula
> that produces the log-ratio and scalar pieces of the BCF Gram energy as its
> diagonal/polar main term, with the total off-diagonal error summable to
> \(o(1/\log N)\) for the exact Möbius logarithmic weights?

That is more precise than asking for a stronger DFI bound: it identifies the
missing main term and the required error scale.

## 9. Proof/heuristic audit

The following are proved by finite identities in this note:

1. oddness, zero modes, and the divisor formula (4);
2. the exact Fourier/Vasyunin/Estermann formulae (9)--(10);
3. conductor decomposition and orthogonality (12)--(16);
4. the exact \(L^1\) expression and triangle bounds (20)--(22);
5. the fixed-DFI exponent \(71/48\) and both Bettin--Chandee exponents
   \(15/8\), conditional only on inserting the stated standard coefficient
   norm bounds;
6. the fact that an ideal Frobenius-DFI bound still leaves \(47/48\).

The prime asymptotic (18) uses the published cotangent-moment theorem.  The
claims that \(\|\beta_p\|_1\asymp p^{3/2}\) and that padded dyadic matrices
have asymptotically linear nuclear norm are numerical heuristics only.  No
unproved heuristic is used in the obstruction (32)--(35).
