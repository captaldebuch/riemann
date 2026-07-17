# Conditional BCF formalization

This directory formalizes the logarithmically tapered
Bettin--Conrey--Farmer approximation. The intended final asymptotic is
conditional on RH, simplicity of the nontrivial zeta zeros, and a reciprocal
zeta-derivative moment bound.

## Completed

- `Definitions.lean`
  - finite BCF weight, coefficients, and Dirichlet polynomial
  - finite approximation, approximation error, and Gram energy
  - nonnegativity and compatibility with the existing `bdApprox` API
- `MellinTransform.lean`
  - convergence of each generator Mellin transform on `0 < re s < 1`
  - convergence and evaluation of the finite BCF combination
  - exact theorem `bcfMellinTransform`
- `MellinPlancherel.lean`
  - critical-line and logarithmic-pullback definitions
  - weighted logarithmic change of variables
  - `L¹ ∩ L²` membership of the finite BCF pullback
  - exact reduction from Mellin to the pointwise Fourier transform
  - bridge to Mathlib's `L²` Fourier isometry
  - exact identification of the zeta-polynomial integrand
  - completed theorem `bcfMellinPlancherel`
- `ContourShift.lean` (Phase 4 local/finite layer)
  - exact Perron kernel and its shifted zero kernel
  - the set of distinct nontrivial zeta zeros and finite disk truncations
  - finite nontrivial- and trivial-zero residue sums
  - truncated vertical contours and rectangular boundary integrals
  - a Cauchy--Goursat theorem for pole-free BCF rectangles
  - a generic theorem converting a simple-pole residue limit into a small
    circle integral
  - the exact residue
    `N^(rho-s) / (zeta'(rho) * (rho-s)^2)` at a simple zeta zero
  - the corresponding BCF small-circle integral theorem
  - exact named propositions for the starting Perron representation and the
    global simple-zero Lemma 2 expansion
- `Perron.lean` (Phase 4 starting-line layer)
  - reciprocal-zeta identity `1 / zeta(z) = L(mu, z)` in `re z > 1`
  - exact substitution of that Möbius L-series into the `re w = 2` BCF
    Perron kernel
  - absolute convergence of the Möbius L-series at every point of that line
  - a pointwise rewrite of every truncated vertical integral; no unproved
    termwise or improper-integral interchange is hidden in this result
  - Cauchy-formula proof of the order-two residue
    `∮ N^w / w^2 dw = 2πi log N` around zero
  - left semicircular boundary-arc estimates for the elementary kernel:
    the centered auxiliary arc satisfies `‖A_R‖ ≤ pi / R`, and the arc which
    actually closes the initial line `re w = 2` satisfies
    `‖A_R‖ ≤ pi * N^2 * R / (R - 2)^2`; both tend to zero as `R → ∞`
  - upper and lower horizontal edges of the elementary Perron rectangle:
    for a rectangle from `re w = -a` to `re w = 2`, each is bounded by
    `(a + 2) * N^2 / T^2` and hence vanishes as `T → ∞`
  - exact transfer from a zero-free reciprocal-zeta contour bound to the full
    BCF horizontal kernel, and conditional vanishing of both full horizontal
    edges under an explicit `o(T^2)` reciprocal-zeta envelope
- `DeletedDiskAssembly.lean` (Phase 4 finite deleted-disk layer)
  - positive isolation disk around every eligible zeta zero, using zeta-zero
    discreteness
  - pairwise-disjoint closed disks for every finite disk truncation under
    simple-zero and `rho ≠ s` hypotheses
  - exact finite assembly: the sum of small-circle integrals is `2*pi*i`
    times `bcfTruncatedSimpleZeroResidueSum`
- `OuterBoundary.lean` (Phase 4 double-pole layer)
  - a positive closed disk about every regular `s ≠ 1` avoiding zeta zeros
  - holomorphy of the shifted-kernel numerator on that disk
  - Cauchy-formula evaluation of the order-two pole circle at `z = s`
  - exact identification of its Perron-normalized contribution with
    `bcfLemma2MainTerm`
  - annular Cauchy--Goursat deformation between pole-free inner and outer
    circles
  - exact normalized assembly of the `s` circle and all finite
    nontrivial-zero circles
  - a concrete `BCFOuterBoundaryDeformation` target against the project’s
    shifted Perron rectangle convention
- `FiniteDeletedRectangle.lean` (finite-hole Cauchy--Goursat foundation)
  - generic rectangle boundary integral and its pole-free Cauchy--Goursat law
  - exact vertical and horizontal grid-split identities, with internal-edge
    cancellation proved algebraically
  - `RectangleSubdivision`: a finite recursive grid datatype carrying its
    required edge-integrability facts
  - exact induction theorem equating the outer boundary integral with the
    finite sum over all leaf rectangles
  - finite-grid edge cancellation is complete; the remaining geometric input
    is an explicit rectangle-to-circle deformation for each deleted disk
  - a BCF deleted-disk family may be uniformly shrunk, preserving all local
    exclusions and the exact finite residue-boundary contribution; this
    supplies a positive local separation margin for a later cell-decomposition
    construction
- `FiniteAxisSeparation.lean` (finite center geometry)
  - proves that any finite set of distinct complex centers is separated by a
    finite family of vertical and horizontal lines that meet none of the
    centers
  - after the already-proved disk shrinking step, this provides the
    point-level geometry required for a disk-clear adaptive subdivision
- `RectangleDiskHomotopy.lean` (smooth-strip deformation assembly)
  - `SmoothCauchyStrip`, the exact `C²`-homotopy interface required by
    Mathlib's curve-integral Cauchy theorem
  - a proved one-strip Cauchy identity, including both transverse sides
  - a proved four-strip cyclic cancellation theorem for the shared radial
    sides
  - a proved limit-transfer theorem: stagewise smooth-strip equalities plus
    convergence of the two boundary sums imply the exact
    rectangle-boundary/circle-integral equality
  - the remaining local work is geometric: build the four strips in the
    rectangle-minus-disk region and prove the two convergence statements
- `FiniteDeletedRectangleAssembly.lean` (global finite assembly)
  - `FiniteDeletedRectangleCauchyGoursatWitness` records local exact cell
    comparisons and a finite disk-partition identity
  - `finite_deleted_rectangle_cauchy_goursat` proves that the outer
    rectangular integral equals the sum of all deleted-disk integrals
  - the theorem is fully proved once its witness is constructed; no annular
    shortcut or undeclared residue theorem is used
- `Asymptotic.lean` (Phase 7 target interface)
  - defines the normalized logarithmic BCF asymptotic and proves it is
    equivalent to convergence of its normalized error to zero
  - proves the Phase 6-to-7 limit algebra: the explicit residue-to-energy
    reduction plus `BCFZeroWeightFormula` yields the normalized asymptotic
  - proves the exact conversion to the published `epsilon / log N` bound
  - does not assert the normalized limit: its analytic proof remains
    contingent on the outstanding contour and zero-sum work
- `EnergyResidueReduction.lean` (Phase 7b.1 analytic target)
  - rewrites the remaining normalized energy-residue error exactly as the
    explicit critical-line integral error using the proved Mellin--Plancherel
    identity
  - makes the required critical-line decay estimate a named proposition
    without asserting it
  - proves that this residue-reduction interface follows from the direct BCF
    normalized energy asymptotic and the separate zero-weight formula; it is
    therefore not a substitute for the cancellation calculation in BCF's
    proof of Theorem 1
- `ZeroWeightFormula.lean` (Phase 7b.2 finite zero-weight calculus)
  - proves monotonicity and positivity for the finite distinct-zero weights
  - transports finite nontrivial-zero truncations through the completed-zeta
    functional equation and proves the critical-line reflection symmetry
  - reduces the remaining zero-weight limit to explicit boundedness and
    conditional-supremum identities; the Hadamard-product argument required
    for those identities is intentionally not asserted
- `HadamardPreparation.lean` (Phase 7b.2 multiplicity bridge)
  - defines an entire xi function from `completedRiemannZeta₀` and proves its
    functional equation
  - defines the finite multiplicity-weighted zero sum used by a canonical
    product and proves the exact reduction to the distinct-zero sum under the
    existing explicit zeta-simplicity hypothesis
  - keeps only the canonical-product evaluation itself as an explicit
    analytic target; no multiplicity ambiguity remains in the simple-zero
    conditional route
- `HadamardTarget.lean` (Phase 7b.2 exact product target)
  - states the natural complex multiplicity-weighted sum produced by a
    logarithmic derivative of the xi Hadamard product
  - proves that RH identifies its denominator `rho * (1 - rho)` with
    `|rho|^2`, and hence identifies every finite complex sum with the real
    multiplicity-weighted BCF sum
  - proves that the future canonical-product formula, followed by the
    existing explicit simplicity hypothesis, is sufficient for
    `BCFZeroWeightFormula`
- `HadamardEndpoint.lean` (Phase 7b.2 endpoint decomposition)
  - centers xi at `1/2`, proves its evenness, and proves the vanishing of the
    centered first derivative
  - proves the endpoint logarithmic-derivative symmetry of xi and the exact
    finite identity equating the endpoint kernel sum with the complex BCF
    zero-weight sum
  - separates the remaining classical calculation into a canonical-product
    endpoint formula and a gamma-factor special-value formula; their
    conjunction is proved sufficient for `BCFZeroWeightFormula`
- `XiSpecialValue.lean` (Phase 7b.2 special-value closure)
  - transports Mathlib's exact pole-removed completed-zeta value at `1` to
    `0` through the completed-zeta functional equation
  - differentiates the project's entire xi normalization at zero and proves
    `BCFXiLogDerivAtZeroFormula` with the exact constant
    `2 + gamma - log (4*pi)`
  - removes the special-value calculation as a hypothesis: under RH and
    simplicity, a future `BCFHadamardEndpointFormula` alone now implies the
    BCF zero-weight formula
- `CanonicalProductFinite.lean` (Phase 7b.2 finite product layer)
  - proves that the xi functional equation preserves analytic zero
    multiplicities
  - defines the finite multiplicity-aware canonical product over each height
    truncation
  - proves its endpoint logarithmic-derivative difference is exactly
    `bcfHadamardEndpointSumUpToHeight`
- `GenusOneProduct.lean` (Phase 7b.2 correct Hadamard-product layer)
  - defines the multiplicity-aware genus-one factor
    `((1 - s / rho) * exp (s / rho)) ^ m(rho)` and its finite height product
  - proves that the exponential correction has logarithmic derivative
    `rho⁻¹`, which cancels the `-rho⁻¹` contribution of the linear factor at
    `s = 0`
  - proves the finite genus-one product has exactly the same endpoint
    logarithmic-derivative difference
    `bcfHadamardEndpointSumUpToHeight`
  - records the honest infinite targets separately: summable genus-one factor
    deviations and a full xi factorization with the required
    `exp (A + B * s)` prefactor
  - proves that the summability target gives a genuine pointwise `Multipliable`
    product through Mathlib's infinite-product API, with nonzero endpoint
    values at `0` and `1`
  - formalizes the exact Weierstrass reduction required for the missing
    zero-counting work: a summable compact majorant for the genus-one
    deviations yields uniform product convergence on that compact and locally
    uniform product convergence on any open region admitting such majorants
  - proves the final formal handoff: the factorization plus justified
    endpoint logarithmic-derivative convergence imply
    `BCFHadamardEndpointFormula`
- `FinalAnalyticAssembly.lean` (Phase 7b complete formal assembly)
  - packages the three genuine Hadamard inputs: compact genus-one majorants,
    xi factorization with `exp (A + B * s)`, and height derivative convergence
  - proves that this package yields locally uniform product convergence and
    the BCF zero-weight formula under the existing conditional hypotheses
  - proves the final normalized and published BCF asymptotics once the
    independently named integrated critical-line cancellation estimate is
    supplied
- `MultiplicityZeroCounting.lean` (Phase 7b.2 zero-count foundation)
  - defines the correct analytic-multiplicity height count for the xi product
  - proves its monotonicity and proves it agrees with the established
    distinct-zero count under the existing zero-simplicity hypothesis
  - states the multiplicity-aware Riemann--von Mangoldt strength target and
    proves the existing distinct-zero target suffices under simplicity
- `HeightTruncationProduct.lean` (Phase 7b.2 product-limit bridge)
  - reindexes the finite BCF height products by the common subtype of all
    nontrivial zeros and proves those height `Finset`s are cofinal
  - proves pointwise multipliability implies convergence of the actual BCF
    height-truncated genus-one products to the infinite product; in particular
    the compact-majorant target already supplies this product convergence
- `ExactCancellationTarget.lean` (Phase 7b.1 exact analytic target)
  - states the required integrated cancellation of
    `|1 - zeta(1/2 + it) * V_N(1/2 + it)|^2`, rather than a pointwise zeta
    bound
  - proves it is exactly equivalent to `BCFCriticalLineResidueReduction`
    using the already proved Mellin--Plancherel identity
  - proves that this cancellation statement plus `BCFZeroWeightFormula`
    yields the normalized BCF asymptotic
- `BCFDeletedRectangleAssembly.lean` (BCF specialization)
  - proves translation compatibility between the Perron-coordinate rectangle
    and the shifted-zero-kernel rectangle
  - collects the main-pole disk and all finite nontrivial-zero disks into one
    finite deleted-hole index
  - proves a positive main-pole radius that is zero-free, avoids `1`, and is
    disjoint from every finite zero disk
  - specializes finite axis separation to the main-pole and truncated-zero
    centers: all selected cuts avoid every center, each center has positive
    cut clearance, and each pair of holes is separated by a selected cut
  - proves the zero disks can be uniformly shrunk clear of every selected
    cut, while the main disk can be chosen simultaneously zero-free,
    disjoint, and cut-clear
  - proves that a concrete BCF finite witness directly yields
    `BCFOuterBoundaryDeformation`
- `Hypotheses.lean` (Phase 5)
  - finite truncations of the distinct nontrivial zero set by `|im rho| ≤ T`
  - finite reciprocal-derivative moment and zero-weight sums
  - explicit critical-strip RH, nontrivial-zero simplicity, and
    `O(T^(3/2-delta))` reciprocal-derivative moment packages
  - a combined `BCFConditionalHypotheses` input for the final theorem
  - RH reduction of the finite zero weights to `1 / (1/4 + (im rho)^2)`
  - direct use of the simplicity package in the Phase 4 simple-pole theorem
- `Lemma3Finite.lean` (BCF Lemma 3 finite layer)
  - defines height-truncated simple-zero residue sums and their geometric
    kernel factor
  - proves the exact norm factorization at a simple zero away from the
    evaluation point
  - proves the finite Cauchy--Schwarz estimate separating the existing
    reciprocal-derivative moment from the geometric kernel square sum
- `Lemma3LimitAssembly.lean` (zero-counting and residue-limit interfaces)
  - defines the finite distinct-zero count and proves its height monotonicity
  - proves that the contour's disk truncation lies in the corresponding
    height truncation and transfers the reciprocal-derivative moment bound
    to that disk cutoff
  - proves the disk-truncated Cauchy--Schwarz residue bound, leaving exactly
    its geometric kernel square sum for the analytic estimate
  - exposes Mathlib's exact Abel partial-summation identity for a discretized
    zero-count shell
  - proves that a genuine Cauchy estimate for the disk-truncated nontrivial
    residues yields the limit data and closed-form Lemma 2 assembly
  - names, but does not assert, the missing Riemann--von Mangoldt/local
    kernel estimates (`BCFZeroCountingAsymptotic` and
    `BCFGeometricKernelSquareBound`)
- `Lemma2Assembly.lean` (global Phase 4 limit algebra)
  - a finite contour-shift witness containing an exact finite identity and
    its vanishing two-parameter error
  - a pair of independent nontrivial- and trivial-residue convergence data
  - proof that a finite witness implies `BCFLemma2SimpleZeroExpansion`
  - proof that residue limits uniquely determine the closed-form Lemma 2
    value

- `../FourierPlancherel.lean`
  - reusable almost-everywhere agreement between the pointwise Fourier
    integral and Mathlib's `L²` transform for `L¹ ∩ L²` functions
  - Plancherel stated directly as an equality of squared-norm integrals

All proved results above are unconditional except for hypotheses passed
explicitly to individual residue theorems (notably zero simplicity). They
contain no `sorry` and introduce no axioms. RH is not used in Phase 4's local
residue calculation.

## Remaining Phase 4 work

The local and finite contour layer is complete. The remaining global theorem
is analytically reduced to constructing `BCFContourShiftWitness` and
`BCFResidueLimitData`. Once those are constructed,
`Lemma2Assembly.lean` proves `BCFLemma2SimpleZeroExpansion` and its exact
closed-form limit. The outstanding inputs are:

- the inverse-Perron identity for the `1 / w^2` kernel (whose **closed**
  contour residue and elementary left-arc decay, including the shifted arc
  closing `re w = 2`, are proved) and its justified improper termwise
  interchange with the starting-line Möbius L-series (the starting-line
  reciprocal-zeta expansion itself is now proved in `Perron.lean`);
- an outer-boundary deformation for the deleted-disk rectangle.  The finite
  disks and their complete simple-zero residue sum are now constructed and
  proved.  The regular `z = s` disk and its normalized main-term contribution
  are also proved, as is the pole-free annular circle deformation.  The
  smooth-strip Cauchy assembly, its limit-transfer bridge, and the finite
  witness-driven grid assembly are now proved.  Still missing are the
  explicit strip geometry and convergence estimates in every
  rectangle-minus-disk component and construction of the finite witness for
  the BCF disks.  Once that witness exists,
  `BCFOuterBoundaryDeformation` follows directly from the proved adapter;
- estimates for the full BCF kernel on the horizontal and shifted-left edges:
  the full horizontal-edge API now isolates the exact needed input as
  `BCFHorizontalReciprocalZetaControl`.  The H14 DVP result controls only its
  narrow zero-free corridor near `re(s + w) = 1`; it does not bound the full
  segment after it crosses nontrivial zeta zeros, so no instance is asserted;
- convergence of the direct trivial-zero residue series;
- convergence of the disk-truncated nontrivial residue sum under the Phase 5
  hypotheses.

Mathlib supplies rectangle Cauchy--Goursat and circle Cauchy formulas, but not
a ready-made finite-pole residue theorem or the improper-contour estimates
above. Consequently the project does not yet construct the finite contour
witness for zeta itself.

BCF Lemma 2 sums over **distinct** zeros and takes the genuine residue at each
zero. It does not use a multiset repeating zeros by multiplicity. The final
conditional argument assumes simplicity, so `ContourShift.lean` gives the
relevant explicit reciprocal-derivative form.

The paper packages the trivial-zero series as `F_s(1/N)`. The Lean API keeps
the direct residue series as its primary definition, avoiding any unstated
branch convention in the displayed factor `z^s`.

## Remaining Phase 5 work

`BCFZeroWeightFormula` names the classical limit of the finite distinct-zero
weight sums to `2 + gamma - log(4*pi)`. Under RH and simplicity it is exactly
the leading constant required by BCF. It is not proved or assumed: completing
it needs a formal canonical Hadamard/product-formula argument for the entire
function `bcfXi`, including justified logarithmic differentiation. The exact
complex target is `BCFHadamardLogDerivativeFormula`; Mathlib does not yet
contain that theory. `HadamardTarget.lean` proves the full RH and
simple-zero reduction from that target to `BCFZeroWeightFormula`.
`HadamardEndpoint.lean` and `XiSpecialValue.lean` refine the missing analytic
work to a single statement: the canonical product must prove
`BCFHadamardEndpointFormula`.  The archimedean special value
`BCFXiLogDerivAtZeroFormula` is now proved from Mathlib's completed-zeta
endpoint evaluation and the functional equation.

`CanonicalProductFinite.lean` and `GenusOneProduct.lean` prove the exact
finite endpoint calculation in both plain and correct genus-one form. The
remaining analytic work is now exact: prove summability of the
multiplicity-weighted genus-one factor deviations (using a formal
zero-counting theorem), construct the required compact majorants (which now
give the locally uniform infinite product by a proved Mathlib bridge), justify
differentiating it, then identify `bcfXi` with
`exp (A + B * s)` times that product. The exponential prefactor cannot be
dropped from the global factorization, although its linear term cancels from
the endpoint difference. Mathlib does not yet contain this Hadamard
factorization/locally-uniform-product theory.

`FinalAnalyticAssembly.lean` proves every remaining implication once those
analytic inputs are established. The final unproved mathematical propositions
are therefore exactly: the multiplicity-weighted zero-counting majorants,
the xi Hadamard identification and logarithmic-derivative limit (the plain
height-product limit is now proved), and the separate integrated critical-line
cancellation estimate. None is stated as an axiom.

## Remaining Phase 7b.1 work

`BCFExactCriticalLineCancellation` is the exact remaining analytic theorem:
after the Mellin--Plancherel identity it compares the integrated numerator
`|1 - zeta(1/2 + it) * V_N(1/2 + it)|^2` with the finite zero-weight sum.
It cannot be replaced by a pointwise convexity, subconvexity, or van der
Corput bound for zeta alone, since the needed main term comes from the
cancellation and the Lemma 2--3 residue calculation. The formal result only
needs the following missing analytic inputs:

- the global BCF Lemma 2 contour expansion represented by
  `BCFContourShiftWitness` and `BCFResidueLimitData`;
- the BCF Lemma 3 estimate for its nontrivial-zero residue contribution,
  using the explicit RH, simplicity, and derivative-moment hypotheses.  Its
  finite Cauchy--Schwarz and disk-to-height layers are proved in
  `Lemma3Finite.lean` and `Lemma3LimitAssembly.lean`; the remaining work is
  the Riemann--von Mangoldt/local-zero-count input and its
  partial-summation bound for the geometric kernel.  Once that proves the
  required residue Cauchy estimate, the passage to the full residue sum is
  already formalized;
- the final contour/integral comparison giving the stated cancellation
  limit.

In the paper, the derivative moment condition is said to implicitly assume
simplicity. Lean's total inverse has `0⁻¹ = 0`, so the formal moment bound
would not imply that fact by itself. `BCFConditionalHypotheses` therefore
keeps simplicity as a separate explicit field.

## Mathematical conventions

The index `k : Fin N` represents the positive integer `k + 1`. This prevents
an invalid mathematical `n = 0` summand. The approximation error is

`chi01 + sum mu(n) w_N(n) rho_n`,

because the Mellin transform of `rho_n` is `-zeta(s) / (s n^s)`.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191.
