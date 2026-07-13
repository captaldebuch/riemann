# NB-MellinTools

Reusable Lean/mathlib infrastructure for the Mellin side of the
Nyman–Beurling criterion.  The package deliberately does not assert RH and
contains no axioms or `sorry` declarations.

Implemented foundations:

- the logarithmic pullback with mathlib's Mellin/Fourier normalization;
- the critical-line Mellin = Fourier identity;
- a named `L²(ℝ)` Fourier–Plancherel linear isometry;
- Cauchy–Schwarz continuity for integral evaluation on an `L²` region;
- exact `A/x` tails for the project’s Báez–Duarte generators and approximants.

Build with `lake build`.

Run `./verify.sh` to build the package and print the axiom dependencies of
every public theorem.  The expected dependencies are only Lean/mathlib's
standard classical and quotient principles; there is no `sorryAx` and no
project-specific analytic axiom.
