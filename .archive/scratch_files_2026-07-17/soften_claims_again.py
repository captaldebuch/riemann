import os

filepath = 'doc/html/js/app.js'
with open(filepath, 'r') as f:
    content = f.read()

replacements = {
    "Classical Routes (H13 + H14) Complete + Functional Analysis (Phase NB) Complete + BCF Phase 7b Targets Formalized": "Classical Routes (H13 + H14) Modeled + Functional Analysis (Phase NB) Modeled + BCF Phase 7b Targets Modeled",
    
    "We present a complete formal verification in Lean 4 of two classical analytical approaches to the Riemann Hypothesis: (1) the Vasyunin–Báez-Duarte–Landreau–Saias (BBLS) chain proving RH-equivalent bounds via cotangent identities (H13); and (2) de la Vallée Poussin's quantitative method combining Fourier–Eisenstein interpolation, Borel–Jensen factorization, and Perron contour inversion (H14). Both are fully formalized with zero new axioms and zero sorries.": "We outline an exploratory formalization model in Lean 4 of two classical analytical approaches to the Riemann Hypothesis: (1) the Vasyunin–Báez-Duarte–Landreau–Saias (BBLS) chain proving RH-equivalent bounds via cotangent identities (H13); and (2) de la Vallée Poussin's quantitative method combining Fourier–Eisenstein interpolation, Borel–Jensen factorization, and Perron contour inversion (H14). Both are experimentally modeled, pending domain-expert validation.",
    
    "We formalize the Nyman–Beurling criterion in Lean 4, proving that the closure of unit fractions in L²(0,∞) is equivalent to the Riemann Hypothesis. This functional-analytic approach bridges classical harmonic analysis with RH, complementing the analytic methods of H13/H14. Our complete formalization includes Mellin transform techniques, Hardy space continuity, zero-detection via logarithmic pullback, and functional equation reflection.": "We outline an exploratory formalization model of the Nyman–Beurling criterion in Lean 4, exploring how the closure of unit fractions in L²(0,∞) is equivalent to the Riemann Hypothesis. This functional-analytic approach bridges classical harmonic analysis with RH, complementing the analytic methods of H13/H14. Our experimental model includes Mellin transform techniques, Hardy space continuity, zero-detection via logarithmic pullback, and functional equation reflection.",
    
    "We formalize a conditional approach to H15 (quadratic cancellation) using the Bettin–Conrey–Farmer asymptotic. The BCF main term emerges from residues at nontrivial zeros of ζ(s), proven via: (1) grid subdivision and multi-hole rectangle theorem; (2) Perron kernel inversion and contour deformation; (3) normalized limit analysis. Hypotheses: RH, zero simplicity, zeta-derivative moment bound. Phase 7b formalizes exact cancellation targets (energy-residue reduction via contour shift) and Hadamard endpoint identities (canonical ξ product + logarithmic-derivative evaluation).": "We outline a conditional, exploratory approach to H15 (quadratic cancellation) using the Bettin–Conrey–Farmer asymptotic. The BCF main term emerges from residues at nontrivial zeros of ζ(s), experimentally modeled via: (1) grid subdivision and multi-hole rectangle theorem; (2) Perron kernel inversion and contour deformation; (3) normalized limit analysis. Hypotheses: RH, zero simplicity, zeta-derivative moment bound. Phase 7b explores exact cancellation targets (energy-residue reduction via contour shift) and Hadamard endpoint identities (canonical ξ product + logarithmic-derivative evaluation).",
    
    "proven equivalent to residue interface": "experimentally modeled as equivalent to residue interface"
}

for old, new in replacements.items():
    content = content.replace(old, new)

with open(filepath, 'w') as f:
    f.write(content)
print("Updated app.js")

