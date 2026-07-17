import os

filepath = 'doc/html/js/app.js'
with open(filepath, 'r') as f:
    content = f.read()

target1 = "We present a complete formal verification in Lean 4 of two classical analytical approaches to the Riemann Hypothesis: (1) the Vasyunin–Báez-Duarte–Landreau–Saias (BBLS) chain proving RH-equivalent bounds via cotangent identities (H13); and (2) de la Vallée Poussin\'s quantitative method combining Fourier–Eisenstein interpolation, Borel–Jensen factorization, and Perron contour inversion (H14). Both are formalized with zero new axioms and zero sorries, establishing pure analytic routes to RH."

replacement1 = "We model an exploratory formalization in Lean 4 of two classical analytical approaches to the Riemann Hypothesis: (1) the Vasyunin–Báez-Duarte–Landreau–Saias (BBLS) chain (H13); and (2) de la Vallée Poussin\\'s quantitative method (H14). Both are experimentally modeled as analytic routes to RH, pending rigorous expert validation."

target2 = "We present a complete formal verification in Lean 4 of two classical analytical approaches to the Riemann Hypothesis: (1) the Vasyunin–Báez-Duarte–Landreau–Saias (BBLS) chain (H13) proving RH-equivalence via cotangent identities; and (2) de la Vallée Poussin\'s quantitative method (H14) combining Fourier–Eisenstein interpolation, Borel–Jensen factorization, and Perron contour inversion. Combined, these formalize 50% of RH."

replacement2 = "We model an exploratory formalization in Lean 4 of two classical analytical approaches to the Riemann Hypothesis: (1) the Vasyunin–Báez-Duarte–Landreau–Saias (BBLS) chain (H13); and (2) de la Vallée Poussin\\'s quantitative method (H14). Combined, these experimentally model foundational routes to RH, subject to domain-expert review."

content = content.replace(target1, replacement1)
content = content.replace(target2, replacement2)

with open(filepath, 'w') as f:
    f.write(content)
print("Replaced abstracts.")
