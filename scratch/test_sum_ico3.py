import sys

def generate_unfold(h, k):
    out = []
    out.append(f"theorem cotangentSumVFormula_{h}_{k}_unfold :")
    out.append(f"    cotangentSumVFormula {h} {k} =")
    terms = []
    for a in range(1, k):
        frac_val = (a * h) % k
        if frac_val != 0:
            terms.append(f"      ({frac_val}/{k} : ℝ) * cotTerm2 {a} {k}")
    
    if not terms:
        terms = ["0"]
    
    out.append("    + \n".join(terms) + " := by")
    out.append("  unfold cotangentSumVFormula")
    
    # Just use norm_num to expand sum and evaluate fractions!
    out.append("  norm_num [Int.fract]")
    
    return "\n".join(out)

print(generate_unfold(2, 3))
print(generate_unfold(3, 10))
