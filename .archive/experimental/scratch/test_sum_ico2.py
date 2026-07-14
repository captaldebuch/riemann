import sys

def generate_lemma(k):
    out = []
    out.append(f"lemma sum_Ico_1_{k} (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 {k}, f a = " + " + ".join(f"f {a}" for a in range(1, k)) + " := by")
    for _ in range(k-1):
        out.append("  rw [Finset.sum_Ico_succ_top (by decide)]")
    out.append("  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]")
    return "\n".join(out)

def generate_unfold(h, k):
    out = []
    out.append(f"theorem cotangentSumVFormula_{h}_{k}_unfold :")
    out.append(f"    cotangentSumVFormula {h} {k} =")
    terms = []
    for a in range(1, k):
        frac_val = (a * h) % k
        if frac_val != 0:
            terms.append(f"      ({frac_val}/{k} : ℝ) * cotangentTermV {a} {k}")
    
    if not terms:
        terms = ["0"]
    
    out.append("    + \n".join(terms) + " := by")
    
    # We DO NOT unfold cotangentTermV! Wait! 
    # If we don't unfold cotangentTermV, then BOTH SIDES have cotangentTermV!
    # Because cotangentSumVFormula is defined in terms of cotangentTermV now!
    out.append("  unfold cotangentSumVFormula")
    out.append(f"  rw [sum_Ico_1_{k}]")
    
    hfs = []
    for a in range(1, k):
        frac_val = (a * h) % k
        out.append(f"  have hf_{a} : Int.fract ((({a} * {h} : ℕ) : ℝ) / (({k} : ℕ) : ℝ)) = ({frac_val} : ℝ) / {k} := by norm_num [Int.fract]")
        hfs.append(f"hf_{a}")
    
    if hfs:
        out.append(f"  rw [{', '.join(hfs)}]")
    out.append("  ring")
    
    return "\n".join(out)

print(generate_lemma(3))
print("")
print(generate_unfold(2, 3))
