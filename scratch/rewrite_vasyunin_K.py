import re
import math
import sys

if len(sys.argv) < 2:
    print("Usage: python rewrite_vasyunin_K.py <k>")
    sys.exit(1)

k = int(sys.argv[1])

with open("RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsCore.lean", "r") as f:
    lines = f.readlines()

out = []
i = 0
while i < len(lines):
    line = lines[i]
    
    # Catch the definitions for obtuse angles and rewrite them!
    m_def_lower = re.match(r"^def cot_pi_(\d+)_" + str(k) + r"_lower\s*:\s*ℚ\s*:=", line)
    if m_def_lower:
        a = int(m_def_lower.group(1))
        if a > k // 2:
            a_acute = k - a
            out.append(f"def cot_pi_{a}_{k}_lower : ℚ := - cot_pi_{a_acute}_{k}_upper\n")
            i += 1
            continue
            
    m_def_upper = re.match(r"^def cot_pi_(\d+)_" + str(k) + r"_upper\s*:\s*ℚ\s*:=", line)
    if m_def_upper:
        a = int(m_def_upper.group(1))
        if a > k // 2:
            a_acute = k - a
            out.append(f"def cot_pi_{a}_{k}_upper : ℚ := - cot_pi_{a_acute}_{k}_lower\n")
            i += 1
            continue

    m = re.match(r"^(?:axiom|theorem) cot_pi_(\d+)_" + str(k) + r"_bounds\s*:", line)
    if m:
        a = int(m.group(1))
        # Consume the axiom
        out.append(f"theorem cot_pi_{a}_{k}_bounds :\n")
        i += 1
        out.append(lines[i]) # lower
        i += 1
        bound_up = lines[i]
        out.append(f"{bound_up.rstrip()} := by\n")
        
        # Determine the target
        acute = a <= k // 2
        a_acute = a if acute else k - a
        
        g = math.gcd(a_acute, k)
        a_prim = a_acute // g
        k_prim = k // g
        
        if g > 1:
            base_thm = f"cot_pi_{a_prim}_{k_prim}_bounds"
        else:
            base_thm = f"cot_pi_div_{a_prim}_{k_prim}_mem_interval_v2"
        
        if not acute:
            out.append(f"  have h0 : cotangentTermV {a} {k} = - cotangentTermV {a_acute} {k} :=\n")
            out.append(f"    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)\n")
            out.append(f"  rw [h0]\n")
            
        # ONLY apply reduction if it's acute!
        if acute and g > 1:
            out.append(f"  have hred : cotangentTermV {a_acute} {k} = cotangentTermV {a_prim} {k_prim} :=\n")
            out.append(f"    cotangentTermV_gcd_reduce (g := {g}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n")
            out.append(f"  rw [hred]\n")

        if not acute:
            # We don't even need the target theorem to be hbase, we can just use the acute bounds theorem
            out.append(f"  have hbase := cot_pi_{a_acute}_{k}_bounds\n")
            out.append(f"  constructor\n")
            out.append(f"  · apply le_trans _ (neg_le_neg hbase.2); norm_num [cot_pi_{a}_{k}_lower, cot_pi_{a_acute}_{k}_upper]\n")
            out.append(f"  · apply le_trans (neg_le_neg hbase.1) _; norm_num [cot_pi_{a}_{k}_upper, cot_pi_{a_acute}_{k}_lower]\n")
        else:
            out.append(f"  have hbase := {base_thm}\n")
            out.append(f"  constructor\n")
            if g > 1:
                out.append(f"  · apply le_trans _ hbase.1; norm_num [cot_pi_{a}_{k}_lower, cot_pi_{a_prim}_{k_prim}_lower]\n")
                out.append(f"  · apply le_trans hbase.2 _; norm_num [cot_pi_{a}_{k}_upper, cot_pi_{a_prim}_{k_prim}_upper]\n")
            else:
                out.append(f"  · apply le_trans _ hbase.1; norm_num [cot_pi_{a}_{k}_lower]\n")
                out.append(f"  · apply le_trans hbase.2 _; norm_num [cot_pi_{a}_{k}_upper]\n")
            
    else:
        out.append(line)
    i += 1

if f"import RiemannHypothesis.Certificates.Generated.CotangentBoundsK{k}\n" not in out:
    idx = 0
    for idx_line, line in enumerate(out):
        if line.startswith("import RiemannHypothesis.Certificates.Generated.CotangentBounds"):
            idx = idx_line
    out.insert(idx + 1, f"import RiemannHypothesis.Certificates.Generated.CotangentBoundsK{k}\n")

with open("RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsCore.lean", "w") as f:
    f.writelines(out)

print(f"Replacement done for K={k}.")
