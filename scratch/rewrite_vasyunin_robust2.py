import re
import math
import sys

k = 21

with open("RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsCore.lean", "r") as f:
    lines = f.readlines()

out = []
i = 0
while i < len(lines):
    line = lines[i]
    m = re.match(r"^theorem cot_pi_(\d+)_21_bounds\s*:", line)
    if m:
        a = int(m.group(1))
        # This time we match the already rewritten 'theorem'
        out.append(line)
        i += 1
        out.append(lines[i]) # lower
        i += 1
        out.append(lines[i]) # upper
        i += 1
        # Now we skip until we hit the next theorem or end
        while i < len(lines) and not lines[i].startswith("theorem cot_pi_") and not lines[i].startswith("end "):
            i += 1
        
        # Determine the target
        acute = a <= k // 2
        a_acute = a if acute else k - a
        
        g = math.gcd(a_acute, k)
        a_prim = a_acute // g
        k_prim = k // g
        
        base_thm = f"cot_pi_div_{a_prim}_{k_prim}_mem_interval_v2"
        
        if not acute:
            out.append(f"  have h0 : cotangentTermV {a} {k} = - cotangentTermV {a_acute} {k} :=\n")
            out.append(f"    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)\n")
            out.append(f"  rw [h0]\n")
            
        if g > 1:
            out.append(f"  have hred : cotangentTermV {a_acute} {k} = cotangentTermV {a_prim} {k_prim} :=\n")
            out.append(f"    cotangentTermV_gcd_reduce (g := {g}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n")
            out.append(f"  rw [hred]\n")

        out.append(f"  have hbase := {base_thm}\n")
        out.append(f"  constructor\n")
        if acute:
            out.append(f"  · apply le_trans _ hbase.1; norm_num [cot_pi_{a}_{k}_lower]\n")
            out.append(f"  · apply le_trans hbase.2 _; norm_num [cot_pi_{a}_{k}_upper]\n")
        else:
            out.append(f"  · apply le_trans _ (neg_le_neg hbase.2); norm_num [cot_pi_{a}_{k}_lower]\n")
            out.append(f"  · apply le_trans (neg_le_neg hbase.1) _; norm_num [cot_pi_{a}_{k}_upper]\n")
            
        continue
    else:
        out.append(line)
        i += 1

with open("RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsCore.lean", "w") as f:
    f.writelines(out)

print("Replacement done.")

