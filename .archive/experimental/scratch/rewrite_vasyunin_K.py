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
changed = 0
while i < len(lines):
    line = lines[i]

    # ONLY match axiom declarations — never touch def lines
    m = re.match(r"^axiom cot_pi_(\d+)_" + str(k) + r"_bounds\s*:", line)
    if m:
        a = int(m.group(1))
        # Consume the three-line axiom body:
        out.append(f"theorem cot_pi_{a}_{k}_bounds :\n")
        i += 1
        out.append(lines[i])   # lower bound line
        i += 1
        bound_up = lines[i]
        out.append(f"{bound_up.rstrip()} := by\n")

        g = math.gcd(a, k)
        acute = a <= k // 2

        if g > 1:
            a_prim = a // g
            k_prim = k // g
            out.append(f"  have hred : cotangentTermV {a} {k} = cotangentTermV {a_prim} {k_prim} :=\n")
            out.append(f"    cotangentTermV_gcd_reduce (g := {g}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n")
            out.append(f"  rw [hred]\n")
            out.append(f"  have hbase := cot_pi_{a_prim}_{k_prim}_bounds\n")
            out.append(f"  constructor\n")
            out.append(f"  · apply le_trans _ hbase.1; norm_num [cot_pi_{a}_{k}_lower, cot_pi_{a_prim}_{k_prim}_lower]\n")
            out.append(f"  · apply le_trans hbase.2 _; norm_num [cot_pi_{a}_{k}_upper, cot_pi_{a_prim}_{k_prim}_upper]\n")
        elif not acute:
            a_acute = k - a
            out.append(f"  have h0 : cotangentTermV {a} {k} = - cotangentTermV {a_acute} {k} :=\n")
            out.append(f"    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)\n")
            out.append(f"  rw [h0]\n")
            out.append(f"  have hbase := cot_pi_{a_acute}_{k}_bounds\n")
            out.append(f"  constructor\n")
            out.append(f"  · apply le_trans _ (neg_le_neg hbase.2); norm_num [cot_pi_{a}_{k}_lower, cot_pi_{a_acute}_{k}_upper]\n")
            out.append(f"  · apply le_trans (neg_le_neg hbase.1) _; norm_num [cot_pi_{a}_{k}_upper, cot_pi_{a_acute}_{k}_lower]\n")
        else:
            out.append(f"  have hbase := cot_pi_div_{a}_{k}_mem_interval_v2\n")
            out.append(f"  constructor\n")
            out.append(f"  · apply le_trans _ hbase.1; norm_num [cot_pi_{a}_{k}_lower]\n")
            out.append(f"  · apply le_trans hbase.2 _; norm_num [cot_pi_{a}_{k}_upper]\n")

        changed += 1
    else:
        out.append(line)
    i += 1

# Add import if not present
import_line = f"import RiemannHypothesis.Certificates.Generated.CotangentBoundsK{k}\n"
if import_line not in out:
    idx = 0
    for idx_line, ln in enumerate(out):
        if ln.startswith("import RiemannHypothesis.Certificates.Generated.CotangentBounds"):
            idx = idx_line
    out.insert(idx + 1, import_line)

with open("RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsCore.lean", "w") as f:
    f.writelines(out)

print(f"Replaced {changed} axioms for k={k} (def lines untouched).")
