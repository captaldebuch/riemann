import sys
import re
import math
from fractions import Fraction

if len(sys.argv) < 2:
    print("Usage: python generate_K_proofs.py <k>")
    sys.exit(1)

k = int(sys.argv[1])

# Extract bounds from VasyuninPrimitiveBoundsCore.lean
bounds = {}
with open("RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsCore.lean", "r") as f:
    content = f.read()
    
# Find all lower/upper bounds for k
for a in range(1, k):
    if math.gcd(a, k) != 1:
        continue
    # look for def cot_pi_{a}_{k}_lower : ℚ := ...
    lo_match = re.search(f"def cot_pi_{a}_{k}_lower : ℚ :=\s*([-\d\s/]+)", content)
    up_match = re.search(f"def cot_pi_{a}_{k}_upper : ℚ :=\s*([-\d\s/]+)", content)
    
    if lo_match and up_match:
        lo_str = lo_match.group(1).strip()
        up_str = up_match.group(1).strip()
        bounds[a] = {'lo_str': lo_str, 'up_str': up_str}

print(f"Found {len(bounds)} bounding definitions for k={k}")

def out_round(val, den, down=True):
    target = val * den
    if down:
        num = math.floor(target)
    else:
        num = math.ceil(target)
    return Fraction(num, den)
    
def gen_base_bound(yl, yu):
    c0l = Fraction(1) - yu**2 / 2 - yu**4 * Fraction(5, 96)
    c0u = Fraction(1) - yl**2 / 2 + yu**4 * Fraction(5, 96)
    s0l = yl - yu**3 / 6 - yu**4 * Fraction(5, 96)
    s0u = yu - yl**3 / 6 + yu**4 * Fraction(5, 96)
    return c0l, c0u, s0l, s0u
    
def gen_double(cl, cu, sl, su):
    c2l = 2 * cl**2 - 1
    c2u = 2 * cu**2 - 1
    s2l = 2 * cl * sl
    s2u = 2 * cu * su
    return c2l, c2u, s2l, s2u

def gen_proof(a, k, target_lo, target_up):
    # depth
    N = 32
    pi_lo = Fraction(314159265358979323846, 100000000000000000000)
    pi_up = Fraction(314159265358979323847, 100000000000000000000)
    
    Xl = pi_lo * a / k
    Xu = pi_up * a / k
    
    yl = Xl / (2**N)
    yu = Xu / (2**N)
    
    yl = out_round(yl, 2**100, True)
    yu = out_round(yu, 2**100, False)
    
    c0l, c0u, s0l, s0u = gen_base_bound(yl, yu)
    
    lines = []
    lines.append(f"theorem cot_pi_div_{a}_{k}_mem_interval_v2 :")
    lines.append(f"    ({target_lo} : ℝ) ≤ cotangentTermV {a} {k} ∧")
    lines.append(f"    cotangentTermV {a} {k} ≤ ({target_up} : ℝ) := by")
    lines.append(f"  have hcot : cotangentTermV {a} {k}")
    lines.append(f"      = Real.cos (Real.pi * {a} / {k}) / Real.sin (Real.pi * {a} / {k}) := by")
    lines.append(f"    unfold cotangentTermV")
    lines.append(f"    norm_num")
    lines.append(f"  set X : ℝ := Real.pi * {a} / {k} with hXdef")
    lines.append(f"  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20")
    lines.append(f"  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20")
    lines.append(f"  have hXl : ({Xl.numerator} : ℝ) / {Xl.denominator} ≤ X := by rw [hXdef]; nlinarith [hpl]")
    lines.append(f"  have hXu : X ≤ ({Xu.numerator} : ℝ) / {Xu.denominator} := by rw [hXdef]; nlinarith [hpu]")
    lines.append(f"  set y : ℝ := X / 2 ^ {N} with hydef")
    lines.append(f"  have hyl : ({yl.numerator} : ℝ) / {yl.denominator} ≤ y := by rw [hydef]; nlinarith [hXl]")
    lines.append(f"  have hyu : y ≤ ({yu.numerator} : ℝ) / {yu.denominator} := by rw [hydef]; nlinarith [hXu]")
    lines.append(f"  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl")
    lines.append(f"  have hXeq : (2 : ℝ) ^ {N} * y = X := by rw [hydef]; ring")
    
    lines.append(f"  have hbase := RH.Certificates.TrigIntervalDemo.cos_sin_base_bound (y := y) (yl := {yl.numerator} / {yl.denominator}) (yu := {yu.numerator} / {yu.denominator}) hy0 hyl hyu (by norm_num) (by norm_num)")
    lines.append(f"  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase")
    
    # level 0
    den = 2**250
    c0l_r = out_round(c0l, den, True)
    c0u_r = out_round(c0u, den, False)
    s0l_r = out_round(s0l, den, True)
    s0u_r = out_round(s0u, den, False)
    
    lines.append(f"  have c0l : ({c0l_r.numerator} : ℝ) / {c0l_r.denominator} ≤ Real.cos y := le_trans (by norm_num) hcb1")
    lines.append(f"  have c0u : Real.cos y ≤ ({c0u_r.numerator} : ℝ) / {c0u_r.denominator} := le_trans hcb2 (by norm_num)")
    lines.append(f"  have s0l : ({s0l_r.numerator} : ℝ) / {s0l_r.denominator} ≤ Real.sin y := le_trans (by norm_num) hsb1")
    lines.append(f"  have s0u : Real.sin y ≤ ({s0u_r.numerator} : ℝ) / {s0u_r.denominator} := le_trans hsb2 (by norm_num)")
    
    cl, cu, sl, su = c0l_r, c0u_r, s0l_r, s0u_r
    
    for i in range(1, N+1):
        lines.append(f"  -- Level {i}")
        if i == 1:
            lines.append(f"  have hd{i} := RH.Certificates.TrigIntervalDemo.cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c{i-1}l c{i-1}u s{i-1}l s{i-1}u")
        else:
            angle_str = "2 * (" * (i-1) + "y" + ")" * (i-1)
            lines.append(f"  have hd{i} := RH.Certificates.TrigIntervalDemo.cos_sin_double_bound (θ := {angle_str}) (by norm_num) (by norm_num) c{i-1}l c{i-1}u s{i-1}l s{i-1}u")
            
        lines.append(f"  obtain ⟨d{i}cl, d{i}cu, d{i}sl, d{i}su⟩ := hd{i}")
        
        cl2, cu2, sl2, su2 = gen_double(cl, cu, sl, su)
        # outward round to prevent denom explosion
        den = 2**(250 - i)
        cl = out_round(cl2, den, True)
        cu = out_round(cu2, den, False)
        sl = out_round(sl2, den, True)
        su = out_round(su2, den, False)
        
        angle_next = "2 * (" * i + "y" + ")" * i
        if i == N:
            # We replace angle_next with X
            lines.append(f"  have hangle : {angle_next} = X := by rw [← hXeq]; ring")
            lines.append(f"  rw [hangle] at d{i}cl d{i}cu d{i}sl d{i}su")
            var_c = "cX"
            var_s = "sX"
            func_angle = "X"
        else:
            var_c = f"c{i}"
            var_s = f"s{i}"
            func_angle = angle_next
            
        lines.append(f"  have {var_c}l : ({cl.numerator} : ℝ) / {cl.denominator} ≤ Real.cos ({func_angle}) := le_trans (by norm_num) d{i}cl")
        lines.append(f"  have {var_c}u : Real.cos ({func_angle}) ≤ ({cu.numerator} : ℝ) / {cu.denominator} := le_trans d{i}cu (by norm_num)")
        lines.append(f"  have {var_s}l : ({sl.numerator} : ℝ) / {sl.denominator} ≤ Real.sin ({func_angle}) := le_trans (by norm_num) d{i}sl")
        lines.append(f"  have {var_s}u : Real.sin ({func_angle}) ≤ ({su.numerator} : ℝ) / {su.denominator} := le_trans d{i}su (by norm_num)")

    lines.append(f"  have hsXpos : (0 : ℝ) < Real.sin X := lt_of_lt_of_le (by norm_num) sXl")
    lines.append(f"  rw [hcot]")
    lines.append(f"  constructor")
    
    target_lo_f = f"({target_lo})"
    lines.append(f"  · rw [le_div_iff₀ hsXpos]")
    lines.append(f"    have h1 : {target_lo_f} * Real.sin X ≤ {target_lo_f} * ({su.numerator} / {su.denominator}) := by apply mul_le_mul_of_nonneg_left sXu (by norm_num)")
    lines.append(f"    have h2 : {target_lo_f} * ({su.numerator} / {su.denominator} : ℝ) ≤ ({cl.numerator} / {cl.denominator}) := by norm_num")
    lines.append(f"    exact le_trans (le_trans h1 h2) cXl")
    
    target_up_f = f"({target_up})"
    lines.append(f"  · rw [div_le_iff₀ hsXpos]")
    lines.append(f"    have h1 : Real.cos X ≤ ({cu.numerator} / {cu.denominator} : ℝ) := cXu")
    lines.append(f"    have h2 : ({cu.numerator} / {cu.denominator} : ℝ) ≤ {target_up_f} * ({sl.numerator} / {sl.denominator}) := by norm_num")
    lines.append(f"    have h3 : {target_up_f} * ({sl.numerator} / {sl.denominator} : ℝ) ≤ {target_up_f} * Real.sin X := by apply mul_le_mul_of_nonneg_left sXl (by norm_num)")
    lines.append(f"    exact le_trans (le_trans h1 h2) h3")
    
    return "\n".join(lines)

out_file = f"RiemannHypothesis/Certificates/Generated/CotangentBoundsK{k}.lean"
with open(out_file, "w") as f:
    f.write("import Mathlib\n")
    f.write("import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula\n")
    f.write("import RiemannHypothesis.Certificates.Generated.CotangentBoundsCore\n")
    f.write("import RiemannHypothesis.Certificates.TrigIntervalDemo\n")
    f.write("import RiemannHypothesis.Certificates.TrigIntervalSweep\n\n")
    f.write(f"/-! # Cotangent bounds for k={k} -/\n\n")
    f.write("namespace RH.Certificates.Generated\n")
    f.write("open RH.Criteria.NymanBeurling.VasyuninGram\n\n")
    
    for a in sorted(bounds.keys()):
        if math.gcd(a, k) == 1 and 2*a <= k:
            lo_str = bounds[a]['lo_str']
            up_str = bounds[a]['up_str']
            proof = gen_proof(a, k, lo_str, up_str)
            f.write(proof + "\n\n")
            
    f.write("end RH.Certificates.Generated\n")
print(f"Done generating K={k}")
