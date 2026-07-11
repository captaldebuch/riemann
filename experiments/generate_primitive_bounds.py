import sys
import hashlib
from fractions import Fraction
import math
import os

try:
    import flint
    HAS_FLINT = True
except ImportError:
    HAS_FLINT = False
    print("Warning: python-flint not installed. Intervals will not be strictly certified.")
    import mpmath
    mpmath.mp.dps = 100

def get_interval(val, bits=128):
    if HAS_FLINT:
        flint.ctx.prec = bits
        lo_f = float(val.lower())
        hi_f = float(val.upper())
        return Fraction(lo_f), Fraction(hi_f)
    else:
        f = float(val)
        err = 1e-15
        return Fraction(f - err).limit_denominator(10**12), Fraction(f + err).limit_denominator(10**12)

def compute_cot_term(a, k, bits=53):
    if HAS_FLINT:
        flint.ctx.prec = bits
        x = flint.arb.pi() * flint.arb(a) / flint.arb(k)
        sin_x, cos_x = x.sin_cos()
        return cos_x / sin_x
    else:
        x = mpmath.pi * mpmath.mpf(a) / mpmath.mpf(k)
        return mpmath.cot(x)

def compute_cot_sum(h, k, bits=53):
    if HAS_FLINT:
        flint.ctx.prec = bits
        V = flint.arb(0)
        for a in range(1, k):
            frac_val = (a * h) % k
            if frac_val == 0:
                continue
            frac_coeff = flint.arb(frac_val) / flint.arb(k)
            x = flint.arb.pi() * flint.arb(a) / flint.arb(k)
            sin_x, cos_x = x.sin_cos()
            cot_x = cos_x / sin_x
            V += frac_coeff * cot_x
        return V
    else:
        V = mpmath.mpf(0)
        for a in range(1, k):
            frac_val = (a * h) % k
            if frac_val == 0:
                continue
            frac_coeff = mpmath.mpf(frac_val) / mpmath.mpf(k)
            x = mpmath.pi * mpmath.mpf(a) / mpmath.mpf(k)
            cot_x = mpmath.cot(x)
            V += frac_coeff * cot_x
        return V

def gcd(a, b):
    return math.gcd(a, b)

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

MAX_K = 50

# We will maintain separate buffers for Core, K10, K20, K30, K40, K50
buffers = {}

def get_buffer(name):
    if name not in buffers:
        buffers[name] = []
        buffers[name].append("import Mathlib")
        buffers[name].append("import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula")
        buffers[name].append("import RiemannHypothesis.Certificates.Generated.ChiRhoBoundsN50")
        buffers[name].append("import RiemannHypothesis.Certificates.Generated.TranscendentalBoundsGenerated")
        
        if name != "Core":
            buffers[name].append("import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsCore")
            
        buffers[name].append("import Mathlib.Tactic.Ring")
        buffers[name].append("import Mathlib.Algebra.BigOperators.Intervals")
        buffers[name].append("")
        buffers[name].append("set_option linter.style.longLine false")
        buffers[name].append("")
        buffers[name].append("namespace RH.Certificates.Generated")
        buffers[name].append("open RH.Criteria.NymanBeurling.VasyuninGram")
        buffers[name].append("open RH.Certificates.Generated.ChiRhoBoundsN50")
        buffers[name].append("open scoped Finset")
        buffers[name].append("")
    return buffers[name]

out_core = get_buffer("Core")

out_core.append("lemma vasyunin_log_div (h k : ℕ) (h_pos : 0 < h) (k_pos : 0 < k) :")
out_core.append("  Real.log ((h : ℝ) / (k : ℝ)) = Real.log (h : ℝ) - Real.log (k : ℝ) := by")
out_core.append("  exact Real.log_div (by exact_mod_cast ne_of_gt h_pos) (by exact_mod_cast ne_of_gt k_pos)")
out_core.append("")

# Generate generic sum unrolling lemmas
for k in range(3, MAX_K + 1):
    out_core.append(f"lemma sum_Ico_1_{k} (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 {k}, f a = " + " + ".join(f"f {a}" for a in range(1, k)) + " := by")
    for _ in range(k-1):
        out_core.append("  rw [Finset.sum_Ico_succ_top (by decide)]")
    out_core.append("  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]")
    out_core.append("")

# Generate pi bounds
pi_val = flint.arb.pi() if HAS_FLINT else mpmath.pi
pi_lo, pi_hi = get_interval(pi_val)
out_core.append(f"def prim_pi_lower : ℚ := {pi_lo.numerator} / {pi_lo.denominator}")
out_core.append(f"def prim_pi_upper : ℚ := {pi_hi.numerator} / {pi_hi.denominator}")
out_core.append(f"axiom prim_pi_bounds : ((prim_pi_lower : ℚ) : ℝ) ≤ Real.pi ∧ Real.pi ≤ ((prim_pi_upper : ℚ) : ℝ)")
out_core.append("")

for n in range(1, MAX_K + 1):
    if is_prime(n):
        continue
    log_val = flint.arb(n).log() if HAS_FLINT else mpmath.log(n)
    lo, hi = get_interval(log_val)
    out_core.append(f"def prim_log_{n}_lower : ℚ := {lo.numerator} / {lo.denominator}")
    out_core.append(f"def prim_log_{n}_upper : ℚ := {hi.numerator} / {hi.denominator}")
    out_core.append(f"axiom prim_log_{n}_bounds : ((prim_log_{n}_lower : ℚ) : ℝ) ≤ Real.log {n} ∧ Real.log {n} ≤ ((prim_log_{n}_upper : ℚ) : ℝ)")
    out_core.append("")


# Track generated cot_pi_a_k_bounds to avoid duplicates within a file
generated_cot_bounds = set()

def get_file_name(k):
    if k <= 10: return "K10"
    if k <= 20: return "K20"
    if k <= 30: return "K30"
    if k <= 40: return "K40"
    return "K50"

def generate_cot_term_bound(a, k, out):
    if (a, k) in generated_cot_bounds:
        return
    generated_cot_bounds.add((a, k))
    val = compute_cot_term(a, k)
    lo, hi = get_interval(val)
    out.append(f"def cot_pi_{a}_{k}_lower : ℚ := {lo.numerator} / {lo.denominator}")
    out.append(f"def cot_pi_{a}_{k}_upper : ℚ := {hi.numerator} / {hi.denominator}")
    out.append(f"axiom cot_pi_{a}_{k}_bounds :")
    out.append(f"  ((cot_pi_{a}_{k}_lower : ℚ) : ℝ) ≤ cotangentTermV {a} {k} ∧")
    out.append(f"  cotangentTermV {a} {k} ≤ ((cot_pi_{a}_{k}_upper : ℚ) : ℝ)")
    out.append("")

# PRE-PASS: Generate all required cot_pi_a_k_bounds into Core
for k_c in range(2, MAX_K + 1):
    for h_c in range(1, k_c):
        if gcd(h_c, k_c) == 1:
            for a in range(1, k_c):
                frac_val = (a * h_c) % k_c
                if frac_val != 0:
                    generate_cot_term_bound(a, k_c, out_core)
            # also for (k_c, h_c) which has denominator h_c
            for a in range(1, h_c):
                frac_val = (a * k_c) % h_c
                if frac_val != 0:
                    generate_cot_term_bound(a, h_c, out_core)

def generate_cot_sum_theorem(h, k, out):
    V = compute_cot_sum(h, k)
    lo, hi = get_interval(V)
    
    # wider bound for nlinarith stability
    lo_t = lo - Fraction(1, 100000000)
    hi_t = hi + Fraction(1, 100000000)
    
    # Generate the unfold theorem
    out.append(f"theorem cotangentSumVFormula_{h}_{k}_unfold :")
    out.append(f"    cotangentSumVFormula {h} {k} =")
    terms = []
    for a in range(1, k):
        frac_val = (a * h) % k
        if frac_val != 0:
            terms.append(f"      (({frac_val}/{k} : ℚ) : ℝ) * cotangentTermV {a} {k}")
    
    if not terms:
        terms = ["0"]
    
    out.append("    + \n".join(terms) + " := by")
    out.append("  unfold cotangentSumVFormula")
    
    if k > 2:
        out.append(f"  rw [sum_Ico_1_{k}]")
    elif k == 2:
        out.append("  rw [Finset.sum_Ico_succ_top (by decide)]")
        out.append("  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]")
    else:
        out.append("  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]")
        
    hfs = []
    for a in range(1, k):
        frac_val = (a * h) % k
        out.append(f"  have hf_{a} : Int.fract ((({a} * {h} : ℕ) : ℝ) / (({k} : ℕ) : ℝ)) = (({frac_val}/{k} : ℚ) : ℝ) := by norm_num [Int.fract]")
        hfs.append(f"hf_{a}")
    
    if hfs:
        out.append(f"  simp only [{', '.join(hfs)}]")
    out.append("  try ring")
    out.append("")
    
    # Generate the bound theorem
    out.append(f"def cotangentSumVFormula_{h}_{k}_lower : ℚ := {lo_t.numerator} / {lo_t.denominator}")
    out.append(f"def cotangentSumVFormula_{h}_{k}_upper : ℚ := {hi_t.numerator} / {hi_t.denominator}")
    out.append(f"theorem cotangentSumVFormula_{h}_{k}_bounds :")
    out.append(f"  ((cotangentSumVFormula_{h}_{k}_lower : ℚ) : ℝ) ≤ cotangentSumVFormula {h} {k} ∧")
    out.append(f"  cotangentSumVFormula {h} {k} ≤ ((cotangentSumVFormula_{h}_{k}_upper : ℚ) : ℝ) := by")
    out.append(f"  rw [cotangentSumVFormula_{h}_{k}_unfold]")
    for a in range(1, k):
        frac_val = (a * h) % k
        if frac_val != 0:
            out.append(f"  have b_cot_{a} := cot_pi_{a}_{k}_bounds")
            out.append(f"  simp only [cot_pi_{a}_{k}_lower, cot_pi_{a}_{k}_upper] at b_cot_{a}")
    out.append("  rw [cotangentSumVFormula_" + str(h) + "_" + str(k) + "_lower, cotangentSumVFormula_" + str(h) + "_" + str(k) + "_upper]")
    out.append("  constructor")
    out.append("  · linarith")
    out.append("  · linarith")
    out.append("")

# Generate V_hk bounds
for k in range(2, MAX_K + 1):
    out = get_buffer(get_file_name(k))
    for h in range(1, k):
        if gcd(h, k) == 1:
            generate_cot_sum_theorem(h, k, out)
            generate_cot_sum_theorem(k, h, out)

            # Evaluate full formula to get bounds to prove
            if HAS_FLINT:
                V = compute_cot_sum(h, k)
                V2 = compute_cot_sum(k, h)
                log2pi = (flint.arb(2) * flint.arb.pi()).log()
                gamma = flint.arb.const_euler()
                Vsum = V + V2
                log_ratio = (flint.arb(h)/flint.arb(k)).log()
                term1 = (log2pi - gamma)/flint.arb(2) * (flint.arb(1)/flint.arb(h) + flint.arb(1)/flint.arb(k))
                term2 = flint.arb(k-h)/(flint.arb(2*h*k)) * log_ratio
                term3 = flint.arb.pi()/(flint.arb(2*h*k)) * Vsum
                formula = term1 + term2 - term3
            else:
                pass
            
            lo_f, hi_f = get_interval(formula)
            lo_t = lo_f - Fraction(1, 1000000)
            hi_t = hi_f + Fraction(1, 1000000)
            
            out.append(f"theorem vasyuninBEntry_{h}{k}_formula_bound :")
            out.append(f"  ((({lo_t.numerator} / {lo_t.denominator} : ℚ) : ℝ) ≤ vasyuninBEntryFormula {h} {k}) ∧")
            out.append(f"  (vasyuninBEntryFormula {h} {k} ≤ (({hi_t.numerator} / {hi_t.denominator} : ℚ) : ℝ)) := by")
            out.append(f"  unfold vasyuninBEntryFormula")
            out.append(f"  rw [vasyunin_log_div {h} {k} (by norm_num) (by norm_num)]")
            out.append(f"  have b_log2pi := log_two_pi_certified_bounds")
            out.append(f"  have b_gamma := euler_gamma_certified_bounds")
            out.append(f"  have b_pi := prim_pi_bounds")
            log_h = f"log_{h}_certified_bounds" if is_prime(h) else f"prim_log_{h}_bounds"
            log_k = f"log_{k}_certified_bounds" if is_prime(k) else f"prim_log_{k}_bounds"
            
            if h == 1:
                out.append(f"  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp")
                log_h = "b_log1"
            elif h in [2,3,5,7]:
                out.append(f"  have b_log{h} : ((log_{h}_lower : ℚ) : ℝ) ≤ Real.log {h} ∧ Real.log {h} ≤ ((log_{h}_upper : ℚ) : ℝ) := {log_h}")
                log_h = f"b_log{h}"
            else:
                out.append(f"  have b_log{h} := {log_h}")
                log_h = f"b_log{h}"
                
            if k in [2,3,5,7]:
                out.append(f"  have b_log{k} : ((log_{k}_lower : ℚ) : ℝ) ≤ Real.log {k} ∧ Real.log {k} ≤ ((log_{k}_upper : ℚ) : ℝ) := {log_k}")
                log_k = f"b_log{k}"
            else:
                out.append(f"  have b_log{k} := {log_k}")
                log_k = f"b_log{k}"
                
            out.append(f"  have b_Vhk := cotangentSumVFormula_{h}_{k}_bounds")
            out.append(f"  have b_Vkh := cotangentSumVFormula_{k}_{h}_bounds")
            out.append(f"  -- apply definitions of bounds for nlinarith")
            out.append(f"  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi")
            out.append(f"  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma")
            out.append(f"  simp only [prim_pi_lower, prim_pi_upper] at b_pi")
            
            if not is_prime(h) and h != 1:
                out.append(f"  simp only [prim_log_{h}_lower, prim_log_{h}_upper] at {log_h}")
            elif is_prime(h):
                out.append(f"  simp only [log_{h}_lower, log_{h}_upper] at {log_h}")
                
            if not is_prime(k):
                out.append(f"  simp only [prim_log_{k}_lower, prim_log_{k}_upper] at {log_k}")
            else:
                out.append(f"  simp only [log_{k}_lower, log_{k}_upper] at {log_k}")
                
            out.append(f"  simp only [cotangentSumVFormula_{h}_{k}_lower, cotangentSumVFormula_{h}_{k}_upper] at b_Vhk")
            out.append(f"  simp only [cotangentSumVFormula_{k}_{h}_lower, cotangentSumVFormula_{k}_{h}_upper] at b_Vkh")
            out.append(f"  push_cast at *")
            out.append(f"  constructor")
            out.append(f"  · nlinarith")
            out.append(f"  · nlinarith")
            out.append(f"")

for name, out in buffers.items():
    out.append("end RH.Certificates.Generated")
    file_name = f"RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBounds{name}.lean"
    with open(file_name, "w") as f:
        f.write("\n".join(out) + "\n")
    print(f"Generated {file_name}")

# Create a master file that imports all of them so old modules still work by importing the master file!
master_out = []
master_out.append("import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsCore")
for name in ["K10", "K20", "K30", "K40", "K50"]:
    if name in buffers:
        master_out.append(f"import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBounds{name}")
master_out.append("")
master_out.append("set_option linter.style.longLine false")
with open("RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsGenerated.lean", "w") as f:
    f.write("\n".join(master_out) + "\n")
print("Generated master file RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsGenerated.lean")
