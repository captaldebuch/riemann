import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Certificates.TrigIntervalDemo

/-!
# A sweep of rational interval certificates for `cotangentTermV a k = cot(π a / k)`

This file extends the method of `RH.Certificates.TrigIntervalDemo` (angle doubling from a
Taylor base case) with a generic division/monotonicity lemma `cot_bound_of_sin_cos_bounds`,
and applies it to prove genuine, kernel-checked interval bounds for nine angles:
`π/3, π/4, π/6, π/10, π/12, π/24, π/47, π/49, π/50`.
-/

namespace RH.Certificates.TrigIntervalSweep

open Real
open RH.Certificates.TrigIntervalDemo (cos_sin_double_bound cos_sin_base_bound)

/-- Generic division step: from two-sided bounds on `sin x` (with a *positive* lower
bound) and `cos x` (with a *nonnegative* lower bound), derive a two-sided rational bound
on `cos x / sin x`. -/
theorem cot_bound_of_sin_cos_bounds
    {x sinLo sinHi cosLo cosHi lo hi : ℝ}
    (hsin_pos : 0 < sinLo)
    (hsin_lo : sinLo ≤ Real.sin x) (hsin_hi : Real.sin x ≤ sinHi)
    (hcos_nonneg : 0 ≤ cosLo)
    (hcos_lo : cosLo ≤ Real.cos x) (hcos_hi : Real.cos x ≤ cosHi)
    (hlo : lo ≤ cosLo / sinHi) (hhi : cosHi / sinLo ≤ hi) :
    lo ≤ Real.cos x / Real.sin x ∧ Real.cos x / Real.sin x ≤ hi := by
  have hsinx_pos : 0 < Real.sin x := lt_of_lt_of_le hsin_pos hsin_lo
  have hsinHi_pos : 0 < sinHi := lt_of_lt_of_le hsin_pos (le_trans hsin_lo hsin_hi)
  have hcoshi_nonneg : 0 ≤ cosHi := le_trans hcos_nonneg (le_trans hcos_lo hcos_hi)
  constructor
  · -- lo ≤ cosLo / sinHi ≤ cos x / sin x
    refine le_trans hlo ?_
    rw [div_le_div_iff₀ hsinHi_pos hsinx_pos]
    -- cosLo * sin x ≤ cos x * sinHi
    have h1 : cosLo * Real.sin x ≤ cosLo * sinHi :=
      mul_le_mul_of_nonneg_left hsin_hi hcos_nonneg
    have h2 : cosLo * sinHi ≤ Real.cos x * sinHi :=
      mul_le_mul_of_nonneg_right hcos_lo (le_of_lt hsinHi_pos)
    exact le_trans h1 h2
  · -- cos x / sin x ≤ cosHi / sinLo ≤ hi
    refine le_trans ?_ hhi
    rw [div_le_div_iff₀ hsinx_pos hsin_pos]
    -- cos x * sinLo ≤ cosHi * sin x
    have h1 : Real.cos x * sinLo ≤ cosHi * sinLo :=
      mul_le_mul_of_nonneg_right hcos_hi (le_of_lt hsin_pos)
    have h2 : cosHi * sinLo ≤ cosHi * Real.sin x :=
      mul_le_mul_of_nonneg_left hsin_lo hcoshi_nonneg
    exact le_trans h1 h2

/-- Certificate: `cot(π*1/3)` lies in a tiny explicit rational interval. -/
theorem cot_pi_div_1_3_mem_interval :
    (1443375409993266671409 : ℝ) / 2500000000000000000000 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 3 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 3 ≤
      (2886751515061123370911 : ℝ) / 5000000000000000000000 := by
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 3
      = Real.cos (Real.pi * 1 / 3) / Real.sin (Real.pi * 1 / 3) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi * 1 / 3 with hXdef
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (10471975511965977461533 : ℝ) / 10000000000000000000000 ≤ X :=
    by rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (10471975511965977461567 : ℝ) / 10000000000000000000000 :=
    by rw [hXdef]; nlinarith [hpu]
  set y : ℝ := X / 2 ^ 10 with hydef
  have hyl : (10471975511965977461533 : ℝ) / 10240000000000000000000000 ≤ y :=
    by rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (10471975511965977461567 : ℝ) / 10240000000000000000000000 :=
    by rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl
  have hXeq : (2 : ℝ) ^ 10 * y = X := by rw [hydef]; ring
  have hbase := cos_sin_base_bound (y := y)
    (yl := (10471975511965977461533 : ℝ) / 10240000000000000000000000)
    (yu := (10471975511965977461567 : ℝ) / 10240000000000000000000000)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  have c0l :
      (12499993463618572366972823525359 : ℝ) / 12500000000000000000000000000000 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u :
      Real.cos y ≤ (49999973854479986037605796718781 : ℝ) / 50000000000000000000000000000000 :=
    le_trans hcb2 (by norm_num)
  have s0l :
      (102265368028132952305687691349 : ℝ) / 100000000000000000000000000000000 ≤ Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u : Real.sin y ≤ (10226536803952609173502461791 : ℝ) / 10000000000000000000000000000000 :=
    le_trans hsb2 (by norm_num)
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l :
      (6249986927240562676519047528357 : ℝ) / 6250000000000000000000000000000 ≤
        Real.cos (2 * (y)) :=
    le_trans (by norm_num) d1cl
  have c1u :
      Real.cos (2 * (y)) ≤
        (49999895417947287679095207199683 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d1cu (by norm_num)
  have s1l :
      (204530629104993541548239364847 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (y)) :=
    le_trans (by norm_num) d1sl
  have s1u :
      Real.sin (2 * (y)) ≤ (51132657281950777740916270041 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d1su (by norm_num)
  have hd2 := cos_sin_double_bound (θ := 2 * (y)) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l :
      (12499895418033875517308303512819 : ℝ) / 12500000000000000000000000000000 ≤
        Real.cos (2 * (2 * (y))) :=
    le_trans (by norm_num) d2cl
  have c2u :
      Real.cos (2 * (2 * (y))) ≤
        (99999163344453293892723471062973 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d2cu (by norm_num)
  have s2l :
      (102265100650119822453083937519 : ℝ) / 25000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (y))) :=
    le_trans (by norm_num) d2sl
  have s2u :
      Real.sin (2 * (2 * (y))) ≤
        (409060402646284752804834371481 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d2su (by norm_num)
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * (y))) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l :
      (49998326695541936365548821182177 : ℝ) / 50000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3cl
  have c3u :
      Real.cos (2 * (2 * (2 * (y)))) ≤
        (4999832669590651282378789467051 : ℝ) / 5000000000000000000000000000000 :=
    le_trans d3cu (by norm_num)
  have s3l :
      (6544911682770974069859256143 : ℝ) / 800000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3sl
  have s3u :
      Real.sin (2 * (2 * (2 * (y)))) ≤
        (409056980219736634327418593459 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d3su (by norm_num)
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * (y))))
    (by norm_num) (by norm_num) c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l :
      (99986613788331315674441240312123 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4cl
  have c4u :
      Real.cos (2 * (2 * (2 * (2 * (y))))) ≤
        (99986613791247829732778401259561 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d4cu (by norm_num)
  have s4l :
      (818086581271630725145989405723 : ℝ) / 50000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4sl
  have s4u :
      Real.sin (2 * (2 * (2 * (2 * (y))))) ≤
        (1636173162741388842255293509051 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d4su (by norm_num)
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (y)))))
    (by norm_num) (by norm_num) c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l :
      (1249330734214231493427160961413 : ℝ) / 1250000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5cl
  have c5u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (3123326835900094189522214312393 : ℝ) / 3125000000000000000000000000000 :=
    le_trans d5cu (by norm_num)
  have s5l :
      (204494267617557150358879403791 : ℝ) / 6250000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5sl
  have s5u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (1635954141186277293392380435477 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d5su (by norm_num)
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (y))))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l :
      (99785892281890653939767998936643 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6cl
  have c6u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (49892946164261825516900199741931 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d6cu (by norm_num)
  have s6l :
      (654031292173425198832153493117 : ℝ) / 10000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6sl
  have s6u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (52322503387842472151144063221 : ℝ) / 800000000000000000000000000000 :=
    le_trans d6su (by norm_num)
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (y)))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l :
      (99144485969861695582969377449719 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7cl
  have c7u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (49572243077997152309367793134853 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d7cu (by norm_num)
  have s7l :
      (6526309606980316080858209182481 : ℝ) / 50000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7sl
  have s7u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (13052619223545157208223671623691 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d7su (by norm_num)
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l :
      (96592581964562052004645119102367 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8cl
  have c8u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (24148145675680731625190772073601 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d8cu (by norm_num)
  have s8l :
      (25881904450569341771970293674467 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8sl
  have s8u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (25881904518164759368571962301331 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d8su (by norm_num)
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l :
      (17320507562322552823798977014847 : ℝ) / 20000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (21650635165911841482146873835489 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d9cu (by norm_num)
  have s9l :
      (24999999770405825078550455179747 : ℝ) / 50000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (25000000026748076952371177825181 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d9su (by norm_num)
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  have hangle : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) = X := by
    rw [← hXeq]; ring
  rw [hangle] at d10cl d10cu d10sl d10su
  have cXl :
      (49999991108236370545806655115591 : ℝ) / 100000000000000000000000000000000 ≤ Real.cos X :=
    le_trans (by norm_num) d10cl
  have cXu :
      Real.cos X ≤ (50000000987973910957561954433113 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d10cu (by norm_num)
  have sXl :
      (86602537016275235520560115772363 : ℝ) / 100000000000000000000000000000000 ≤ Real.sin X :=
    le_trans (by norm_num) d10sl
  have sXu :
      Real.sin X ≤ (43301270378152711403135624381951 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d10su (by norm_num)
  rw [hcot]
  exact RH.Certificates.TrigIntervalSweep.cot_bound_of_sin_cos_bounds
    (x := X) (sinLo := (86602537016275235520560115772363 : ℝ) / 100000000000000000000000000000000)
    (sinHi := (43301270378152711403135624381951 : ℝ) / 50000000000000000000000000000000)
    (cosLo := (49999991108236370545806655115591 : ℝ) / 100000000000000000000000000000000)
    (cosHi := (50000000987973910957561954433113 : ℝ) / 100000000000000000000000000000000)
    (lo := (1443375409993266671409 : ℝ) / 2500000000000000000000)
    (hi := (2886751515061123370911 : ℝ) / 5000000000000000000000)
    (by norm_num) sXl sXu (by norm_num) cXl cXu (by norm_num) (by norm_num)

/-- Certificate: `cot(π*1/4)` lies in a tiny explicit rational interval. -/
theorem cot_pi_div_1_4_mem_interval :
    (1999999910692365539959 : ℝ) / 2000000000000000000000 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 4 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 4 ≤
      (10000000166717458928619 : ℝ) / 10000000000000000000000 := by
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 4
      = Real.cos (Real.pi * 1 / 4) / Real.sin (Real.pi * 1 / 4) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi * 1 / 4 with hXdef
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (157079632679489661923 : ℝ) / 200000000000000000000 ≤ X :=
    by rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (314159265358979323847 : ℝ) / 400000000000000000000 :=
    by rw [hXdef]; nlinarith [hpu]
  set y : ℝ := X / 2 ^ 10 with hydef
  have hyl : (157079632679489661923 : ℝ) / 204800000000000000000000 ≤ y :=
    by rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (314159265358979323847 : ℝ) / 409600000000000000000000 :=
    by rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl
  have hXeq : (2 : ℝ) ^ 10 * y = X := by rw [hydef]; ring
  have hbase := cos_sin_base_bound (y := y)
    (yl := (157079632679489661923 : ℝ) / 204800000000000000000000)
    (yu := (314159265358979323847 : ℝ) / 409600000000000000000000)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  have c0l :
      (49999985293142488770790442101347 : ℝ) / 50000000000000000000000000000000 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u : Real.cos y ≤ (1999999411725771648042066859401 : ℝ) / 2000000000000000000000000000000 :=
    le_trans hcb2 (by norm_num)
  have s0l : (76699031872467801241094729737 : ℝ) / 100000000000000000000000000000000 ≤ Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u : Real.sin y ≤ (9587378984509082720474681317 : ℝ) / 12500000000000000000000000000000 :=
    le_trans hsb2 (by norm_num)
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l :
      (49999941172578606749475992366177 : ℝ) / 50000000000000000000000000000000 ≤
        Real.cos (2 * (y)) :=
    le_trans (by norm_num) d1cl
  have c1u :
      Real.cos (2 * (y)) ≤
        (99999882345171632936800526457547 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d1cu (by norm_num)
  have s1l :
      (76699009312433141288862170237 : ℝ) / 50000000000000000000000000000000 ≤ Real.sin (2 * (y)) :=
    le_trans (by norm_num) d1sl
  have s1u :
      Real.sin (2 * (y)) ≤ (76699009316040765644362698541 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d1su (by norm_num)
  have hd2 := cos_sin_double_bound (θ := 2 * (y)) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l :
      (9999952938090570723643026448327 : ℝ) / 10000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (y))) :=
    le_trans (by norm_num) d2cl
  have c2u :
      Real.cos (2 * (2 * (y))) ≤
        (99999529380963384919963767816851 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d2cu (by norm_num)
  have s2l :
      (3067956762893372637674054863 : ℝ) / 1000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (y))) :=
    le_trans (by norm_num) d2sl
  have s2u :
      Real.sin (2 * (2 * (y))) ≤
        (153397838151905991237571819627 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d2su (by norm_num)
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * (y))) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l :
      (99998117528052475583979879692599 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3cl
  have c3u :
      Real.cos (2 * (2 * (2 * (y)))) ≤
        (24999529382070796308086298035887 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d3cu (by norm_num)
  have s3l :
      (613588464900608363059164881723 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3sl
  have s3u :
      Real.sin (2 * (2 * (2 * (y)))) ≤
        (153397116232477892377901746993 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d3su (by norm_num)
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * (y))))
    (by norm_num) (by norm_num) c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l :
      (399969880732335660000987491253 : ℝ) / 400000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4cl
  have c4u :
      Real.cos (2 * (2 * (2 * (2 * (y))))) ≤
        (99992470184006736221531544318967 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d4cu (by norm_num)
  have s4l :
      (613576914269883363409090407973 : ℝ) / 50000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4sl
  have s4u :
      Real.sin (2 * (2 * (2 * (2 * (y))))) ≤
        (153394228575150406506685309831 : ℝ) / 12500000000000000000000000000000 :=
    le_trans d4su (by norm_num)
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (y)))))
    (by norm_num) (by norm_num) c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l :
      (99969881866298515796183815531261 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5cl
  have c5u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (3998795274799580909373833258909 : ℝ) / 4000000000000000000000000000000 :=
    le_trans d5cu (by norm_num)
  have s5l :
      (306765356525799738687418292859 : ℝ) / 12500000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5sl
  have s5u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (2454122852351910579750488479833 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d5su (by norm_num)
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (y))))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l :
      (99879545607233616394307021124863 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6cl
  have c6u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (12484943202749149687201161094709 : ℝ) / 12500000000000000000000000000000 :=
    le_trans d6cu (by norm_num)
  have s6l :
      (613345929051142927247995755563 : ℝ) / 12500000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6sl
  have s6u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (39254139463049958372701998501 : ℝ) / 800000000000000000000000000000 :=
    le_trans d6su (by norm_num)
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (y)))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l :
      (24879618153537299985342582999109 : ℝ) / 25000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7cl
  have c7u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (24879618168279102525941232155399 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d7cu (by norm_num)
  have s7l :
      (392068561239518104972476755689 : ℝ) / 4000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7sl
  have s7u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (2450428508344863671358717143017 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d7su (by norm_num)
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l :
      (49039263914531642935545698414613 : ℝ) / 50000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8cl
  have c8u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (9807852806379635352779591676401 : ℝ) / 10000000000000000000000000000000 :=
    le_trans d8cu (by norm_num)
  have s8l :
      (1950903218729193051530534587797 : ℝ) / 10000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8sl
  have s8u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (19509032203611497789995832769471 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d8su (by norm_num)
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l :
      (46193976211163414233790441461369 : ℝ) / 50000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (2887123541975555559761022452933 : ℝ) / 3125000000000000000000000000000 :=
    le_trans d9cu (by norm_num)
  have s9l :
      (38268343125988059865772650895241 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (19134171624794171025647989291169 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d9su (by norm_num)
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  have hangle : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) = X := by
    rw [← hXeq]; ring
  rw [hangle] at d10cl d10cu d10sl d10su
  have cXl :
      (70710675055802513838202847573051 : ℝ) / 100000000000000000000000000000000 ≤ Real.cos X :=
    le_trans (by norm_num) d10cl
  have cXu :
      Real.cos X ≤ (35355339229485849868602052263583 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d10cu (by norm_num)
  have sXl :
      (35355338640050628105598174696479 : ℝ) / 50000000000000000000000000000000 ≤ Real.sin X :=
    le_trans (by norm_num) d10sl
  have sXu :
      Real.sin X ≤ (70710678213304214985879007566669 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d10su (by norm_num)
  rw [hcot]
  exact RH.Certificates.TrigIntervalSweep.cot_bound_of_sin_cos_bounds
    (x := X) (sinLo := (35355338640050628105598174696479 : ℝ) / 50000000000000000000000000000000)
    (sinHi := (70710678213304214985879007566669 : ℝ) / 100000000000000000000000000000000)
    (cosLo := (70710675055802513838202847573051 : ℝ) / 100000000000000000000000000000000)
    (cosHi := (35355339229485849868602052263583 : ℝ) / 50000000000000000000000000000000)
    (lo := (1999999910692365539959 : ℝ) / 2000000000000000000000)
    (hi := (10000000166717458928619 : ℝ) / 10000000000000000000000)
    (by norm_num) sXl sXu (by norm_num) cXl cXu (by norm_num) (by norm_num)

/-- Certificate: `cot(π*1/6)` lies in a tiny explicit rational interval. -/
theorem cot_pi_div_1_6_mem_interval :
    (3464101588566978268827 : ℝ) / 2000000000000000000000 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 6 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 6 ≤
      (8660254064797648430641 : ℝ) / 5000000000000000000000 := by
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 6
      = Real.cos (Real.pi * 1 / 6) / Real.sin (Real.pi * 1 / 6) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi * 1 / 6 with hXdef
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (2617993877991494365383 : ℝ) / 5000000000000000000000 ≤ X :=
    by rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (163624617374468397837 : ℝ) / 312500000000000000000 :=
    by rw [hXdef]; nlinarith [hpu]
  set y : ℝ := X / 2 ^ 10 with hydef
  have hyl : (2617993877991494365383 : ℝ) / 5120000000000000000000000 ≤ y :=
    by rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (163624617374468397837 : ℝ) / 320000000000000000000000 :=
    by rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl
  have hXeq : (2 : ℝ) ^ 10 * y = X := by rw [hydef]; ring
  have hbase := cos_sin_base_bound (y := y)
    (yl := (2617993877991494365383 : ℝ) / 5120000000000000000000000)
    (yu := (163624617374468397837 : ℝ) / 320000000000000000000000)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  have c0l : (4999999346361910642038355812857 : ℝ) / 5000000000000000000000000000000 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u :
      Real.cos y ≤ (99999986927238924911981429152969 : ℝ) / 100000000000000000000000000000000 :=
    le_trans hcb2 (by norm_num)
  have s0l : (204530762804054741553124731 : ℝ) / 400000000000000000000000000000 ≤ Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u : Real.sin y ≤ (5113269070172575660276976997 : ℝ) / 10000000000000000000000000000000 :=
    le_trans hsb2 (by norm_num)
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l :
      (99999947708956269305083341241769 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (y)) :=
    le_trans (by norm_num) d1cl
  have c1u :
      Real.cos (2 * (y)) ≤
        (99999947708959117589568243340819 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d1cu (by norm_num)
  have s1l :
      (102265368033117669359683279463 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (y)) :=
    le_trans (by norm_num) d1sl
  have s1u :
      Real.sin (2 * (y)) ≤ (51132684017271269902414443963 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d1su (by norm_num)
  have hd2 := cos_sin_double_bound (θ := 2 * (y)) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l :
      (99999790835879764285422273930029 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (y))) :=
    le_trans (by norm_num) d2cl
  have c2u :
      Real.cos (2 * (2 * (y))) ≤
        (49999895417945578708702145873093 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d2cu (by norm_num)
  have s2l :
      (204530629114978699612045667263 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (y))) :=
    le_trans (by norm_num) d2sl
  have s2u :
      Real.sin (2 * (2 * (y))) ≤
        (12783164319864641539337496303 : ℝ) / 6250000000000000000000000000000 :=
    le_trans d2su (by norm_num)
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * (y))) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l :
      (99999163344394049725568705010077 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3cl
  have c3u :
      Real.cos (2 * (2 * (2 * (y)))) ≤
        (99999163344439622158175401760849 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d3cu (by norm_num)
  have s3l :
      (3272483220964603179112827159 : ℝ) / 800000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3sl
  have s3u :
      Real.sin (2 * (2 * (2 * (y)))) ≤
        (40906040262633312036721514187 : ℝ) / 10000000000000000000000000000000 :=
    le_trans d3su (by norm_num)
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * (y))))
    (by norm_num) (by norm_num) c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l :
      (49998326695788025480817618863807 : ℝ) / 50000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4cl
  have c4u :
      Real.cos (2 * (2 * (2 * (2 * (y))))) ≤
        (49998326695879169583462408790139 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d4cu (by norm_num)
  have s4l :
      (818113960387570299163486464497 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4sl
  have s4u :
      Real.sin (2 * (2 * (2 * (2 * (y))))) ≤
        (51132122524966155395481309479 : ℝ) / 6250000000000000000000000000000 :=
    le_trans d4su (by norm_num)
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (y)))))
    (by norm_num) (by norm_num) c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l :
      (24996653447574990677868570229753 : ℝ) / 25000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5cl
  have c5u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (99986613791029091130743528563081 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d5cu (by norm_num)
  have s5l :
      (409043290658427232818529029449 : ℝ) / 25000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5sl
  have s5u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (818086581330233580205835130541 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d5su (by norm_num)
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (y))))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l :
      (49973229372506026756672502331627 : ℝ) / 50000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6cl
  have c6u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (99946458747928176779795884010253 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d6cu (by norm_num)
  have s6l :
      (1635954141063103050848837578359 : ℝ) / 50000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6sl
  have s6u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (1635954141101787501591141272407 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d6su (by norm_num)
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (y)))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l :
      (99785892313367927739470755526853 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7cl
  have c7u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (99785892325026175489468935215137 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d7cu (by norm_num)
  have s7l :
      (261612516909592093613468963217 : ℝ) / 4000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7sl
  have s7u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (6540312923085283052092831856803 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d7su (by norm_num)
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l :
      (99144486095501209710974480641041 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8cl
  have c8u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (12393060767754294486931008416941 : ℝ) / 12500000000000000000000000000000 :=
    le_trans d8cu (by norm_num)
  have s8l :
      (13052619220084851356016815017291 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8sl
  have s8u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (13052619222299305146406488905751 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d8su (by norm_num)
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l :
      (24148145615705163537330139704027 : ℝ) / 25000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (96592582647360848787285900119669 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d9cu (by norm_num)
  have s9l :
      (25881904495511487789870193806727 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (12940952256025047108854521693179 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d9su (by norm_num)
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  have hangle : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) = X := by
    rw [← hXeq]; ring
  rw [hangle] at d10cl d10cu d10sl d10su
  have cXl :
      (86602539736736163772534611013329 : ℝ) / 100000000000000000000000000000000 ≤ Real.cos X :=
    le_trans (by norm_num) d10cl
  have cXu :
      Real.cos X ≤ (86602540449744723184541925442023 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d10cu (by norm_num)
  have sXl :
      (12499999971387709927639513752739 : ℝ) / 25000000000000000000000000000000 ≤ Real.sin X :=
    le_trans (by norm_num) d10sl
  have sXu :
      Real.sin X ≤ (50000000013026007739680406545501 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d10su (by norm_num)
  rw [hcot]
  exact RH.Certificates.TrigIntervalSweep.cot_bound_of_sin_cos_bounds
    (x := X) (sinLo := (12499999971387709927639513752739 : ℝ) / 25000000000000000000000000000000)
    (sinHi := (50000000013026007739680406545501 : ℝ) / 100000000000000000000000000000000)
    (cosLo := (86602539736736163772534611013329 : ℝ) / 100000000000000000000000000000000)
    (cosHi := (86602540449744723184541925442023 : ℝ) / 100000000000000000000000000000000)
    (lo := (3464101588566978268827 : ℝ) / 2000000000000000000000)
    (hi := (8660254064797648430641 : ℝ) / 5000000000000000000000)
    (by norm_num) sXl sXu (by norm_num) cXl cXu (by norm_num) (by norm_num)

/-- Certificate: `cot(π*1/10)` lies in a tiny explicit rational interval. -/
theorem cot_pi_div_1_10_mem_interval :
    (30776835342985153088947 : ℝ) / 10000000000000000000000 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 10 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 10 ≤
      (1923552211492057906541 : ℝ) / 625000000000000000000 := by
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 10
      = Real.cos (Real.pi * 1 / 10) / Real.sin (Real.pi * 1 / 10) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi * 1 / 10 with hXdef
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (157079632679489661923 : ℝ) / 500000000000000000000 ≤ X :=
    by rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (314159265358979323847 : ℝ) / 1000000000000000000000 :=
    by rw [hXdef]; nlinarith [hpu]
  set y : ℝ := X / 2 ^ 10 with hydef
  have hyl : (157079632679489661923 : ℝ) / 512000000000000000000000 ≤ y :=
    by rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (314159265358979323847 : ℝ) / 1024000000000000000000000 :=
    by rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl
  have hXeq : (2 : ℝ) ^ 10 * y = X := by rw [hydef]; ring
  have hbase := cos_sin_base_bound (y := y)
    (yl := (157079632679489661923 : ℝ) / 512000000000000000000000)
    (yu := (314159265358979323847 : ℝ) / 1024000000000000000000000)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  have c0l :
      (99999995293805838653280050689013 : ℝ) / 100000000000000000000000000000000 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u :
      Real.cos y ≤ (49999997646902965468854712829313 : ℝ) / 50000000000000000000000000000000 :=
    le_trans hcb2 (by norm_num)
  have s0l : (30679615276385925260703454941 : ℝ) / 100000000000000000000000000000000 ≤ Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u : Real.sin y ≤ (30679615276478209690176050847 : ℝ) / 100000000000000000000000000000000 :=
    le_trans hsb2 (by norm_num)
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l :
      (49999990587611898789194944317593 : ℝ) / 50000000000000000000000000000000 ≤
        Real.cos (2 * (y)) :=
    le_trans (by norm_num) d1cl
  have c1u :
      Real.cos (2 * (y)) ≤
        (99999981175224166716090016176101 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d1cu (by norm_num)
  have s1l :
      (61359227665087324799585363921 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (y)) :=
    le_trans (by norm_num) d1sl
  have s1u :
      Real.sin (2 * (y)) ≤
        (61359227665271950274860171539 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d1su (by norm_num)
  have hd2 := cos_sin_double_bound (θ := 2 * (y)) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l :
      (99999924700902277757540979720279 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (y))) :=
    le_trans (by norm_num) d2cl
  have c2u :
      Real.cos (2 * (2 * (y))) ≤
        (49999962350451877154031766251477 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d2cu (by norm_num)
  have s2l :
      (122718432228700074625059348877 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (y))) :=
    le_trans (by norm_num) d2sl
  have s2u :
      Real.sin (2 * (2 * (y))) ≤
        (122718432229069778506181938261 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d2su (by norm_num)
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * (y))) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l :
      (312499058761632844101623735221 : ℝ) / 312500000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3cl
  have c3u :
      Real.cos (2 * (2 * (2 * (y)))) ≤
        (99999698803728416310162489561443 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d3cu (by norm_num)
  have s3l :
      (61359169911413933766152859091 : ℝ) / 25000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3sl
  have s3u :
      Real.sin (2 * (2 * (2 * (y)))) ≤
        (245436679646398766269393935499 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d3su (by norm_num)
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * (y))))
    (by norm_num) (by norm_num) c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l :
      (6249924701044026525097105442347 : ℝ) / 6250000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4cl
  have c4u :
      Real.cos (2 * (2 * (2 * (2 * (y))))) ≤
        (12499849402091006140121034396467 : ℝ) / 12500000000000000000000000000000 :=
    le_trans d4cu (by norm_num)
  have s4l :
      (490871880799026095138358559281 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4sl
  have s4u :
      Real.sin (2 * (2 * (2 * (2 * (y))))) ≤
        (490871880800541145022735045997 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d4su (by norm_num)
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (y)))))
    (by norm_num) (by norm_num) c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l :
      (12499397611980969174021843065833 : ℝ) / 12500000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5cl
  have c5u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (49997590447971125565663207765849 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d5cu (by norm_num)
  have s5l :
      (98173193371320710141704475063 : ℝ) / 10000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5sl
  have s5u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (196346386743293819777742069839 : ℝ) / 20000000000000000000000000000000 :=
    le_trans d5su (by norm_num)
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (y))))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l :
      (19996144809573262034541782394409 : ℝ) / 20000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6cl
  have c6u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (99980724048244282913537889639253 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d6cu (by norm_num)
  have s6l :
      (98168462302882559733807643433 : ℝ) / 5000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6sl
  have s6u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (981684623033015152092578474339 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d6su (by norm_num)
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (y)))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l :
      (24980725905677963474215938849923 : ℝ) / 25000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7cl
  have c7u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (19984580724844690685760824195883 : ℝ) / 20000000000000000000000000000000 :=
    le_trans d7cu (by norm_num)
  have s7l :
      (392598157588314706997079771171 : ℝ) / 10000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7sl
  have s7u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (1962990787957372029893213760319 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d7su (by norm_num)
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l :
      (19938346673575046942172124214829 : ℝ) / 20000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8cl
  have c8u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (49845866686958485642377429838351 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d8cu (by norm_num)
  have s8l :
      (1961477393157570547452757178847 : ℝ) / 25000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8sl
  have s8u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (3922954786406058843712256471139 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d8su (by norm_num)
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l :
      (98768834037830569750941735724929 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (49384417030961508707907982974487 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d9cu (by norm_num)
  have s9l :
      (7821723251431180253328496029041 : ℝ) / 50000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (15643446504172968801985477582323 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d9su (by norm_num)
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  have hangle : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) = X := by
    rw [← hXeq]; ring
  rw [hangle] at d10cl d10cu d10sl d10su
  have cXl :
      (11888206442981296322858808216639 : ℝ) / 12500000000000000000000000000000 ≤ Real.cos X :=
    le_trans (by norm_num) d10cl
  have cXu : Real.cos X ≤ (5944103227439605574597665395759 : ℝ) / 6250000000000000000000000000000 :=
    le_trans d10cu (by norm_num)
  have sXl :
      (3090169942841787007603640879507 : ℝ) / 10000000000000000000000000000000 ≤ Real.sin X :=
    le_trans (by norm_num) d10sl
  have sXu : Real.sin X ≤ (965678107454518545757356651693 : ℝ) / 3125000000000000000000000000000 :=
    le_trans d10su (by norm_num)
  rw [hcot]
  exact RH.Certificates.TrigIntervalSweep.cot_bound_of_sin_cos_bounds
    (x := X) (sinLo := (3090169942841787007603640879507 : ℝ) / 10000000000000000000000000000000)
    (sinHi := (965678107454518545757356651693 : ℝ) / 3125000000000000000000000000000)
    (cosLo := (11888206442981296322858808216639 : ℝ) / 12500000000000000000000000000000)
    (cosHi := (5944103227439605574597665395759 : ℝ) / 6250000000000000000000000000000)
    (lo := (30776835342985153088947 : ℝ) / 10000000000000000000000)
    (hi := (1923552211492057906541 : ℝ) / 625000000000000000000)
    (by norm_num) sXl sXu (by norm_num) cXl cXu (by norm_num) (by norm_num)

/-- Certificate: `cot(π*1/12)` lies in a tiny explicit rational interval. -/
theorem cot_pi_div_1_12_mem_interval :
    (18660254029515196653011 : ℝ) / 5000000000000000000000 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 12 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 12 ≤
      (2332531755172039619337 : ℝ) / 625000000000000000000 := by
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 12
      = Real.cos (Real.pi * 1 / 12) / Real.sin (Real.pi * 1 / 12) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi * 1 / 12 with hXdef
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (2617993877991494365383 : ℝ) / 10000000000000000000000 ≤ X :=
    by rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (163624617374468397837 : ℝ) / 625000000000000000000 :=
    by rw [hXdef]; nlinarith [hpu]
  set y : ℝ := X / 2 ^ 10 with hydef
  have hyl : (2617993877991494365383 : ℝ) / 10240000000000000000000000 ≤ y :=
    by rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (163624617374468397837 : ℝ) / 640000000000000000000000 :=
    by rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl
  have hXeq : (2 : ℝ) ^ 10 * y = X := by rw [hydef]; ring
  have hbase := cos_sin_base_bound (y := y)
    (yl := (2617993877991494365383 : ℝ) / 10240000000000000000000000)
    (yu := (163624617374468397837 : ℝ) / 640000000000000000000000)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  have c0l :
      (49999998365904809983434060444921 : ℝ) / 50000000000000000000000000000000 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u :
      Real.cos y ≤ (19999999346361932894263803092537 : ℝ) / 20000000000000000000000000000000 :=
    le_trans hcb2 (by norm_num)
  have s0l : (159789663663871739190249641 : ℝ) / 625000000000000000000000000000 ≤ Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u : Real.sin y ≤ (25566346186263982721422383561 : ℝ) / 100000000000000000000000000000000 :=
    le_trans hsb2 (by norm_num)
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l :
      (99999986927238693488839686381507 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (y)) :=
    le_trans (by norm_num) d1cl
  have c1u :
      Real.cos (2 * (y)) ≤
        (24999996731809717876659361678047 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d1cu (by norm_num)
  have s1l :
      (10226538140265044674578982851 : ℝ) / 20000000000000000000000000000000 ≤ Real.sin (2 * (y)) :=
    le_trans (by norm_num) d1sl
  have s1u :
      Real.sin (2 * (y)) ≤ (12783172675353563757068695973 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d1su (by norm_num)
  have hd2 := cos_sin_double_bound (θ := 2 * (y)) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l :
      (99999947708958191897122285833611 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (y))) :=
    le_trans (by norm_num) d2cl
  have c2u :
      Real.cos (2 * (2 * (y))) ≤
        (99999947708958903968220239789833 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d2cu (by norm_num)
  have s2l :
      (102265368033741236784042123589 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (y))) :=
    le_trans (by norm_num) d2sl
  have s2u :
      Real.sin (2 * (2 * (y))) ≤
        (6391585502119967632631494737 : ℝ) / 6250000000000000000000000000000 :=
    le_trans d2su (by norm_num)
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * (y))) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l :
      (19999958167177490929911335719187 : ℝ) / 20000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3cl
  have c3u :
      Real.cos (2 * (2 * (2 * (y)))) ≤
        (99999790835890302932459096848827 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d3cu (by norm_num)
  have s3l :
      (25566328639528720762534044323 : ℝ) / 12500000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3sl
  have s3u :
      Real.sin (2 * (2 * (2 * (y)))) ≤
        (204530629116587712994241222067 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d3su (by norm_num)
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * (y))))
    (by norm_num) (by norm_num) c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l :
      (99999163344424811117764394917933 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4cl
  have c4u :
      Real.cos (2 * (2 * (2 * (2 * (y))))) ≤
        (4999958167221810211277186273463 : ℝ) / 5000000000000000000000000000000 :=
    le_trans d4cu (by norm_num)
  have s4l :
      (409060402623108983432283195713 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4sl
  have s4u :
      Real.sin (2 * (2 * (2 * (2 * (y))))) ≤
        (204530201311918263472353357443 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d4su (by norm_num)
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (y)))))
    (by norm_num) (by norm_num) c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l :
      (99996653391699095500950367189943 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5cl
  have c5u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (99996653391744667550783406299121 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d5cu (by norm_num)
  have s5l :
      (409056980196444547102301534011 : ℝ) / 50000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5sl
  have s5u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (204528490098609344610122595881 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d5su (by norm_num)
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (y))))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l :
      (19997322758158424879491885969973 : ℝ) / 20000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6cl
  have c6u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (3999464551638976259852784696141 : ℝ) / 4000000000000000000000000000000 :=
    le_trans d6cu (by norm_num)
  have s6l :
      (1636173162646359454465139909861 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6sl
  have s6u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (1636173162650201581910341026951 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d6su (by norm_num)
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (y)))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l :
      (49973229373490218365054524002451 : ℝ) / 50000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7cl
  have c7u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (3997858349908378700915922201179 : ℝ) / 4000000000000000000000000000000 :=
    le_trans d7cu (by norm_num)
  have s7l :
      (3271908282167608996074431447663 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7sl
  have s7u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (3271908282181257123898129781681 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d7su (by norm_num)
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l :
      (19957178464247449003659101844753 : ℝ) / 20000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8cl
  have c8u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (2494647308103795171514418406973 : ℝ) / 2500000000000000000000000000000 :=
    le_trans d8cu (by norm_num)
  have s8l :
      (6540312922951371180819935231513 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8sl
  have s8u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (1635078230756589814871965314953 : ℝ) / 25000000000000000000000000000000 :=
    le_trans d8su (by norm_num)
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l :
      (99144486126911083574794300038393 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (19828897227708873948252529676233 : ℝ) / 20000000000000000000000000000000 :=
    le_trans d9cu (by norm_num)
  have s9l :
      (6526309610768219508276646309659 : ℝ) / 50000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (6526309611033668496530301880913 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d9su (by norm_num)
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  have hangle : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) = X := by
    rw [← hXeq]; ring
  rw [hangle] at d10cl d10cu d10sl d10su
  have cXl :
      (48296291293692643135584700002009 : ℝ) / 50000000000000000000000000000000 ≤ Real.cos X :=
    le_trans (by norm_num) d10cl
  have cXu : Real.cos X ≤ (1509259103648755209867943411407 : ℝ) / 1562500000000000000000000000000 :=
    le_trans d10cu (by norm_num)
  have sXl :
      (3235238063323681063652248042537 : ℝ) / 12500000000000000000000000000000 ≤ Real.sin X :=
    le_trans (by norm_num) d10sl
  have sXu : Real.sin X ≤ (1617619031917441108949735373613 : ℝ) / 6250000000000000000000000000000 :=
    le_trans d10su (by norm_num)
  rw [hcot]
  exact RH.Certificates.TrigIntervalSweep.cot_bound_of_sin_cos_bounds
    (x := X) (sinLo := (3235238063323681063652248042537 : ℝ) / 12500000000000000000000000000000)
    (sinHi := (1617619031917441108949735373613 : ℝ) / 6250000000000000000000000000000)
    (cosLo := (48296291293692643135584700002009 : ℝ) / 50000000000000000000000000000000)
    (cosHi := (1509259103648755209867943411407 : ℝ) / 1562500000000000000000000000000)
    (lo := (18660254029515196653011 : ℝ) / 5000000000000000000000)
    (hi := (2332531755172039619337 : ℝ) / 625000000000000000000)
    (by norm_num) sXl sXu (by norm_num) cXl cXu (by norm_num) (by norm_num)

/-- Certificate: `cot(π*1/24)` lies in a tiny explicit rational interval. -/
theorem cot_pi_div_1_24_mem_interval :
    (75957541125163972716761 : ℝ) / 10000000000000000000000 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 24 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 24 ≤
      (2373673160254623960037 : ℝ) / 312500000000000000000 := by
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 24
      = Real.cos (Real.pi * 1 / 24) / Real.sin (Real.pi * 1 / 24) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi * 1 / 24 with hXdef
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (1308996938995747182691 : ℝ) / 10000000000000000000000 ≤ X :=
    by rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (163624617374468397837 : ℝ) / 1250000000000000000000 :=
    by rw [hXdef]; nlinarith [hpu]
  set y : ℝ := X / 2 ^ 10 with hydef
  have hyl : (1308996938995747182691 : ℝ) / 10240000000000000000000000 ≤ y :=
    by rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (163624617374468397837 : ℝ) / 1280000000000000000000000 :=
    by rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl
  have hXeq : (2 : ℝ) ^ 10 * y = X := by rw [hydef]; ring
  have hbase := cos_sin_base_bound (y := y)
    (yl := (1308996938995747182691 : ℝ) / 10240000000000000000000000)
    (yu := (163624617374468397837 : ℝ) / 1280000000000000000000000)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  have c0l :
      (99999999182952409164009301586557 : ℝ) / 100000000000000000000000000000000 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u :
      Real.cos y ≤ (49999999591476205972768741251099 : ℝ) / 50000000000000000000000000000000 :=
    le_trans hcb2 (by norm_num)
  have s0l : (1597896649695510404202415559 : ℝ) / 12500000000000000000000000000000 ≤ Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u : Real.sin y ≤ (3195793299391716190462265499 : ℝ) / 25000000000000000000000000000000 :=
    le_trans hsb2 (by norm_num)
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l :
      (99999996731809650007372520164157 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (y)) :=
    le_trans (by norm_num) d1cl
  have c1u :
      Real.cos (2 * (y)) ≤
        (49999998365904830566742576460543 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d1cu (by norm_num)
  have s1l :
      (3195793273279868647632476203 : ℝ) / 12500000000000000000000000000000 ≤ Real.sin (2 * (y)) :=
    le_trans (by norm_num) d1sl
  have s1u :
      Real.sin (2 * (y)) ≤ (12783173093122256474304480833 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d1su (by norm_num)
  have hd2 := cos_sin_double_bound (θ := 2 * (y)) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l :
      (49999993463619406825426678177643 : ℝ) / 50000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (y))) :=
    le_trans (by norm_num) d2cl
  have c2u :
      Real.cos (2 * (2 * (y))) ≤
        (99999986927238858155302432892847 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d2cu (by norm_num)
  have s2l :
      (1022653814027283611067613143 : ℝ) / 2000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (y))) :=
    le_trans (by norm_num) d2sl
  have s2u :
      Real.sin (2 * (2 * (y))) ≤
        (51132690701375313777196237731 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d2su (by norm_num)
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * (y))) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l :
      (99999947708958672545114131756103 : ℝ) / 100000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3cl
  have c3u :
      Real.cos (2 * (2 * (2 * (y)))) ≤
        (99999947708958850562887166065007 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d3cu (by norm_num)
  have s3l :
      (102265368033819274018969631743 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3sl
  have s3u :
      Real.sin (2 * (2 * (2 * (y)))) ≤
        (12783171004230198247041817837 : ℝ) / 12500000000000000000000000000000 :=
    le_trans d3su (by norm_num)
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * (y))))
    (by norm_num) (by norm_num) c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l :
      (4999989541794468862025935946053 : ℝ) / 5000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4cl
  have c4u :
      Real.cos (2 * (2 * (2 * (2 * (y))))) ≤
        (1249997385448626116390481334603 : ℝ) / 1250000000000000000000000000000 :=
    le_trans d4cu (by norm_num)
  have s4l :
      (204530629116386823561390021397 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4sl
  have s4u :
      Real.sin (2 * (2 * (2 * (2 * (y))))) ≤
        (10226531455821590577692352599 : ℝ) / 5000000000000000000000000000000 :=
    le_trans d4su (by norm_num)
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (y)))))
    (by norm_num) (by norm_num) c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l :
      (19999832668886500293105414999569 : ℝ) / 20000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5cl
  have c5u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (99999163344435349742448640844509 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d5cu (by norm_num)
  have s5l :
      (204530201311715481136141415807 : ℝ) / 50000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5sl
  have s5u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) ≤
        (204530201311761925437222648069 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d5su (by norm_num)
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (y))))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l :
      (19999330678345971326926839092183 : ℝ) / 20000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6cl
  have c6u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (99996653391741249646999389241599 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d6cu (by norm_num)
  have s6l :
      (818113960393595962831936830553 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6sl
  have s6u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤
        (1022642450492256301035041021 : ℝ) / 125000000000000000000000000000 :=
    le_trans d6su (by norm_num)
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (y)))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l :
      (6249163361932197800898509287337 : ℝ) / 6250000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7cl
  have c7u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (99986613790960735338718950188019 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d7cu (by norm_num)
  have s7l :
      (327234632529655293333128917819 : ℝ) / 20000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7sl
  have s7u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤
        (1636173162648881024313131630309 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d7su (by norm_num)
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l :
      (12493307343434066564498218864569 : ℝ) / 12500000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8cl
  have c8u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (9994645874765479021269432047997 : ℝ) / 10000000000000000000000000000000 :=
    le_trans d8cu (by norm_num)
  have s8l :
      (327190828217546881580651721023 : ℝ) / 10000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8sl
  have s8u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤
        (1635954141089084497312770210343 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d8su (by norm_num)
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l :
      (24946473080801143566201976155103 : ℝ) / 25000000000000000000000000000000 ≤
        Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (49892946161966607359714132653677 : ℝ) / 50000000000000000000000000000000 :=
    le_trans d9cu (by norm_num)
  have s9l :
      (6540312922999284249340840088497 : ℝ) / 100000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤
        (6540312923016608324906795847907 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d9su (by norm_num)
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  have hangle : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) = X := by
    rw [← hXeq]; ring
  rw [hangle] at d10cl d10cu d10sl d10su
  have cXl :
      (99144486134763551748987975361863 : ℝ) / 100000000000000000000000000000000 ≤ Real.cos X :=
    le_trans (by norm_num) d10cl
  have cXu :
      Real.cos X ≤ (12393060767208984158360214914693 : ℝ) / 12500000000000000000000000000000 :=
    le_trans d10cu (by norm_num)
  have sXl :
      (13052619221889398960372623381487 : ℝ) / 100000000000000000000000000000000 ≤ Real.sin X :=
    le_trans (by norm_num) d10sl
  have sXu :
      Real.sin X ≤ (13052619222019283658784818627693 : ℝ) / 100000000000000000000000000000000 :=
    le_trans d10su (by norm_num)
  rw [hcot]
  exact RH.Certificates.TrigIntervalSweep.cot_bound_of_sin_cos_bounds
    (x := X) (sinLo := (13052619221889398960372623381487 : ℝ) / 100000000000000000000000000000000)
    (sinHi := (13052619222019283658784818627693 : ℝ) / 100000000000000000000000000000000)
    (cosLo := (99144486134763551748987975361863 : ℝ) / 100000000000000000000000000000000)
    (cosHi := (12393060767208984158360214914693 : ℝ) / 12500000000000000000000000000000)
    (lo := (75957541125163972716761 : ℝ) / 10000000000000000000000)
    (hi := (2373673160254623960037 : ℝ) / 312500000000000000000)
    (by norm_num) sXl sXu (by norm_num) cXl cXu (by norm_num) (by norm_num)

/-- Certificate: `cot(π*1/47)` lies in a tiny explicit rational interval. -/
theorem cot_pi_div_1_47_mem_interval :
    (14938277212283480448748358666983 : ℝ) / 1000000000000000000000000000000 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 47 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 47 ≤
      (14938277212283635028038453004527 : ℝ) / 1000000000000000000000000000000 := by
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 47
      = Real.cos (Real.pi * 1 / 47) / Real.sin (Real.pi * 1 / 47) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi * 1 / 47 with hXdef
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (13368479376977843567914893617 : ℝ) / 200000000000000000000000000000 ≤ X :=
    by rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (66842396884889217839787234043 : ℝ) / 1000000000000000000000000000000 :=
    by rw [hXdef]; nlinarith [hpu]
  set y : ℝ := X / 2 ^ 14 with hydef
  have hyl : (13368479376977843567914893617 : ℝ) / 3276800000000000000000000000000000 ≤ y :=
    by rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (66842396884889217839787234043 : ℝ) / 16384000000000000000000000000000000 :=
    by rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl
  have hXeq : (2 : ℝ) ^ 14 * y = X := by rw [hydef]; ring
  have hbase := cos_sin_base_bound (y := y)
    (yl := (13368479376977843567914893617 : ℝ) / 3276800000000000000000000000000000)
    (yu := (66842396884889217839787234043 : ℝ) / 16384000000000000000000000000000000)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  have c0l :
      (99999999999167787652215958729389516490987397 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u :
      Real.cos y ≤ (12499999999895973456527355558565915265187007 : ℝ) / 12500000000000000000000000000000000000000000 :=
    le_trans hcb2 (by norm_num)
  have s0l :
      (203986806899120465219212093172766602383 : ℝ) / 50000000000000000000000000000000000000000000 ≤
        Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u :
      Real.sin y ≤ (40797361379824093332546193920226724661 : ℝ) / 10000000000000000000000000000000000000000000 :=
    le_trans hsb2 (by norm_num)
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l :
      (49999999998335575304438843232697075242590133 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (y)) :=
    le_trans (by norm_num) d1cl
  have c1u :
      Real.cos (2 * (y)) ≤ (19999999999334230121777845884389055389061037 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d1cu (by norm_num)
  have s1l :
      (163189445517938289459477779259295088957 : ℝ) / 20000000000000000000000000000000000000000000 ≤
        Real.sin (2 * (y)) :=
    le_trans (by norm_num) d1sl
  have s1u :
      Real.sin (2 * (y)) ≤ (815947227589691453071487948070381550807 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d1su (by norm_num)
  have hd2 := cos_sin_double_bound (θ := 2 * (y)) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l :
      (12499999998335575304466546328369013736468589 : ℝ) / 12500000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (y))) :=
    le_trans (by norm_num) d2cl
  have c2u :
      Real.cos (2 * (2 * (y))) ≤ (99999999986684602435778542453155078741692913 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d2cu (by norm_num)
  have s2l :
      (815947227562529792979890054679753841603 : ℝ) / 50000000000000000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (y))) :=
    le_trans (by norm_num) d2sl
  have s2u :
      Real.sin (2 * (2 * (y))) ≤ (1631894455125059597508166581390819371029 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d2su (by norm_num)
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * (y))) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l :
      (99999999946738409746475478753698525908993749 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3cl
  have c3u :
      Real.cos (2 * (2 * (2 * (y)))) ≤ (19999999989347681949332033211697161891976833 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d3cu (by norm_num)
  have s3l :
      (652757781963106540572255769279206462859 : ℝ) / 20000000000000000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3sl
  have s3u :
      Real.sin (2 * (2 * (2 * (y)))) ≤ (3263788909815532725959558738326501003939 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d3su (by norm_num)
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * (y))))
    (by norm_num) (by norm_num) c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l :
      (49999999893476819521318927470740434572070289 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4cl
  have c4u :
      Real.cos (2 * (2 * (2 * (2 * (y))))) ≤ (49999999893476819521688302080118266882799301 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d4cu (by norm_num)
  have s4l :
      (6527577816154373653950709707564856483497 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4sl
  have s4u :
      Real.sin (2 * (2 * (2 * (2 * (y))))) ≤ (6527577816154373700159325074363740623457 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d4su (by norm_num)
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (y)))))
    (by norm_num) (by norm_num) c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l :
      (624999994673840981739540363183851894798671 : ℝ) / 625000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5cl
  have c5u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) ≤ (24999999786953639270320363744535862086247707 : ℝ) / 25000000000000000000000000000000000000000000 :=
    le_trans d5cu (by norm_num)
  have s5l :
      (2611031120899042663189506262369729331453 : ℝ) / 20000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5sl
  have s5u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) ≤ (6527577802247606704230603354397942490421 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d5su (by norm_num)
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (y))))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l :
      (99999996591258242837706414989843496690095129 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6cl
  have c6u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤ (99999996591258242849526402364023864782747617 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d6cu (by norm_num)
  have s6l :
      (26110310986482155407332621574440490609981 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6sl
  have s6u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤ (26110310986482155593131529670199398283517 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d6su (by norm_num)
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (y)))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l :
      (24999996591258300935308250099247942995288587 : ℝ) / 25000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7cl
  have c7u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤ (99999986365033203788512948282061863094570043 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d7cu (by norm_num)
  have s7l :
      (26110310096449081886181405093797329123837 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7sl
  have s7u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤ (52220620192898164150133084636225384986859 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d7su (by norm_num)
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l :
      (99999945460136533211322703169257308766319423 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8cl
  have c8u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤ (19999989092027306680088493784623378318733161 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d8cu (by norm_num)
  have s8l :
      (104441226145267879340594595369958477022283 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8sl
  have s8u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤ (52220613072633940072757402637221118539341 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d8su (by norm_num)
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l :
      (99999781840605624779430331681775882811950913 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤ (19999956368121125107181796422913218274863027 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d9cu (by norm_num)
  have s9l :
      (4177646767326629466859765756666538163807 : ℝ) / 2000000000000000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤ (104441169183165737673932917055153080927461 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d9su (by norm_num)
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  have c10l :
      (49999563681687184772402293566863172078375237 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) :=
    le_trans (by norm_num) d10cl
  have c10u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) ≤ (99999127363374372570712587547917741783414877 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d10cu (by norm_num)
  have s10l :
      (26110235333735892069405757105692964007801 : ℝ) / 6250000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) :=
    le_trans (by norm_num) d10sl
  have s10u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) ≤ (417763765339774280280539047119777500377473 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d10su (by norm_num)
  have hd11 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))
    (by norm_num) (by norm_num) c10l c10u s10l s10u
  obtain ⟨d11cl, d11cu, d11sl, d11su⟩ := hd11
  have c11l :
      (49998254734363685893526246400203407980118931 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) :=
    le_trans (by norm_num) d11cl
  have c11u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) ≤ (24999127367181845972644718432823651017289689 : ℝ) / 25000000000000000000000000000000000000000000 :=
    le_trans d11cu (by norm_num)
  have s11l :
      (835520239560298610742258973976377755607379 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) :=
    le_trans (by norm_num) d11sl
  have s11u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) ≤ (835520239560298650364522100418123338789843 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d11su (by norm_num)
  have hd12 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))
    (by norm_num) (by norm_num) c11l c11u s11l s11u
  obtain ⟨d12cl, d12cu, d12sl, d12su⟩ := hd12
  have c12l :
      (99986038118585658452120608439487278995447871 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) :=
    le_trans (by norm_num) d12cl
  have c12u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) ≤ (99986038118585706864536222669372567727024013 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d12cu (by norm_num)
  have s12l :
      (835491075465047620357630472908571319647247 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) :=
    le_trans (by norm_num) d12sl
  have s12u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) ≤ (208872768866261940276480796265666111877833 : ℝ) / 12500000000000000000000000000000000000000000 :=
    le_trans d12su (by norm_num)
  have hd13 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))
    (by norm_num) (by norm_num) c12l c12u s12l s12u
  obtain ⟨d13cl, d13cu, d13sl, d13su⟩ := hd13
  have c13l :
      (24986039093256321592800315312751977275189271 : ℝ) / 25000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) :=
    le_trans (by norm_num) d13cl
  have c13u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) ≤ (99944156373025479993826581939088147777759491 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d13cu (by norm_num)
  have s13l :
      (133659908030698205369249080801051359502133 : ℝ) / 4000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) :=
    le_trans (by norm_num) d13sl
  have s13u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) ≤ (1670748850383728657535720462754918648913339 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d13su (by norm_num)
  have hd14 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))))
    (by norm_num) (by norm_num) c13l c13u s13l s13u
  obtain ⟨d14cl, d14cu, d14sl, d14su⟩ := hd14
  have hangle : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) = X := by
    rw [← hXeq]; ring
  rw [hangle] at d14cl d14cu d14sl d14su
  have cXl :
      (99776687862314619304077795921033773400520679 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos X :=
    le_trans (by norm_num) d14cl
  have cXu :
      Real.cos X ≤ (49888343931157696681037746091587322077163811 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d14cu (by norm_num)
  have sXl :
      (1335852674902427969584388901167665059802983 : ℝ) / 20000000000000000000000000000000000000000000 ≤ Real.sin X :=
    le_trans (by norm_num) d14sl
  have sXu :
      Real.sin X ≤ (1669815843628039286739449570407808975026809 : ℝ) / 25000000000000000000000000000000000000000000 :=
    le_trans d14su (by norm_num)
  rw [hcot]
  exact RH.Certificates.TrigIntervalSweep.cot_bound_of_sin_cos_bounds
    (x := X) (sinLo := (1335852674902427969584388901167665059802983 : ℝ) / 20000000000000000000000000000000000000000000)
    (sinHi := (1669815843628039286739449570407808975026809 : ℝ) / 25000000000000000000000000000000000000000000)
    (cosLo := (99776687862314619304077795921033773400520679 : ℝ) / 100000000000000000000000000000000000000000000)
    (cosHi := (49888343931157696681037746091587322077163811 : ℝ) / 50000000000000000000000000000000000000000000)
    (lo := (14938277212283480448748358666983 : ℝ) / 1000000000000000000000000000000)
    (hi := (14938277212283635028038453004527 : ℝ) / 1000000000000000000000000000000)
    (by norm_num) sXl sXu (by norm_num) cXl cXu (by norm_num) (by norm_num)

/-- Certificate: `cot(π*1/49)` lies in a tiny explicit rational interval. -/
theorem cot_pi_div_1_49_mem_interval :
    (623032287418861373931236352453 : ℝ) / 40000000000000000000000000000 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 49 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 49 ≤
      (1557580718547167076879709756321 : ℝ) / 100000000000000000000000000000 := by
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 49
      = Real.cos (Real.pi * 1 / 49) / Real.sin (Real.pi * 1 / 49) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi * 1 / 49 with hXdef
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (64114135787546800784897959183 : ℝ) / 1000000000000000000000000000000 ≤ X :=
    by rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (64114135787546800785102040817 : ℝ) / 1000000000000000000000000000000 :=
    by rw [hXdef]; nlinarith [hpu]
  set y : ℝ := X / 2 ^ 14 with hydef
  have hyl : (64114135787546800784897959183 : ℝ) / 16384000000000000000000000000000000 ≤ y :=
    by rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (64114135787546800785102040817 : ℝ) / 16384000000000000000000000000000000 :=
    by rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl
  have hXeq : (2 : ℝ) ^ 14 * y = X := by rw [hydef]; ring
  have hbase := cos_sin_base_bound (y := y)
    (yl := (64114135787546800784897959183 : ℝ) / 16384000000000000000000000000000000)
    (yu := (64114135787546800785102040817 : ℝ) / 16384000000000000000000000000000000)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  have c0l :
      (99999999999234336911180886176981317856879023 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u :
      Real.cos y ≤ (49999999999617168455591664421754717267935889 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans hcb2 (by norm_num)
  have s0l :
      (391321629561664842696013029258530526799 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u :
      Real.sin y ≤ (97830407390416211284981291985687735679 : ℝ) / 25000000000000000000000000000000000000000000 :=
    le_trans hsb2 (by norm_num)
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l :
      (99999999996937347644735269507236871951175749 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (y)) :=
    le_trans (by norm_num) d1cl
  have c1u :
      Real.cos (2 * (y)) ≤ (19999999999387469528949008034669852771352563 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d1cu (by norm_num)
  have s1l :
      (782643259117337274839787791599064665367 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (y)) :=
    le_trans (by norm_num) d1sl
  have s1u :
      Real.sin (2 * (y)) ≤ (31305730364693491189105247451800255917 : ℝ) / 4000000000000000000000000000000000000000000 :=
    le_trans d1su (by norm_num)
  have hd2 := cos_sin_double_bound (θ := 2 * (y)) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l :
      (99999999987749390579128674817931659823888449 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (y))) :=
    le_trans (by norm_num) d2cl
  have c2u :
      Real.cos (2 * (2 * (y))) ≤ (99999999987749390579167757482380030480093451 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d2cu (by norm_num)
  have s2l :
      (782643259093367632631110013981452350033 : ℝ) / 50000000000000000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (y))) :=
    le_trans (by norm_num) d2sl
  have s2u :
      Real.sin (2 * (2 * (y))) ≤ (1565286518186735275038059755974791857977 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d2su (by norm_num)
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * (y))) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l :
      (19999999990199512463903249579076292920580433 : ℝ) / 20000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3cl
  have c3u :
      Real.cos (2 * (2 * (2 * (y)))) ≤ (49999999975498781159836289276577897884715423 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d3cu (by norm_num)
  have s3l :
      (782643258997489063800803544380873715953 : ℝ) / 25000000000000000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3sl
  have s3u :
      Real.sin (2 * (2 * (2 * (y)))) ≤ (3130573035989956274756117142507186306403 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d3su (by norm_num)
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * (y))))
    (by norm_num) (by norm_num) c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l :
      (19999999960798049865217953910823947070795777 : ℝ) / 20000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4cl
  have c4u :
      Real.cos (2 * (2 * (2 * (2 * (y))))) ≤ (99999999803990249326715092184910636687488671 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d4cu (by norm_num)
  have s4l :
      (3130573034455899154200207679560056286141 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4sl
  have s4u :
      Real.sin (2 * (2 * (2 * (2 * (y))))) ≤ (1565286517227949586879002340190808793199 : ℝ) / 25000000000000000000000000000000000000000000 :=
    le_trans d4su (by norm_num)
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (y)))))
    (by norm_num) (by norm_num) c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l :
      (49999999607980499036377762700723991092295341 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5cl
  have c5u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) ≤ (2499999980399024951881420397992720355013863 : ℝ) / 2500000000000000000000000000000000000000000 :=
    le_trans d5cu (by norm_num)
  have s5l :
      (12522292113278683018794135745527112577387 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5sl
  have s5u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) ≤ (2504458422655736619420725664420832387811 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d5su (by norm_num)
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (y))))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l :
      (19999999372768800917073046493437045562950609 : ℝ) / 20000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6cl
  have c6u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤ (19999999372768800919074078892356836604008283 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d6cu (by norm_num)
  have s6l :
      (5008916806039611566171959738220035119623 : ℝ) / 20000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6sl
  have s6u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤ (12522292015099028994052610213448536815229 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d6su (by norm_num)
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (y)))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l :
      (99999987455376215050949481371913892036188269 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7cl
  have c7u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤ (19999997491075243018194025619039952376219491 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d7cu (by norm_num)
  have s7l :
      (6261145811190208560286811220462867207873 : ℝ) / 12500000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7sl
  have s7u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤ (10017833297904333760359365155712568400823 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d7su (by norm_num)
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l :
      (24999987455377001888879010919124258533913107 : ℝ) / 25000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8cl
  have c8u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤ (3124998431922125241112456577746320080884813 : ℝ) / 3125000000000000000000000000000000000000000 :=
    le_trans d8cu (by norm_num)
  have s8l :
      (100178320412048350710059806309731278150101 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8sl
  have s8u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤ (100178320412048351389156414913538927868983 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d8su (by norm_num)
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l :
      (99999799286082387843236891009935138548782821 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤ (99999799286082388483566836947404097869886161 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d9cu (by norm_num)
  have s9l :
      (100178270144077864585000180148388383055987 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤ (200356540288155730848928949391799023030643 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d9su (by norm_num)
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  have c10l :
      (19999839429027054581482391419380226400165969 : ℝ) / 20000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) :=
    le_trans (by norm_num) d10cl
  have c10u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) ≤ (3999967885805411018749063996859857515525411 : ℝ) / 4000000000000000000000000000000000000000000 :=
    le_trans d10cu (by norm_num)
  have s10l :
      (400712276289389049266875156287514799993921 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) :=
    le_trans (by norm_num) d10sl
  have s10u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) ≤ (400712276289389055190611447009530759634271 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d10su (by norm_num)
  have hd11 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))
    (by norm_num) (by norm_num) c10l c10u s10l s10u
  obtain ⟨d11cl, d11cu, d11sl, d11su⟩ := hd11
  have c11l :
      (24999197148358152576491747788430380094832939 : ℝ) / 25000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) :=
    le_trans (by norm_num) d11cl
  have c11u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) ≤ (124995985741790775688929134869074170822379 : ℝ) / 125000000000000000000000000000000000000000 :=
    le_trans d11cu (by norm_num)
  have s11l :
      (801418118302770602477833911353579924630687 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) :=
    le_trans (by norm_num) d11sl
  have s11u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) ≤ (200354529575692658713053947794846519680701 : ℝ) / 25000000000000000000000000000000000000000000 :=
    le_trans d11su (by norm_num)
  have hd12 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))
    (by norm_num) (by norm_num) c11l c11u s11l s11u
  obtain ⟨d12cl, d12cu, d12sl, d12su⟩ := hd12
  have c12l :
      (99987154579993084045341113466936258616699603 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) :=
    le_trans (by norm_num) d12cl
  have c12u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) ≤ (99987154579993125024730323372783657777235259 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d12cu (by norm_num)
  have s12l :
      (1602784763017374352790353030114082594677187 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) :=
    le_trans (by norm_num) d12sl
  have s12u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) ≤ (1602784763017374581750435952576287147629093 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d12su (by norm_num)
  have hd13 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))
    (by norm_num) (by norm_num) c12l c12u s12l s12u
  obtain ⟨d13cl, d13cu, d13sl, d13su⟩ := hd13
  have c13l :
      (19989724324013727852579629319704718649615769 : ℝ) / 20000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) :=
    le_trans (by norm_num) d13cl
  have c13u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) ≤ (19989724324013760631879817516164392275222781 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d13cu (by norm_num)
  have s13l :
      (3205157757165515837028550007936231709033493 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) :=
    le_trans (by norm_num) d13sl
  have s13u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) ≤ (641031551433103521702541310435101330524791 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d13su (by norm_num)
  have hd14 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))))
    (by norm_num) (by norm_num) c13l c13u s13l s13u
  obtain ⟨d14cl, d14cu, d14sl, d14su⟩ := hd14
  have hangle : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) = X := by
    rw [← hXeq]; ring
  rw [hangle] at d14cl d14cu d14sl d14su
  have cXl :
      (49897269637516522238313698292986605452742261 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos X :=
    le_trans (by norm_num) d14cl
  have cXu :
      Real.cos X ≤ (99794539275033699725801692725047481371772843 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d14cu (by norm_num)
  have sXl :
      (6407021998071279715464164952733981785058621 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin X :=
    le_trans (by norm_num) d14sl
  have sXu :
      Real.sin X ≤ (400438874879455860180936599122850289649881 : ℝ) / 6250000000000000000000000000000000000000000 :=
    le_trans d14su (by norm_num)
  rw [hcot]
  exact RH.Certificates.TrigIntervalSweep.cot_bound_of_sin_cos_bounds
    (x := X) (sinLo := (6407021998071279715464164952733981785058621 : ℝ) / 100000000000000000000000000000000000000000000)
    (sinHi := (400438874879455860180936599122850289649881 : ℝ) / 6250000000000000000000000000000000000000000)
    (cosLo := (49897269637516522238313698292986605452742261 : ℝ) / 50000000000000000000000000000000000000000000)
    (cosHi := (99794539275033699725801692725047481371772843 : ℝ) / 100000000000000000000000000000000000000000000)
    (lo := (623032287418861373931236352453 : ℝ) / 40000000000000000000000000000)
    (hi := (1557580718547167076879709756321 : ℝ) / 100000000000000000000000000000)
    (by norm_num) sXl sXu (by norm_num) cXl cXu (by norm_num) (by norm_num)

/-- Certificate: `cot(π*1/50)` lies in a tiny explicit rational interval. -/
theorem cot_pi_div_1_50_mem_interval :
    (1986818105483151695417222967587 : ℝ) / 125000000000000000000000000000 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 50 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 50 ≤
      (3973636210966335491126789116983 : ℝ) / 250000000000000000000000000000 := by
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 50
      = Real.cos (Real.pi * 1 / 50) / Real.sin (Real.pi * 1 / 50) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi * 1 / 50 with hXdef
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (157079632679489661923 : ℝ) / 2500000000000000000000 ≤ X :=
    by rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (314159265358979323847 : ℝ) / 5000000000000000000000 :=
    by rw [hXdef]; nlinarith [hpu]
  set y : ℝ := X / 2 ^ 14 with hydef
  have hyl : (157079632679489661923 : ℝ) / 40960000000000000000000000 ≤ y :=
    by rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (314159265358979323847 : ℝ) / 81920000000000000000000000 :=
    by rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl
  have hXeq : (2 : ℝ) ^ 14 * y = X := by rw [hydef]; ring
  have hbase := cos_sin_base_bound (y := y)
    (yl := (157079632679489661923 : ℝ) / 40960000000000000000000000)
    (yu := (314159265358979323847 : ℝ) / 81920000000000000000000000)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  have c0l :
      (99999999999264657169498169533924050323790339 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u :
      Real.cos y ≤ (9999999999926465716950042257175526827420753 : ℝ) / 10000000000000000000000000000000000000000000 :=
    le_trans hcb2 (by norm_num)
  have s0l :
      (95873799242617576205983091500924621121 : ℝ) / 25000000000000000000000000000000000000000000 ≤
        Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u :
      Real.sin y ≤ (95873799242617576769547723916330006093 : ℝ) / 25000000000000000000000000000000000000000000 :=
    le_trans hsb2 (by norm_num)
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l :
      (24999999999264657169500873179315902542642643 : ℝ) / 25000000000000000000000000000000000000000000 ≤ Real.cos (2 * (y)) :=
    le_trans (by norm_num) d1cl
  have c1u :
      Real.cos (2 * (y)) ≤ (12499999999632328584751563108573551962753837 : ℝ) / 12500000000000000000000000000000000000000000 :=
    le_trans d1cu (by norm_num)
  have s1l :
      (383495196967650300387691139665560761333 : ℝ) / 50000000000000000000000000000000000000000000 ≤
        Real.sin (2 * (y)) :=
    le_trans (by norm_num) d1sl
  have s1u :
      Real.sin (2 * (y)) ≤ (191747598483825151320979154801237210617 : ℝ) / 25000000000000000000000000000000000000000000 :=
    le_trans d1su (by norm_num)
  have hd2 := cos_sin_double_bound (θ := 2 * (y)) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l :
      (49999999994117257356093502087065855150413243 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (y))) :=
    le_trans (by norm_num) d2cl
  have c2u :
      Real.cos (2 * (2 * (y))) ≤ (49999999994117257356111526389714936051664367 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d2cu (by norm_num)
  have s2l :
      (1533980787825481130571402618062639857129 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (y))) :=
    le_trans (by norm_num) d2sl
  have s2u :
      Real.sin (2 * (2 * (y))) ≤ (1533980787825481139588609542214965367219 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d2su (by norm_num)
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * (y))) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l :
      (49999999976469029425758274788840861133902497 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3cl
  have c3u :
      Real.cos (2 * (2 * (2 * (y)))) ≤ (19999999990587611770332148799771480860880549 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d3cu (by norm_num)
  have s3l :
      (3067961575290001693323835497267315112051 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (y)))) :=
    le_trans (by norm_num) d3sl
  have s3u :
      Real.sin (2 * (2 * (2 * (y)))) ≤ (3067961575290001711359355300809235505271 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d3su (by norm_num)
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * (y))))
    (by norm_num) (by norm_num) c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l :
      (99999999811752235450362724403993284842229391 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4cl
  have c4u :
      Real.cos (2 * (2 * (2 * (2 * (y))))) ≤ (99999999811752235450939502088424570214088429 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d4cu (by norm_num)
  have s4l :
      (1533980786923079711151384558417373102917 : ℝ) / 25000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (y))))) :=
    le_trans (by norm_num) d4sl
  have s4u :
      Real.sin (2 * (2 * (2 * (2 * (y))))) ≤ (6135923147692318880685425482648365275409 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d4su (by norm_num)
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (y)))))
    (by norm_num) (by norm_num) c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l :
      (24999999811752235627548828693671647772735379 : ℝ) / 25000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5cl
  have c5u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (y)))))) ≤ (99999999247008942512502425508068648188932099 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d5cu (by norm_num)
  have s5l :
      (1533980784035395171147752396827032846913 : ℝ) / 12500000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) :=
    le_trans (by norm_num) d5sl
  have s5u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (y)))))) ≤ (1533980784035395180176571850954291512103 : ℝ) / 12500000000000000000000000000000000000000000 :=
    le_trans d5su (by norm_num)
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (y))))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l :
      (49999998494017890690345956145516627608189867 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6cl
  have c6u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤ (49999998494017890694960177577536066786715581 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d6cu (by norm_num)
  have s6l :
      (6135923089938628174996933171253004156947 : ℝ) / 25000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) :=
    le_trans (by norm_num) d6sl
  have s6u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (y))))))) ≤ (24543692359754512845015093028332887250189 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d6su (by norm_num)
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (y)))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l :
      (99999987952143306961336734024515512432906407 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7cl
  have c7u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤ (390624952938059792961916032690786866642593 : ℝ) / 390625000000000000000000000000000000000000 :=
    le_trans d7cu (by norm_num)
  have s7l :
      (49087383241014561792361811429496740989223 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) :=
    le_trans (by norm_num) d7sl
  have s7u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))) ≤ (24543691620507281043473262316042461101013 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d7su (by norm_num)
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l :
      (12499993976072016357795607003545817500090111 : ℝ) / 12500000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8cl
  have c8u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤ (12499993976072016376252489952049704676399267 : ℝ) / 12500000000000000000000000000000000000000000 :=
    le_trans d8cu (by norm_num)
  have s8l :
      (9817475465407394910449964376186924464297 : ℝ) / 10000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) :=
    le_trans (by norm_num) d8sl
  have s8u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))) ≤ (9817475465407394972990900702001193003123 : ℝ) / 10000000000000000000000000000000000000000000 :=
    le_trans d8su (by norm_num)
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l :
      (49999903617175485858075060942695938347439767 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤ (99999807234350972306770091609206034961727427 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d9cu (by norm_num)
  have s9l :
      (7853976587380944101903615135454685367891 : ℝ) / 4000000000000000000000000000000000000000000 ≤
        Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))) ≤ (98174707342261802044164247469515497193301 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d9su (by norm_num)
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  have c10l :
      (99999228938147058773506397748702439636047473 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) :=
    le_trans (by norm_num) d10cl
  have c10u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) ≤ (24999807234536765283995430648571841156084181 : ℝ) / 25000000000000000000000000000000000000000000 :=
    le_trans d10cu (by norm_num)
  have s10l :
      (392698072380600045378383366831729905665147 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) :=
    le_trans (by norm_num) d10sl
  have s10u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))) ≤ (49087259047575006347401420879329558886941 : ℝ) / 12500000000000000000000000000000000000000000 :=
    le_trans d10su (by norm_num)
  have hd11 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))
    (by norm_num) (by norm_num) c10l c10u s10l s10u
  obtain ⟨d11cl, d11cu, d11sl, d11su⟩ := hd11
  have c11l :
      (2499922894111974067881218570621615656600439 : ℝ) / 2500000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) :=
    le_trans (by norm_num) d11cl
  have c11u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) ≤ (19999383152895794433015435524628860667053467 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d11cu (by norm_num)
  have s11l :
      (392695044435566683044887647875878074907479 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) :=
    le_trans (by norm_num) d11sl
  have s11u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))) ≤ (785390088871133395446138130980526741558041 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d11su (by norm_num)
  have hd12 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))
    (by norm_num) (by norm_num) c11l c11u s11l s11u
  obtain ⟨d12cl, d12cu, d12sl, d12su⟩ := hd12
  have c12l :
      (99987663248166025845557598288247466455102833 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) :=
    le_trans (by norm_num) d12cl
  have c12u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) ≤ (99987663248166063643705517620315439879157677 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d12cu (by norm_num)
  have s12l :
      (1570731731182067392591684075649049601228147 : ℝ) / 100000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) :=
    le_trans (by norm_num) d12sl
  have s12u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))) ≤ (785365865591033799869315395914889364595001 : ℝ) / 50000000000000000000000000000000000000000000 :=
    le_trans d12su (by norm_num)
  have hd13 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))
    (by norm_num) (by norm_num) c12l c12u s12l s12u
  obtain ⟨d13cl, d13cu, d13sl, d13su⟩ := hd13
  have c13l :
      (49975328018286509821761827534472909394832613 : ℝ) / 50000000000000000000000000000000000000000000 ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) :=
    le_trans (by norm_num) d13cl
  have c13u :
      Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) ≤ (99950656036573170817463077570660436108927471 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d13cu (by norm_num)
  have s13l :
      (785268976953206987453561851167532050276621 : ℝ) / 25000000000000000000000000000000000000000000 ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) :=
    le_trans (by norm_num) d13sl
  have s13u :
      Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) ≤ (3141075907812829551472036763702037834736929 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d13su (by norm_num)
  have hd14 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y))))))))))))))
    (by norm_num) (by norm_num) c13l c13u s13l s13u
  obtain ⟨d14cl, d14cu, d14sl, d14su⟩ := hd14
  have hangle : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (y)))))))))))))) = X := by
    rw [← hXeq]; ring
  rw [hangle] at d14cl d14cu d14sl d14su
  have cXl :
      (3118833526338331632424835448227054234164393 : ℝ) / 3125000000000000000000000000000000000000000 ≤ Real.cos X :=
    le_trans (by norm_num) d14cl
  have cXu :
      Real.cos X ≤ (99802672842827216634971570831522535246851237 : ℝ) / 100000000000000000000000000000000000000000000 :=
    le_trans d14cu (by norm_num)
  have sXl :
      (1255810390586265238709226241360329770406647 : ℝ) / 20000000000000000000000000000000000000000000 ≤ Real.sin X :=
    le_trans (by norm_num) d14sl
  have sXu :
      Real.sin X ≤ (1255810390586267778451489448155511814201903 : ℝ) / 20000000000000000000000000000000000000000000 :=
    le_trans d14su (by norm_num)
  rw [hcot]
  exact RH.Certificates.TrigIntervalSweep.cot_bound_of_sin_cos_bounds
    (x := X) (sinLo := (1255810390586265238709226241360329770406647 : ℝ) / 20000000000000000000000000000000000000000000)
    (sinHi := (1255810390586267778451489448155511814201903 : ℝ) / 20000000000000000000000000000000000000000000)
    (cosLo := (3118833526338331632424835448227054234164393 : ℝ) / 3125000000000000000000000000000000000000000)
    (cosHi := (99802672842827216634971570831522535246851237 : ℝ) / 100000000000000000000000000000000000000000000)
    (lo := (1986818105483151695417222967587 : ℝ) / 125000000000000000000000000000)
    (hi := (3973636210966335491126789116983 : ℝ) / 250000000000000000000000000000)
    (by norm_num) sXl sXu (by norm_num) cXl cXu (by norm_num) (by norm_num)
end RH.Certificates.TrigIntervalSweep
