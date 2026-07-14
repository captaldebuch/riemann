import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

/-!
# A rational interval certificate for `cotangentTermV 1 24 = cot(π/24)`

This file proves, as a fully checked `theorem`, a rational interval bound on `cot(π/24)`.

The strategy is a Taylor base case at `y = (π/24) / 2^10` combined with `10`
angle-doubling steps `cos(2θ) = 2cos²θ - 1`, `sin(2θ) = 2 sinθ cosθ`, ending at the
angle `2^10 * y = π/24`. All numeric bounds are pre-computed rationals, each chosen so
that a plain `norm_num` inequality certifies it against the exact algebraic expression.
-/

namespace RH.Certificates.TrigIntervalDemo

open Real

/-- The angle-doubling step: from two-sided rational bounds on `cos θ` and `sin θ`
(with nonnegative lower bounds), derive two-sided algebraic bounds on `cos (2θ)`
and `sin (2θ)`. -/
lemma cos_sin_double_bound {θ cl cu sl su : ℝ}
    (hcl : 0 ≤ cl) (hsl : 0 ≤ sl)
    (hc1 : cl ≤ Real.cos θ) (hc2 : Real.cos θ ≤ cu)
    (hs1 : sl ≤ Real.sin θ) (hs2 : Real.sin θ ≤ su) :
    2 * cl ^ 2 - 1 ≤ Real.cos (2 * θ) ∧ Real.cos (2 * θ) ≤ 2 * cu ^ 2 - 1 ∧
      2 * sl * cl ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 2 * su * cu := by
  have hccl : cl ≤ cu := le_trans hc1 hc2
  have hcu0 : 0 ≤ cu := le_trans hcl hccl
  have hssl : sl ≤ su := le_trans hs1 hs2
  have hsu0 : 0 ≤ su := le_trans hsl hssl
  rw [Real.cos_two_mul, Real.sin_two_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul hc1 hc1 hcl (le_trans hcl hc1)]
  · nlinarith [mul_le_mul hc2 hc2 (le_trans hcl hc1) hcu0]
  · nlinarith [mul_le_mul hs1 hc1 hcl (le_trans hsl hs1)]
  · nlinarith [mul_le_mul hs2 hc2 (le_trans hcl hc1) hsu0]

/-- Base-case Taylor bounds on `cos y` and `sin y` from `Real.cos_bound` / `Real.sin_bound`,
made symbolic in the rational bracket `[yl, yu]` for `y`. -/
lemma cos_sin_base_bound {y yl yu : ℝ}
    (hy0 : 0 ≤ y) (hyl : yl ≤ y) (hyu : y ≤ yu) (hyu1 : yu ≤ 1) (hyl0 : 0 ≤ yl) :
    (1 - yu ^ 2 / 2 - yu ^ 4 * (5 / 96) ≤ Real.cos y ∧
      Real.cos y ≤ 1 - yl ^ 2 / 2 + yu ^ 4 * (5 / 96)) ∧
    (yl - yu ^ 3 / 6 - yu ^ 4 * (5 / 96) ≤ Real.sin y ∧
      Real.sin y ≤ yu - yl ^ 3 / 6 + yu ^ 4 * (5 / 96)) := by
  have hya : |y| ≤ 1 := by
    rw [abs_of_nonneg hy0]; exact le_trans hyu hyu1
  have habs : |y| = y := abs_of_nonneg hy0
  -- cos bound
  have hcos := Real.cos_bound hya
  rw [abs_le] at hcos
  rw [habs] at hcos
  have hsin := Real.sin_bound hya
  rw [abs_le] at hsin
  rw [habs] at hsin
  -- monotone powers
  have hy2 : y ^ 2 ≤ yu ^ 2 := by nlinarith
  have hy2' : yl ^ 2 ≤ y ^ 2 := by nlinarith
  have hy3 : y ^ 3 ≤ yu ^ 3 := by nlinarith
  have hy3' : yl ^ 3 ≤ y ^ 3 := by nlinarith
  have hy4 : y ^ 4 ≤ yu ^ 4 := by nlinarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [hcos.1]
  · nlinarith [hcos.2]
  · nlinarith [hsin.1]
  · nlinarith [hsin.2]

/-- Certificate: `cot(π/24)` lies in a tiny explicit rational interval. -/
theorem cotangentTermV_1_24_mem_interval :
    (560467728641666387133 : ℝ) / 73786976294838206464 ≤
      RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 24 ∧
    RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 24 ≤
      (4483741829309490358569 : ℝ) / 590295810358705651712 := by
  -- Rewrite the cotangent term into `cos X / sin X` with `X = π / 24`.
  have hcot : RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV 1 24
      = Real.cos (Real.pi / 24) / Real.sin (Real.pi / 24) := by
    unfold RH.Criteria.NymanBeurling.VasyuninGram.cotangentTermV
    norm_num
  set X : ℝ := Real.pi / 24 with hXdef
  -- π bounds → bounds on X.
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hXl : (157079632679489661923 : ℝ) / 1200000000000000000000 ≤ X := by
    rw [hXdef]; nlinarith [hpl]
  have hXu : X ≤ (314159265358979323847 : ℝ) / 2400000000000000000000 := by
    rw [hXdef]; nlinarith [hpu]
  -- y = X / 2^10.
  set y : ℝ := X / 2 ^ 10 with hydef
  have hyl : (9432317002704587 : ℝ) / 73786976294838206464 ≤ y := by
    rw [hydef]; nlinarith [hXl]
  have hyu : y ≤ (150917072043273393 : ℝ) / 1180591620717411303424 := by
    rw [hydef]; nlinarith [hXu]
  have hy0 : 0 ≤ y := by
    apply le_trans _ hyl; norm_num
  -- `2^10 * y = X`.
  have hXeq : (2 : ℝ) ^ 10 * y = X := by rw [hydef]; ring
  -- ==================== Base case (level 0) ====================
  have hbase := cos_sin_base_bound (y := y)
    (yl := (9432317002704587 : ℝ) / 73786976294838206464)
    (yu := (150917072043273393 : ℝ) / 1180591620717411303424)
    hy0 hyl hyu (by norm_num) (by norm_num)
  obtain ⟨⟨hcb1, hcb2⟩, ⟨hsb1, hsb2⟩⟩ := hbase
  -- Concrete level-0 bounds (rational sandwich against the Taylor expressions).
  have c0l : (295147902767853977185 : ℝ) / 295147905179352825856 ≤ Real.cos y :=
    le_trans (by norm_num) hcb1
  have c0u : Real.cos y ≤ (1180591611071415941581 : ℝ) / 1180591620717411303424 :=
    le_trans hcb2 (by norm_num)
  have s0l : (75458535816117769 : ℝ) / 590295810358705651712 ≤ Real.sin y :=
    le_trans (by norm_num) hsb1
  have s0u : Real.sin y ≤ (37729267908067095 : ℝ) / 295147905179352825856 :=
    le_trans hsb2 (by norm_num)
  -- ==================== Doubling levels 1 .. 10 ====================
  -- Angle at level i is `2^i * y`. We track `2*(2^(i-1)*y) = 2^i * y`.
  -- Level 1 : angle 2*y
  have hd1 := cos_sin_double_bound (θ := y) (by norm_num) (by norm_num) c0l c0u s0l s0u
  obtain ⟨d1cl, d1cu, d1sl, d1su⟩ := hd1
  have c1l : (147573947766678735289 : ℝ) / 147573952589676412928 ≤ Real.cos (2 * y) :=
    le_trans (by norm_num) d1cl
  have c1u : Real.cos (2 * y) ≤ (1180591582133430013677 : ℝ) / 1180591620717411303424 :=
    le_trans d1cu (by norm_num)
  have s1l : (18864633799896405 : ℝ) / 73786976294838206464 ≤ Real.sin (2 * y) :=
    le_trans (by norm_num) d1sl
  have s1u : Real.sin (2 * y) ≤ (301834140798408173 : ℝ) / 1180591620717411303424 :=
    le_trans d1su (by norm_num)
  -- Level 2 : angle 2*(2*y)
  have hd2 := cos_sin_double_bound (θ := 2 * y) (by norm_num) (by norm_num) c1l c1u s1l s1u
  obtain ⟨d2cl, d2cu, d2sl, d2su⟩ := hd2
  have c2l : (1180591466381488140971 : ℝ) / 1180591620717411303424 ≤ Real.cos (2 * (2 * y)) :=
    le_trans (by norm_num) d2cl
  have c2u : Real.cos (2 * (2 * y)) ≤ (18446741662210760413 : ℝ) / 18446744073709551616 :=
    le_trans d2cu (by norm_num)
  have s2l : (301834130933828217 : ℝ) / 590295810358705651712 ≤ Real.sin (2 * (2 * y)) :=
    le_trans (by norm_num) d2sl
  have s2u : Real.sin (2 * (2 * y)) ≤ (603668261867787889 : ℝ) / 1180591620717411303424 :=
    le_trans d2su (by norm_num)
  -- Level 3
  have hd3 := cos_sin_double_bound (θ := 2 * (2 * y)) (by norm_num) (by norm_num) c2l c2u s2l s2u
  obtain ⟨d3cl, d3cu, d3sl, d3su⟩ := hd3
  have c3l : (1180591003373759005545 : ℝ) / 1180591620717411303424 ≤ Real.cos (2 * (2 * (2 * y))) :=
    le_trans (by norm_num) d3cl
  have c3u : Real.cos (2 * (2 * (2 * y))) ≤ (590295501686880553695 : ℝ) / 590295810358705651712 :=
    le_trans d3cu (by norm_num)
  have s3l : (301834091475773101 : ℝ) / 295147905179352825856 ≤ Real.sin (2 * (2 * (2 * y))) :=
    le_trans (by norm_num) d3sl
  have s3u : Real.sin (2 * (2 * (2 * y))) ≤ (301834091475838963 : ℝ) / 295147905179352825856 :=
    le_trans d3su (by norm_num)
  -- Level 4
  have hd4 := cos_sin_double_bound (θ := 2 * (2 * (2 * y))) (by norm_num) (by norm_num)
    c3l c3u s3l s3u
  obtain ⟨d4cl, d4cu, d4sl, d4su⟩ := hd4
  have c4l : (295147287835861935689 : ℝ) / 295147905179352825856
      ≤ Real.cos (2 * (2 * (2 * (2 * y)))) := le_trans (by norm_num) d4cl
  have c4u : Real.cos (2 * (2 * (2 * (2 * y))))
      ≤ (1180589151343456150133 : ℝ) / 1180591620717411303424 := le_trans d4cu (by norm_num)
  have s4l : (301833933643583587 : ℝ) / 147573952589676412928
      ≤ Real.sin (2 * (2 * (2 * (2 * y)))) := le_trans (by norm_num) d4sl
  have s4u : Real.sin (2 * (2 * (2 * (2 * y))))
      ≤ (2414671469149199891 : ℝ) / 1180591620717411303424 := le_trans d4su (by norm_num)
  -- Level 5
  have hd5 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * y)))) (by norm_num) (by norm_num)
    c4l c4u s4l s4u
  obtain ⟨d5cl, d5cu, d5sl, d5su⟩ := hd5
  have c5l : (1180581743231887148929 : ℝ) / 1180591620717411303424
      ≤ Real.cos (2 * (2 * (2 * (2 * (2 * y))))) := le_trans (by norm_num) d5cl
  have c5u : Real.cos (2 * (2 * (2 * (2 * (2 * y)))))
      ≤ (9223294868999381081 : ℝ) / 9223372036854775808 := le_trans d5cu (by norm_num)
  have s5l : (2414666418522565789 : ℝ) / 590295810358705651712
      ≤ Real.sin (2 * (2 * (2 * (2 * (2 * y))))) := le_trans (by norm_num) d5sl
  have s5u : Real.sin (2 * (2 * (2 * (2 * (2 * y)))))
      ≤ (2414666418523114179 : ℝ) / 590295810358705651712 := le_trans d5su (by norm_num)
  -- Level 6
  have hd6 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * y)))))
    (by norm_num) (by norm_num) c5l c5u s5l s5u
  obtain ⟨d6cl, d6cu, d6sl, d6su⟩ := hd6
  have c6l : (1180552110940595750577 : ℝ) / 1180591620717411303424
      ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * y)))))) := le_trans (by norm_num) d6cl
  have c6u : Real.cos (2 * (2 * (2 * (2 * (2 * (2 * y))))))
      ≤ (147569013867591283401 : ℝ) / 147573952589676412928 := le_trans d6cu (by norm_num)
  have s6l : (9658584864326154801 : ℝ) / 1180591620717411303424
      ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * y)))))) := le_trans (by norm_num) d6sl
  have s6u : Real.sin (2 * (2 * (2 * (2 * (2 * (2 * y))))))
      ≤ (9658584864328623473 : ℝ) / 1180591620717411303424 := le_trans d6su (by norm_num)
  -- Level 7
  have hd7 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * y))))))
    (by norm_num) (by norm_num) c6l c6u s6l s6u
  obtain ⟨d7cl, d7cu, d7sl, d7su⟩ := hd7
  have c7l : (1180433584254624008885 : ℝ) / 1180591620717411303424
      ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * y))))))) := le_trans (by norm_num) d7cl
  have c7u : Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * y)))))))
      ≤ (1180433584255162057403 : ℝ) / 1180591620717411303424 := le_trans d7cu (by norm_num)
  have s7l : (19316523258652612821 : ℝ) / 1180591620717411303424
      ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * y))))))) := le_trans (by norm_num) d7sl
  have s7u : Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * y)))))))
      ≤ (2414565407332468875 : ℝ) / 147573952589676412928 := le_trans d7su (by norm_num)
  -- Level 8
  have hd8 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * y)))))))
    (by norm_num) (by norm_num) c7l c7u s7l s7u
  obtain ⟨d8cl, d8cu, d8sl, d8su⟩ := hd8
  have c8l : (589979758588222401621 : ℝ) / 590295810358705651712
      ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y)))))))) := le_trans (by norm_num) d8cl
  have c8u : Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y))))))))
      ≤ (589979758589298354609 : ℝ) / 590295810358705651712 := le_trans d8cu (by norm_num)
  have s8l : (19313937508461288477 : ℝ) / 590295810358705651712
      ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y)))))))) := le_trans (by norm_num) d8sl
  have s8u : Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y))))))))
      ≤ (38627875016954458213 : ℝ) / 1180591620717411303424 := le_trans d8su (by norm_num)
  -- Level 9
  have hd9 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y))))))))
    (by norm_num) (by norm_num) c8l c8u s8l s8u
  obtain ⟨d9cl, d9cu, d9sl, d9su⟩ := hd9
  have c9l : (589031941712925755323 : ℝ) / 590295810358705651712
      ≤ Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y))))))))) :=
    le_trans (by norm_num) d9cl
  have c9u : Real.cos (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y)))))))))
      ≤ (1178063883434454525921 : ℝ) / 1180591620717411303424 := le_trans d9cu (by norm_num)
  have s9l : (77214386337627539255 : ℝ) / 1180591620717411303424
      ≤ Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y))))))))) :=
    le_trans (by norm_num) d9sl
  have s9u : Real.sin (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y)))))))))
      ≤ (77214386337832084415 : ℝ) / 1180591620717411303424 := le_trans d9su (by norm_num)
  -- Level 10 : angle 2^10 * y = X
  have hd10 := cos_sin_double_bound (θ := 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y)))))))))
    (by norm_num) (by norm_num) c9l c9u s9l s9u
  obtain ⟨d10cl, d10cu, d10sl, d10su⟩ := hd10
  -- The level-10 angle equals X.
  have hangle : (2 : ℝ) * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * y)))))))))
      = X := by rw [← hXeq]; ring
  rw [hangle] at d10cl d10cu d10sl d10su
  have cXl : (585245747855176517043 : ℝ) / 590295810358705651712 ≤ Real.cos X :=
    le_trans (by norm_num) d10cl
  have cXu : Real.cos X ≤ (1170491495744691416323 : ℝ) / 1180591620717411303424 :=
    le_trans d10cu (by norm_num)
  have sXl : (154098128817776364095 : ℝ) / 1180591620717411303424 ≤ Real.sin X :=
    le_trans (by norm_num) d10sl
  have sXu : Real.sin X ≤ (77049064409654953381 : ℝ) / 590295810358705651712 :=
    le_trans d10su (by norm_num)
  -- Positivity of sin X (and its bounds).
  have hsXpos : (0 : ℝ) < Real.sin X := lt_of_lt_of_le (by norm_num) sXl
  have hcXpos : (0 : ℝ) ≤ Real.cos X :=
    le_trans (by norm_num) cXl
  -- ==================== Final division ====================
  rw [hcot]
  constructor
  · -- lower : lower_num ≤ cos X / sin X, using cos X ≥ cXl, sin X ≤ sXu.
    rw [le_div_iff₀ hsXpos]
    -- lower_num * sin X ≤ cos X.  Suffices lower_num * sXu ≤ cXl ≤ cos X, but sin X ≤ sXu,
    -- and lower_num ≥ 0, so lower_num * sin X ≤ lower_num * sXu ≤ cXl ≤ cos X.
    have h1 : (560467728641666387133 : ℝ) / 73786976294838206464 * Real.sin X
        ≤ (560467728641666387133 : ℝ) / 73786976294838206464
          * ((77049064409654953381 : ℝ) / 590295810358705651712) := by
      apply mul_le_mul_of_nonneg_left sXu (by norm_num)
    have h2 : (560467728641666387133 : ℝ) / 73786976294838206464
        * ((77049064409654953381 : ℝ) / 590295810358705651712)
        ≤ (585245747855176517043 : ℝ) / 590295810358705651712 := by norm_num
    exact le_trans (le_trans h1 h2) cXl
  · -- upper : cos X / sin X ≤ upper_num, using cos X ≤ cXu, sin X ≥ sXl.
    rw [div_le_iff₀ hsXpos]
    -- cos X ≤ cXu ≤ upper_num * sXl ≤ upper_num * sin X.
    have h1 : Real.cos X ≤ (1170491495744691416323 : ℝ) / 1180591620717411303424 := cXu
    have h2 : (1170491495744691416323 : ℝ) / 1180591620717411303424
        ≤ (4483741829309490358569 : ℝ) / 590295810358705651712
          * ((154098128817776364095 : ℝ) / 1180591620717411303424) := by norm_num
    have h3 : (4483741829309490358569 : ℝ) / 590295810358705651712
          * ((154098128817776364095 : ℝ) / 1180591620717411303424)
        ≤ (4483741829309490358569 : ℝ) / 590295810358705651712 * Real.sin X := by
      apply mul_le_mul_of_nonneg_left sXl (by norm_num)
    exact le_trans (le_trans h1 h2) h3

end RH.Certificates.TrigIntervalDemo
