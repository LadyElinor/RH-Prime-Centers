import QuarticChord.Asymptotic

/-! Uniform rescaling of the short- and long-interval errors from base
`z = A/d` to the single maximal width at base `A`. -/
namespace QuarticChord

open Filter Set

/-- Any fixed positive power of the base eventually dominates any power of its logarithm. -/
theorem eventually_logpow_le_rpow (m r : ℝ) (hr : 0 < r) :
    ∀ᶠ A : ℝ in atTop, (Real.log A)^m ≤ A^r := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop m hr).bound (by norm_num : (0:ℝ) < 1),
      eventually_gt_atTop (1:ℝ)] with A h hA
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.log_pos hA) m),
    abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hA) r), one_mul] using h

/-- The first term covers short offsets using an integer count. The second
term covers long offsets using a logarithmic saving at the dilated base. -/
theorem shortIntervalPrimeEstimate_of_local {B m D : ℝ} (hB : 0 ≤ B)
    (hm : 0 < m) (hD : 0 ≤ D)
    (localBound : ∀ᶠ z : ℝ in atTop, ∀ A d u : ℝ, 0 < A → 0 < d → 0 ≤ u →
      A/d = z → u/d ≤ z^(99/100 : ℝ) →
      |thetaMass A d u - u/d| ≤ 4*z^(7/10 : ℝ) + D*(u/d)/(Real.log z)^m) :
    ShortIntervalPrimeEstimate B m := by
  let C := 4 + D*(2:ℝ)^m
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have fixed (d : ℝ) (hd1 : 1 ≤ d) :
      ∀ᶠ A : ℝ in atTop, ∀ u ∈ Icc 0 (width B A),
        |thetaMass A d u - u/d| ≤ C * width B A / (Real.log A)^m := by
    have hd := zero_lt_one.trans_le hd1
    have t : Tendsto (fun A : ℝ => A/d) atTop atTop := tendsto_id.atTop_div_const hd
    filter_upwards [t.eventually localBound, t.eventually (eventually_gt_atTop (1:ℝ)),
        Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log d),
        Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop (1:ℝ),
        eventually_logpow_le_rpow B (6/25) (by norm_num),
        eventually_logpow_le_rpow m (1/20) (by norm_num)] with A hloc hz hlogd hlogA hA hBpow hmpow
    intro u hu
    let z := A/d
    have ha := zero_lt_one.trans hA
    have hzpos : 0 < z := div_pos ha hd
    have hzl : 0 < Real.log z := Real.log_pos hz
    have hl := Real.log_pos hA
    have hlm := Real.rpow_pos_of_pos hl m
    have hzm := Real.rpow_pos_of_pos hzl m
    have hVpos : 0 ≤ width B A := hu.1.trans hu.2
    have zA : z ≤ A := div_le_self ha.le hd1
    have zlA : Real.log A ≤ 2 * Real.log z := by
      dsimp [z]
      rw [Real.log_div ha.ne' hd.ne']
      linarith
    have hlog : (Real.log A)^m ≤ (2:ℝ)^m * (Real.log z)^m := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hzl.le]
      exact Real.rpow_le_rpow hl.le zlA hm.le
    have wUpper : width B A ≤ A^(99/100 : ℝ) := by
      unfold width
      calc
        _ ≤ A^(3/4:ℝ) * A^(6/25:ℝ) := mul_le_mul_of_nonneg_left hBpow (by positivity)
        _ = _ := by rw [← Real.rpow_add ha]; norm_num
    have len : u/d ≤ z^(99/100 : ℝ) := by
      rw [Real.div_rpow ha.le hd.le]
      have hden : d^(99/100:ℝ) ≤ d := by
        simpa using Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (99/100:ℝ) ≤ 1)
      calc
        _ ≤ A^(99/100:ℝ)/d := div_le_div_of_nonneg_right (hu.2.trans wUpper) hd.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hd _) hden
    have small : z^(7/10:ℝ) * (Real.log A)^m ≤ width B A := by
      calc
        _ ≤ A^(7/10:ℝ) * A^(1/20:ℝ) :=
          mul_le_mul (Real.rpow_le_rpow hzpos.le zA (by norm_num)) hmpow hlm.le (by positivity)
        _ = A^(3/4:ℝ) := by rw [← Real.rpow_add ha]; norm_num
        _ ≤ width B A := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hlogA hB)
    have long : (u/d)/(Real.log z)^m ≤ (2:ℝ)^m * width B A / (Real.log A)^m := by
      apply (div_le_div_iff₀ hzm hlm).2
      calc
        _ ≤ width B A * ((2:ℝ)^m * (Real.log z)^m) :=
          mul_le_mul ((div_le_self hu.1 hd1).trans hu.2) hlog hlm.le hVpos
        _ = _ := by ring
    calc
      _ ≤ 4*z^(7/10:ℝ) + D*(u/d)/(Real.log z)^m := hloc A d u ha hd hu.1 rfl len
      _ ≤ 4 * (width B A/(Real.log A)^m) + D*((2:ℝ)^m*width B A/(Real.log A)^m) := by
        rw [mul_div_assoc D]
        exact add_le_add (mul_le_mul_of_nonneg_left ((le_div_iff₀ hlm).2 small) (by norm_num))
          (mul_le_mul_of_nonneg_left long hD)
      _ = _ := by dsimp [C]; ring
  filter_upwards [fixed 1 (by norm_num), fixed 2 (by norm_num), fixed 4 (by norm_num)]
    with A one two four
  intro d hd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl <;> assumption

end QuarticChord
