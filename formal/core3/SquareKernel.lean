import HigherPowers

/-! The prime-square tent and its square-root model. -/
namespace PrimeWindowDiscrete

open Filter Real Set MeasureTheory PrimeWindowTransfer Asymptotics
open scoped Topology Interval

noncomputable def squareBias : ℝ := 6 * sqrt 2 - 8

private theorem average_sqrt {y : ℝ} (hy : 0 < y) :
    PrimeWindowTransfer.average sqrt y = (2 - sqrt 2) * sqrt y := by
  have hab : y ≤ 2*y := by linarith
  have hpos : (0 : ℝ) ∉ [[y, 2*y]] := by
    rw [uIcc_of_le hab]
    exact fun h => (not_le_of_gt hy) h.1
  have hi : (∫ t in y..2*y, weighted sqrt t) = ∫ t in y..2*y, t ^ (-3/2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht' := hy.trans_le ht.1
    simp only [weighted, smul_eq_mul, sqrt_eq_rpow, ← Real.rpow_neg_ofNat,
      ← Real.rpow_add ht']
    norm_num
  rw [PrimeWindowTransfer.average, hi, integral_rpow (Or.inr ⟨by norm_num, hpos⟩), smul_eq_mul]
  rw [show (-3/2:ℝ) + 1 = -(1/2) by norm_num,
    Real.rpow_neg (by positivity : 0 ≤ 2*y), Real.rpow_neg hy.le, ← sqrt_eq_rpow,
    ← sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hys := sq_sqrt hy.le
  have h2s := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  field_simp
  ring_nf
  simp only [hys, h2s]
  ring

theorem neg_tent_sqrt {y : ℝ} (hy : 0 < y) :
    -tent sqrt y = squareBias * sqrt y := by
  rw [tent, average_sqrt hy, average_sqrt (by linarith), smul_eq_mul, squareBias,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  linear_combination (-(2*sqrt y)) * (sq_sqrt (by norm_num : (0:ℝ) ≤ 2))

private theorem weighted_mono_integrable {f : ℝ → ℝ} (hf : Monotone f) {y : ℝ} (hy : 0 < y) :
    IntervalIntegrable (weighted f) volume y (2*y) := by
  have hk : ContinuousOn (fun u : ℝ => u^(-2 : ℤ)) [[y,2*y]] := by
    rw [uIcc_of_le (by linarith)]
    exact (continuousOn_zpow₀ _).mono fun _ hu => (hy.trans_le hu.1).ne'
  exact hf.intervalIntegrable.continuousOn_mul hk

private theorem cumulative_square_mono : Monotone (cumulative squareCoeff) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hab)
  · intro n _ _
    classical
    unfold squareCoeff powerCoeff
    split_ifs <;> simp

/-- The model constant follows from the ordinary θ form of the prime number theorem. -/
theorem square_limit_of_theta (pnt : Chebyshev.theta ~[atTop] id) :
    Tendsto (fun y => windowSum squareCoeff y / sqrt y) atTop (𝓝 squareBias) := by
  have hmodel : (fun u => Chebyshev.theta (sqrt u)) ~[atTop] sqrt :=
    pnt.comp_tendsto Real.tendsto_sqrt_atTop
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := eventually_atTop.1 (hmodel.bound (show 0 < ε/16 by linarith))
  filter_upwards [eventually_ge_atTop A, eventually_gt_atTop (0:ℝ)] with y hAy hy
  have hroot : 0 < sqrt y := sqrt_pos.2 hy
  have hroot8 : sqrt (8*y) ≤ 4*sqrt y := by
    rw [Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ hroot.le
    exact (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  have bound := tent_uniform (f := fun u => cumulative squareCoeff u - sqrt u)
    (Y := y) (y := y) (M := ε/16*(4*sqrt y)) hy (by
      intro u hu
      have hu' : 0 ≤ u := hy.le.trans hu.1
      rw [cumulative_squares hu']
      have h := hA u (hAy.trans hu.1)
      change ‖Chebyshev.theta (sqrt u) - sqrt u‖ ≤ ε/16 * ‖sqrt u‖ at h
      rw [show ‖sqrt u‖ = sqrt u by simp] at h
      exact h.trans (mul_le_mul_of_nonneg_left ((sqrt_le_sqrt hu.2).trans hroot8) (by positivity)))
    ⟨le_rfl, by linarith⟩
  have h2y : 0 < 2*y := by linarith
  rw [tent_sub (weighted_mono_integrable cumulative_square_mono hy)
      (weighted_mono_integrable Real.sqrt_monotone hy)
      (weighted_mono_integrable cumulative_square_mono h2y)
      (weighted_mono_integrable Real.sqrt_monotone h2y)] at bound
  have he : -tent (cumulative squareCoeff) y / sqrt y - squareBias =
      -(tent (cumulative squareCoeff) y - tent sqrt y) / sqrt y := by
    apply (eq_div_iff hroot.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hroot.ne', ← neg_tent_sqrt hy]
    ring
  rw [Real.dist_eq, windowSum_eq_neg_tent squareCoeff hy, he, abs_div, abs_neg, abs_of_pos hroot]
  apply (div_lt_iff₀ hroot).mpr
  rw [Real.norm_eq_abs] at bound
  nlinarith only [bound, mul_pos hε hroot]

end PrimeWindowDiscrete

#print axioms PrimeWindowDiscrete.neg_tent_sqrt
#print axioms PrimeWindowDiscrete.square_limit_of_theta
