import SquareBias
import OrdinaryFormula

/-! Normalize the ordinary-prime formula by its explicit prime-square bias. -/
namespace PrimeWindowCore3

open PrimeWindowDiscrete Filter Set Real
open scoped Topology

/-- One fixed zero cutoff works for the whole doubling, with an explicit real bias. -/
theorem bias_tent_vanishing :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y in atTop, ∀ y ∈ Icc Y (2*Y),
      ‖(ordinaryDeficit y : ℂ) - (spectrum Y y + ((squareBias * sqrt y : ℝ) : ℂ))‖ /
        sqrt y < ε := by
  intro ε hε
  have he : 0 < ε/2 := by linarith
  filter_upwards [eventually_gt_atTop (0:ℝ), square_tent_vanishing _ he,
    square_window_uniform _ he] with Y hY hzero hsquare
  intro y hy
  have hp := sqrt_pos.2 (hY.trans_le hy.1)
  let r : ℂ := (ordinaryDeficit y : ℂ) - (spectrum Y y + (windowSum squareCoeff y : ℝ))
  let q := windowSum squareCoeff y - squareBias * sqrt y
  have herr : (ordinaryDeficit y : ℂ) - (spectrum Y y + ((squareBias * sqrt y : ℝ) : ℂ)) =
      r + (q : ℂ) := by dsimp [r, q]; push_cast; ring
  have hq : |q| / sqrt y < ε/2 := by
    have := hsquare y hy
    rwa [show windowSum squareCoeff y / sqrt y - squareBias = q / sqrt y by
      dsimp [q]; rw [sub_div, mul_div_cancel_right₀ _ hp.ne'], abs_div, abs_of_pos hp] at this
  rw [herr]
  apply (div_le_div_of_nonneg_right (norm_add_le r (q:ℂ)) hp.le).trans_lt
  rw [add_div, Complex.norm_real, Real.norm_eq_abs]
  linarith [show ‖r‖ / sqrt y < ε/2 from hzero y hy]

/-- Real-part form for sign comparisons. The normalized real zero sum can be used directly. -/
theorem signed_bias_vanishing :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y in atTop, ∀ y ∈ Icc Y (2*Y),
      |ordinaryDeficit y / sqrt y - ((spectrum Y y).re / sqrt y + squareBias)| < ε := by
  intro ε hε
  filter_upwards [eventually_gt_atTop (0:ℝ), bias_tent_vanishing ε hε] with Y hY h
  intro y hy
  have hp := sqrt_pos.2 (hY.trans_le hy.1)
  let z := (ordinaryDeficit y : ℂ) - (spectrum Y y + ((squareBias * sqrt y : ℝ) : ℂ))
  have he : z.re / sqrt y =
      ordinaryDeficit y / sqrt y - ((spectrum Y y).re / sqrt y + squareBias) := by
    simp only [z, Complex.sub_re, Complex.add_re, Complex.ofReal_re, sub_div, add_div,
      mul_div_cancel_right₀ _ hp.ne']
  rw [← he, abs_div, abs_of_pos hp]
  exact (div_le_div_of_nonneg_right (Complex.abs_re_le_norm z) hp.le).trans_lt (h y hy)

/-- A fixed spectral margin implies a positive ordinary-prime deficit throughout a late doubling. -/
theorem doubling_of_spectral_margin {η : ℝ} (hη : 0 < η) :
    ∀ᶠ Y in atTop, (∀ y ∈ Icc Y (2*Y), -squareBias + η ≤ (spectrum Y y).re / sqrt y) →
      ∀ y ∈ Icc Y (2*Y), η/2 < ordinaryDeficit y / sqrt y := by
  filter_upwards [signed_bias_vanishing (η/2) (by linarith)] with Y h
  intro hm y hy
  linarith [(abs_lt.mp (h y hy)).1, hm y hy]

/-- With a sliding cutoff y = x/4, a fixed positive spectral margin throughout arbitrarily
late power windows suffices for the ordinary-prime sign hypothesis on those same windows. -/
theorem power_windows_of_spectral_margin {δ η : ℝ} (hη : 0 < η)
    (windows : ∃ᶠ X : ℝ in atTop, ∀ x ∈ Icc X (X^(1+δ)),
      -squareBias + η ≤ (spectrum (x/4) (x/4)).re / sqrt (x/4)) :
    ∃ᶠ X : ℝ in atTop, ∀ x ∈ Icc X (X^(1+δ)), 0 < ordinaryDeficit (x/4) := by
  obtain ⟨A, hA⟩ := eventually_atTop.1 (signed_bias_vanishing (η/2) (by linarith))
  apply (windows.and_eventually (eventually_ge_atTop (4 * max A 1))).mono
  rintro X ⟨hwindow, hX⟩ x hx
  have hstart : A ≤ x/4 := by linarith [hx.1, le_max_left A 1]
  have hp : 0 < x/4 := by linarith [hx.1, le_max_right A 1]
  have h := hA (x/4) hstart (x/4) ⟨le_rfl, by linarith⟩
  have hratio : 0 < ordinaryDeficit (x/4) / sqrt (x/4) := by
    linarith [(abs_lt.mp h).1, hwindow x hx]
  exact (div_pos_iff_of_pos_right (sqrt_pos.2 hp)).mp hratio

end PrimeWindowCore3

#print axioms PrimeWindowCore3.bias_tent_vanishing
#print axioms PrimeWindowCore3.signed_bias_vanishing
#print axioms PrimeWindowCore3.doubling_of_spectral_margin
#print axioms PrimeWindowCore3.power_windows_of_spectral_margin
