import SquareKernel
import PrimeNumberTheoremAnd.Wiener

/-! A prime number theorem with no RH hypothesis supplies the ordinary-prime square bias. -/
namespace PrimeWindowDiscrete

open Filter Real Asymptotics
open scoped Topology ArithmeticFunction

/-- The upstream sum counts n < N. The shift N = ⌊x⌋+1 includes a jump at x. -/
private theorem psi_ratio :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  have hN := WeakPNT.comp ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
  have hshift : Tendsto (fun x : ℝ => (↑⌊x⌋₊ + 1) / x) atTop (𝓝 1) := by
    simpa only [add_div, one_div, add_zero] using
      (tendsto_nat_floor_div_atTop (R := ℝ)).add (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hprod := hN.mul hshift
  rw [one_mul] at hprod
  apply hprod.congr'
  filter_upwards with x
  change cumsum (fun n => Λ n) (⌊x⌋₊ + 1) / ((⌊x⌋₊ + 1 : ℕ) : ℝ) *
    ((↑⌊x⌋₊ + 1) / x) = Chebyshev.psi x / x
  rw [cumsum, Nat.range_succ_eq_Icc_zero, ← Chebyshev.psi_eq_sum_Icc, Nat.cast_add_one]
  have hpos : 0 < (⌊x⌋₊ : ℝ) + 1 := by positivity
  field_simp

/-- Removing prime powers from ψ changes its ratio to x by a quantity tending to zero. -/
theorem theta_ratio : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  obtain ⟨B, hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hsmall : Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (show Tendsto (fun x : ℝ => B * (sqrt x)⁻¹) atTop (𝓝 0) by
      simpa using (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul B)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x)) hx.le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simpa only [mul_div_assoc, Real.sqrt_div_self] using
        div_le_div_of_nonneg_right (hB x) hx.le
  have h := psi_ratio.sub hsmall
  simpa only [sub_div, sub_sub_cancel, sub_zero] using h

theorem square_window_limit :
    Tendsto (fun y => windowSum squareCoeff y / sqrt y) atTop (𝓝 (6 * sqrt 2 - 8)) :=
  square_limit_of_theta (isEquivalent_of_tendsto_one theta_ratio)

/-- Pointwise convergence at infinity gives the same error tolerance throughout each late doubling. -/
theorem square_window_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y in atTop, ∀ y ∈ Set.Icc Y (2*Y),
      |windowSum squareCoeff y / sqrt y - squareBias| < ε := by
  intro ε hε
  obtain ⟨A, hA⟩ := eventually_atTop.1 (Metric.tendsto_nhds.mp square_window_limit ε hε)
  filter_upwards [eventually_ge_atTop A] with Y hY
  intro y hy
  exact hA y (hY.trans hy.1)

end PrimeWindowDiscrete

#print axioms WeakPNT
#print axioms PrimeWindowDiscrete.theta_ratio
#print axioms PrimeWindowDiscrete.square_window_limit
#print axioms PrimeWindowDiscrete.square_window_uniform
