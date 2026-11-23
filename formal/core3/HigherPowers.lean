import DiscreteTent

/-! A cube-root bound for the contribution of prime powers of exponent at least three. -/
namespace PrimeWindowDiscrete

open Set Filter Real PrimeWindowTransfer
open scoped ArithmeticFunction Topology

/-- Squaring gives a bijection between primes up to √x and prime squares up to x. -/
theorem cumulative_squares {x : ℝ} (hx : 0 ≤ x) :
    cumulative squareCoeff x = Chebyshev.theta (sqrt x) := by
  classical
  rw [cumulative, Chebyshev.theta_eq_sum_Icc]
  let A := (Finset.Icc 0 ⌊x⌋₊).filter IsPrimeSquare
  have hf : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, squareCoeff n = ∑ n ∈ A, squareCoeff n := by
    simp only [A, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hs : IsPrimeSquare n <;> simp [hs, squareCoeff]
  rw [hf, eq_comm]
  apply Finset.sum_bij (fun (p : ℕ) _ => p^2)
  · intro p hp
    obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
    have hp' := (Nat.le_floor_iff (sqrt_nonneg x)).mp (Finset.mem_Icc.mp hpI).2
    have hs := (Real.le_sqrt (Nat.cast_nonneg p) hx).mp hp'
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,
      (Nat.le_floor_iff hx).mpr (by exact_mod_cast hs)⟩, p, hprime, rfl⟩
  · intro a ha b hb hab
    exact (Nat.pow_left_injective (by decide : 2 ≠ 0)) hab
  · intro n hn
    obtain ⟨hnI, p, hp, rfl⟩ := Finset.mem_filter.mp hn
    have hn' := (Nat.le_floor_iff hx).mp (Finset.mem_Icc.mp hnI).2
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hp⟩, rfl⟩
    apply (Nat.le_floor_iff (sqrt_nonneg x)).mpr
    apply (Real.le_sqrt (Nat.cast_nonneg p) hx).mpr
    exact_mod_cast hn'
  · intro p hp
    exact (squareCoeff_at_square (Finset.mem_filter.mp hp).2).symm

private theorem cum_split (x : ℝ) :
    cumulative higherCoeff x =
      Chebyshev.psi x - Chebyshev.theta x - cumulative squareCoeff x := by
  classical
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, cumulative,
    cumulative, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> by_cases hs : IsPrimeSquare n <;>
    simp [squareCoeff, higherCoeff, powerCoeff, hp, hs, ArithmeticFunction.vonMangoldt_apply_prime]

private theorem higher_nonneg (n : ℕ) : 0 ≤ higherCoeff n := by
  classical
  unfold higherCoeff powerCoeff
  split_ifs <;> simp

/-- The unsmoothed cumulative higher powers already satisfy a cube-root bound. -/
theorem cumulative_higher_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → cumulative higherCoeff x ≤ C*x^(1/3 : ℝ) := by
  obtain ⟨B, hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K := Real.log 4 + 4
  refine ⟨|B| + 2*K, by dsimp [K]; positivity, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hk : 0 ≤ K := by unfold K; positivity
  have hbase := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hid : x^(2:ℝ)⁻¹ = sqrt x := by rw [sqrt_eq_rpow, one_div]
  rw [hid] at hbase
  have hthree := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx0 (3:ℝ)⁻¹)
  have hfive := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx0 (5:ℝ)⁻¹)
  change _ ≤ K * _ at hthree hfive
  have h53 : x^(5:ℝ)⁻¹ ≤ x^(1/3:ℝ) := rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hquarter : sqrt (sqrt x) ≤ x^(1/3:ℝ) := by
    simp only [sqrt_eq_rpow, ← rpow_mul hx0]
    exact rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hsmall := calc
    Chebyshev.psi (sqrt x) - Chebyshev.theta (sqrt x) ≤ B*sqrt (sqrt x) := hB _
    _ ≤ |B| * sqrt (sqrt x) := by gcongr; exact le_abs_self _
    _ ≤ |B| * x^(1/3:ℝ) := mul_le_mul_of_nonneg_left hquarter (abs_nonneg _)
  rw [cum_split, cumulative_squares hx0]
  rw [← one_div (3:ℝ)] at hthree hbase
  linarith [mul_le_mul_of_nonneg_left h53 hk]

/-- On each half, the tent weights are bounded above by one. -/
private theorem window_le_twice_cumulative {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n)
    {y : ℝ} (hy : 0 < y) : windowSum c y ≤ 2*cumulative c (4*y) := by
  have half {a b k d : ℝ} (hb : b ≤ 4*y)
      (hw : ∀ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, side k d n ≤ 1) :
      halfSum c a b k d ≤ cumulative c (4*y) := by
    apply le_trans (Finset.sum_le_sum fun n hn => (mul_le_mul_of_nonneg_right (hw n hn) (hc n)).trans_eq (one_mul _))
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun n _ _ => hc n)
    intro n hn
    exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Ioc.mp hn).2.trans (Nat.floor_le_floor hb)⟩
  have hl : halfSum c y (2*y) (-2*y) 2 ≤ cumulative c (4*y) := by
    apply half (by linarith)
    intro n hn
    have h := Finset.mem_Ioc.mp hn
    have hu := (Nat.le_floor_iff (show 0 ≤ 2*y by linarith)).mp h.2
    have hl := (Nat.floor_lt hy.le).mp h.1
    rw [side, ← div_eq_mul_inv]
    have := (div_le_iff₀ (hy.trans hl)).mpr (show -2*y ≤ -1*(n:ℝ) by linarith)
    linarith
  have hr : halfSum c (2*y) (4*y) (4*y) (-1) ≤ cumulative c (4*y) := by
    apply half le_rfl
    intro n hn
    have hl := (Nat.floor_lt (show 0 ≤ 2*y by linarith)).mp (Finset.mem_Ioc.mp hn).1
    have hn' : 0 < (n:ℝ) := by linarith
    rw [side, ← div_eq_mul_inv]
    have := (div_le_iff₀ hn').mpr (show 4*y ≤ 2*(n:ℝ) by linarith)
    linarith
  unfold windowSum
  linarith

theorem higher_window_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
      0 ≤ windowSum higherCoeff y ∧ windowSum higherCoeff y ≤ C*y^(1/3 : ℝ) := by
  obtain ⟨C, hC, h⟩ := cumulative_higher_bound
  refine ⟨2*C*(4:ℝ)^(1/3:ℝ), by positivity, ?_⟩
  intro y hy
  have hy' : 0 < y := by linarith
  refine ⟨windowSum_nonneg higher_nonneg hy', ?_⟩
  have ht := window_le_twice_cumulative higher_nonneg hy'
  have hu := h (4*y) (by linarith)
  rw [Real.mul_rpow (by norm_num) hy'.le] at hu
  linarith

/-- All exponents ≥3 contribute o(√y), at every sufficiently large real scale. -/
theorem higher_window_vanishing :
    Filter.Tendsto (fun y : ℝ => windowSum higherCoeff y / sqrt y) atTop (𝓝 0) := by
  obtain ⟨C, hC, h⟩ := higher_window_bound
  apply squeeze_zero' _ _ (show Tendsto (fun y : ℝ => C * y^(-(1/6) : ℝ)) atTop (𝓝 0) by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : 0 < (1/6 : ℝ))).const_mul C)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    exact div_nonneg (h y hy).1 (sqrt_nonneg y)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have hp : 0 < y := by linarith
    apply (div_le_div_of_nonneg_right (h y hy).2 (sqrt_nonneg y)).trans_eq
    rw [sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hp]
    norm_num

end PrimeWindowDiscrete
