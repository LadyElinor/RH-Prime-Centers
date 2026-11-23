import TentTransfer
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-! Abel summation on the two halves of the ordinary-prime tent. -/
namespace PrimeWindowDiscrete

open Set MeasureTheory PrimeWindowTransfer
open scoped Interval ArithmeticFunction

/-- On either half of the tent the weight has the form k / x + b. -/
noncomputable def side (k b x : ℝ) : ℝ := k * x⁻¹ + b

noncomputable def halfSum (c : ℕ → ℝ) (a b k d : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, side k d n * c n

/-- The lower cut is strict and the upper cut is inclusive on each half. -/
noncomputable def windowSum (c : ℕ → ℝ) (y : ℝ) : ℝ :=
  halfSum c y (2*y) (-2*y) 2 + halfSum c (2*y) (4*y) (4*y) (-1)

noncomputable def cumulative (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n

set_option backward.isDefEq.respectTransparency false in
private theorem side_deriv (k d : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (side k d) ((-k) * x^(-2 : ℤ)) x := by
  unfold side
  convert! (((hasDerivAt_inv hx.ne').const_mul k).add_const d) using 1
  simp [zpow_neg]

private theorem abel_half (c : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (k d : ℝ) :
    halfSum c a b k d = side k d b * cumulative c b - side k d a * cumulative c a +
      k * ∫ t in a..b, weighted (cumulative c) t := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) := side_deriv k d (ha.trans_le ht.1)
  have hk : ContinuousOn (fun x : ℝ => (-k) * x^(-2 : ℤ)) (Icc a b) :=
    continuousOn_const.mul ((continuousOn_zpow₀ _).mono fun _ hx => (ha.trans_le hx.1).ne')
  have hi : IntegrableOn (deriv (side k d)) (Icc a b) :=
    (hk.congr fun t ht => (hd t ht).deriv).integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c ha.le hab (fun t ht => (hd t ht).differentiableAt) hi
  change halfSum c a b k d = side k d b * cumulative c b - side k d a * cumulative c a -
    ∫ t in Ioc a b, deriv (side k d) t * cumulative c t at h
  rw [← intervalIntegral.integral_of_le hab] at h
  have hI : (∫ t in a..b, deriv (side k d) t * cumulative c t) =
      (-k) * ∫ t in a..b, weighted (cumulative c) t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    dsimp only
    rw [(hd t ht).deriv, weighted, smul_eq_mul, mul_assoc]
  rw [h, hI]
  ring

/-- Both half-sums have the same boundary term at 2y. It cancels in Abel summation. -/
theorem windowSum_eq_neg_tent (c : ℕ → ℝ) {y : ℝ} (hy : 0 < y) :
    windowSum c y = -tent (cumulative c) y := by
  rw [windowSum, abel_half c hy (by linarith),
    abel_half c (show 0 < 2*y by linarith) (by linarith)]
  have hA : side (-2*y) 2 y = 0 := by unfold side; field_simp; ring
  have hB : side (-2*y) 2 (2*y) = 1 := by unfold side; field_simp; ring
  have hC : side (4*y) (-1) (2*y) = 1 := by unfold side; field_simp; ring
  have hD : side (4*y) (-1) (4*y) = 0 := by unfold side; field_simp; ring
  rw [hA, hB, hC, hD]
  simp only [tent, PrimeWindowTransfer.average, smul_eq_mul, show 2*(2*y) = 4*y by ring]
  ring

noncomputable def primeCoeff (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

/-- Exactly the von Mangoldt mass omitted by the restriction to ordinary primes. -/
noncomputable def powerCoeff (n : ℕ) : ℝ := if n.Prime then 0 else Λ n

theorem windowSum_add (c d : ℕ → ℝ) (y : ℝ) :
    windowSum (fun n => c n + d n) y = windowSum c y + windowSum d y := by
  simp only [windowSum, halfSum, mul_add, Finset.sum_add_distrib]
  ring

theorem split_prime_powers (y : ℝ) :
    windowSum (fun n => Λ n) y = windowSum primeCoeff y + windowSum powerCoeff y := by
  rw [← windowSum_add]
  congr 1
  funext n
  by_cases hp : n.Prime <;> simp [primeCoeff, powerCoeff, hp, ArithmeticFunction.vonMangoldt_apply_prime]

private theorem cuts {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) : a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  obtain ⟨hl, hr⟩ := Finset.mem_Ioc.mp hn
  exact ⟨(Nat.floor_lt ha).mp hl, (Nat.le_floor_iff (ha.trans hab)).mp hr⟩

theorem windowSum_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {y : ℝ} (hy : 0 < y) :
    0 ≤ windowSum c y := by
  unfold windowSum halfSum
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro n hn <;> apply mul_nonneg _ (hc n)
  · obtain ⟨hl, _⟩ := cuts hy.le (show y ≤ 2*y by linarith) hn
    have hn' := hy.trans hl
    rw [side, ← div_eq_mul_inv]
    have := (le_div_iff₀ hn').mpr (show (-2)*(n:ℝ) ≤ -2*y by linarith)
    linarith
  · obtain ⟨hl, hr⟩ := cuts (show 0 ≤ 2*y by linarith) (show 2*y ≤ 4*y by linarith) hn
    have hn' : 0 < (n:ℝ) := by linarith
    rw [side, ← div_eq_mul_inv]
    have := (le_div_iff₀ hn').mpr (show 1*(n:ℝ) ≤ 4*y by linarith)
    linarith

theorem omitted_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ windowSum powerCoeff y :=
  windowSum_nonneg (fun n => by unfold powerCoeff; split <;> simp) hy

/-- The omitted coefficient is positive precisely at nonprime prime powers. -/
theorem powerCoeff_pos_iff (n : ℕ) : 0 < powerCoeff n ↔ IsPrimePow n ∧ ¬n.Prime := by
  by_cases hp : n.Prime <;> simp [powerCoeff, hp, ArithmeticFunction.vonMangoldt_pos_iff]

/-- Separate prime squares from all higher prime powers, including fourth powers. -/
def IsPrimeSquare (n : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ p^2 = n

noncomputable def squareCoeff (n : ℕ) : ℝ := by
  classical exact if IsPrimeSquare n then powerCoeff n else 0

noncomputable def higherCoeff (n : ℕ) : ℝ := by
  classical exact if IsPrimeSquare n then 0 else powerCoeff n

theorem squareCoeff_at_square {p : ℕ} (hp : p.Prime) :
    squareCoeff (p^2) = Real.log p := by
  have hs : IsPrimeSquare (p^2) := ⟨p, hp, rfl⟩
  have hn : ¬(p^2).Prime := Nat.Prime.not_prime_pow (by decide)
  simp [squareCoeff, hs, powerCoeff, hn, ArithmeticFunction.vonMangoldt_apply_pow,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

theorem higherCoeff_pos_iff (n : ℕ) :
    0 < higherCoeff n ↔ ∃ (p k : ℕ), p.Prime ∧ 3 ≤ k ∧ p^k = n := by
  classical
  constructor
  · intro h
    by_cases hs : IsPrimeSquare n
    · simp [higherCoeff, hs] at h
    have hpw := (powerCoeff_pos_iff n).mp (by simpa [higherCoeff, hs] using h)
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpw.1
    refine ⟨p, k, hp, ?_, rfl⟩
    by_contra! hsmall
    have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl
    · exact hpw.2 (by simpa using hp)
    · exact hs ⟨p, hp, rfl⟩
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hs : ¬IsPrimeSquare (p^k) := by
      rintro ⟨q, hq, he⟩
      have := (hq.pow_inj' hp (by decide) (by omega) he).2
      omega
    have hn : ¬(p^k).Prime := Nat.Prime.not_prime_pow (by omega)
    have hpp : IsPrimePow (p^k) := (isPrimePow_nat_iff _).mpr ⟨p, k, hp, by omega, rfl⟩
    simp [higherCoeff, hs, powerCoeff_pos_iff, hn, hpp]

theorem split_squares_higher (y : ℝ) :
    windowSum powerCoeff y = windowSum squareCoeff y + windowSum higherCoeff y := by
  rw [← windowSum_add]
  congr 1
  funext n
  by_cases h : IsPrimeSquare n <;> simp [squareCoeff, higherCoeff, h]

private theorem weighted_integrable {f : ℝ → ℝ} (hf : Monotone f) {y : ℝ} (hy : 0 < y) :
    IntervalIntegrable (weighted f) volume y (2*y) := by
  have hk : ContinuousOn (fun u : ℝ => u^(-2 : ℤ)) [[y,2*y]] := by
    rw [uIcc_of_le (by linarith)]
    exact (continuousOn_zpow₀ _).mono fun u hu => (hy.trans_le hu.1).ne'
  exact hf.intervalIntegrable.continuousOn_mul hk

private theorem average_id {y : ℝ} (hy : 0 < y) :
    PrimeWindowTransfer.average (fun u : ℝ => u) y = y * Real.log 2 := by
  have h : weighted (fun u : ℝ => u) = fun u => u⁻¹ := by
    funext u
    by_cases hz : u = 0
    · simp [weighted, hz]
    · simp [weighted, zpow_neg, sq, mul_inv_rev, hz]
  rw [PrimeWindowTransfer.average, h, integral_inv_of_pos hy (by linarith), smul_eq_mul]
  rw [mul_div_cancel_right₀ _ hy.ne']

theorem primePower_identity {y : ℝ} (hy : 0 < y) :
    tent (fun u : ℝ => Chebyshev.psi u - u) y =
      2*y*Real.log 2 - windowSum (fun n => Λ n) y := by
  have hcum : cumulative (fun n => Λ n) = Chebyshev.psi :=
    funext fun u => (Chebyshev.psi_eq_sum_Icc u).symm
  have h := windowSum_eq_neg_tent (fun n => Λ n) hy
  rw [hcum] at h
  have h2 : 0 < 2*y := by linarith
  change tent (fun u => Chebyshev.psi u - id u) y = _
  rw [tent_sub (weighted_integrable Chebyshev.psi_mono hy) (weighted_integrable monotone_id hy)
        (weighted_integrable Chebyshev.psi_mono h2) (weighted_integrable monotone_id h2)]
  have ht : tent (fun u : ℝ => u) y = -(2*y*Real.log 2) := by
    rw [tent, average_id hy, average_id h2, smul_eq_mul]
    ring
  change tent Chebyshev.psi y - tent (fun u : ℝ => u) y = _
  rw [ht, h]; ring

theorem tent_ofReal (f : ℝ → ℝ) (y : ℝ) :
    tent (fun u => (f u : ℂ)) y = ((tent f y : ℝ) : ℂ) := by
  simp only [tent, PrimeWindowTransfer.average, weighted, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_ofNat]
  simp only [← Complex.ofReal_mul, intervalIntegral.integral_ofReal]

theorem ordinary_prime_identity {y : ℝ} (hy : 0 < y) :
    2*y*Real.log 2 - windowSum primeCoeff y =
      tent (fun u : ℝ => Chebyshev.psi u - u) y + windowSum powerCoeff y := by
  rw [primePower_identity hy, split_prime_powers]; ring

end PrimeWindowDiscrete
