import QuarticChord.Scale
import QuarticChord.CountWeight

/-! From the prime count in Guth–Maynard, Corollary 1.3 (at ε = 1/20),
to the dilated θ estimate. The prime-count theorem itself is an explicit input. -/

namespace QuarticChord

open Set Filter Topology

/-- Count ordinary primes in (z,z+h]. Only the fixed ε = 1/20 instance is used. -/
def GuthMaynardPrimeCount : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z : ℝ in atTop,
    ∀ h ∈ Icc (z ^ (17/30 + 1/20 : ℝ)) (z ^ (99/100 : ℝ)),
      |((Nat.primeCounting ⌊z+h⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊) - h / Real.log z| ≤ C * h * Real.exp (-((Real.log z) ^ (1/4 : ℝ)))

/-- The exponential saving still beats any prescribed log power after weighting by log z. -/
private theorem count_saving (m : ℝ) :
    ∀ᶠ z : ℝ in atTop, Real.exp (-((Real.log z) ^ (1/4 : ℝ))) * Real.log z
      ≤ 1 / (Real.log z)^m := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp Real.tendsto_log_atTop
  have hp := (isLittleO_rpow_exp_atTop (4*(m+1))).bound (by norm_num : (0:ℝ) < 1)
  filter_upwards [ht.eventually hp, eventually_gt_atTop (1:ℝ)] with z hz hzone
  have hl := Real.log_pos hzone
  let t := (Real.log z) ^ (1/4 : ℝ)
  have htpos : 0 < t := Real.rpow_pos_of_pos hl _
  have hb : t ^ (4*(m+1)) ≤ Real.exp t := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _),
      abs_of_pos (Real.exp_pos t), one_mul, t] using hz
  have he : (Real.log z)^m * Real.log z ≤ Real.exp t := by
    dsimp [t] at hb
    rw [← Real.rpow_mul hl.le, show (1/4 : ℝ)*(4*(m+1)) = m+1 by ring,
      Real.rpow_add_one hl.ne'] at hb
    exact hb
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hl m), Real.exp_neg, inv_mul_eq_div,
    div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos _), one_mul, mul_comm]
  exact he

private theorem short_count_error {z h n θ : ℝ} (hz : 1 ≤ z) (hl : 1 ≤ Real.log z)
    (hlog : Real.log z ≤ z ^ (1/30 : ℝ)) (hh : h ≤ z^(2/3 : ℝ))
    (hn : 0 ≤ n) (hcard : n ≤ h+1) (hlo : n * Real.log z ≤ θ)
    (hhi : θ ≤ n * (Real.log z + h/z)) (hh0 : 0 ≤ h) :
    |θ-h| ≤ 4 * z^(7/10 : ℝ) := by
  have zp := zero_lt_one.trans_le hz
  have h1 := Real.one_le_rpow hz (by norm_num : (0:ℝ) ≤ 2/3)
  have hhz : h ≤ z := hh.trans (by simpa using
    Real.rpow_le_rpow_of_exponent_le hz (by norm_num : (2/3:ℝ) ≤ 1))
  have hn' : n ≤ 2*z^(2/3 : ℝ) := by linarith
  have hl' : Real.log z + h/z ≤ 2 * z^(1/30 : ℝ) := by
    linarith [(div_le_one zp).2 hhz]
  have hθ := hhi.trans (mul_le_mul hn' hl' (by positivity) (by positivity))
  have prod : 2*z^(2/3:ℝ) * (2*z^(1/30:ℝ)) = 4*z^(7/10:ℝ) := by
    rw [show (7/10:ℝ) = 2/3+1/30 by norm_num, Real.rpow_add zp]
    ring
  rw [prod] at hθ
  apply abs_le.mpr
  have := hh.trans (Real.rpow_le_rpow_of_exponent_le hz (by norm_num : (2/3:ℝ) ≤ 7/10))
  have := (mul_nonneg hn (by linarith : 0 ≤ Real.log z)).trans hlo
  constructor <;> linarith [Real.rpow_nonneg zp.le (7/10:ℝ)]

private theorem long_count_error {C m z h n θ : ℝ} (hz : 1 < z)
    (hsave : Real.exp (-((Real.log z) ^ (1/4 : ℝ))) * Real.log z ≤ 1/(Real.log z)^m)
    (hlog : (Real.log z)^m ≤ z^(1/100:ℝ)) (hC : 0 ≤ C)
    (hh1 : 1 ≤ h) (hupper : h ≤ z^(99/100:ℝ))
    (hcard : n ≤ h+1) (hlo : n * Real.log z ≤ θ) (hhi : θ ≤ n * (Real.log z + h/z))
    (hcount : |n - h / Real.log z| ≤ C*h*Real.exp (-((Real.log z) ^ (1/4 : ℝ)))) :
    |θ-h| ≤ (C+2)*h/(Real.log z)^m := by
  have hl := Real.log_pos hz
  have zp := zero_lt_one.trans hz
  have hp := Real.rpow_pos_of_pos hl m
  have hh : 0 ≤ h := by linarith
  have main : |n*Real.log z-h| ≤ C*h/(Real.log z)^m := by
    calc
      _ = |n-h/Real.log z| * Real.log z := by
        rw [← abs_of_pos hl, ← abs_mul, abs_of_pos hl, sub_mul, div_mul_cancel₀ _ hl.ne']
      _ ≤ C*h * (Real.exp (-((Real.log z) ^ (1/4 : ℝ))) * Real.log z) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcount hl.le
      _ ≤ _ := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hsave (mul_nonneg hC hh)
  have hratio : h/z ≤ 1/(Real.log z)^m := by
    rw [div_le_div_iff₀ zp hp, one_mul]
    calc
      _ ≤ z^(99/100:ℝ) * z^(1/100:ℝ) := mul_le_mul hupper hlog hp.le (by positivity)
      _ = z := by rw [← Real.rpow_add zp]; norm_num
  have drift := mul_le_mul (by linarith : n ≤ 2*h) hratio (div_nonneg hh zp.le) (by positivity)
  rw [mul_add] at hhi
  rcases abs_le.mp main with ⟨h1,h2⟩
  rw [add_mul, add_div]
  apply abs_le.mpr
  constructor
  · linarith [show 0 ≤ 2*h/(Real.log z)^m by positivity]
  · linarith only [hhi, h2, drift, show 2*h*(1/(Real.log z)^m) = 2*h/(Real.log z)^m by ring]

/-- Only the longer offsets call Corollary 1.3. Integer counting suffices below
`z^(2/3)`, with room to spare compared with the quartic width. -/
private theorem local_theta_estimate (gm : GuthMaynardPrimeCount) (m : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ z : ℝ in atTop, ∀ A d u : ℝ,
      0 < A → 0 < d → 0 ≤ u → A/d = z → u/d ≤ z^(99/100 : ℝ) →
      |thetaMass A d u - u/d| ≤ 4*z^(7/10:ℝ) + D*(u/d)/(Real.log z)^m := by
  obtain ⟨C,hC,hgm⟩ := gm
  refine ⟨C+2, by linarith, ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    count_saving m, eventually_logpow_le_rpow m (1/100) (by norm_num),
    eventually_logpow_le_rpow 1 (1/30) (by norm_num), hgm] with z hz hl hsave hpow hlog hc
  intro A d u hA hd hu heq hupper
  let h := u/d
  let θ := thetaMass A d u
  have h0 : 0 ≤ h := div_nonneg hu hd.le
  have bounds := count_weight_bounds hA hd hu
  dsimp only at bounds
  rw [heq] at bounds
  obtain ⟨hlo,hhi,hcard⟩ := bounds
  change |θ-h| ≤ 4*z^(7/10:ℝ) + (C+2)*h/(Real.log z)^m
  by_cases hsmall : h ≤ z^(2/3:ℝ)
  · have hs := short_count_error hz.le hl (by simpa using hlog) hsmall
      (primeCount_nonneg z h) hcard hlo hhi h0
    exact hs.trans (le_add_of_nonneg_right (by positivity))
  · have hlow := (Real.rpow_le_rpow_of_exponent_le hz.le
        (by norm_num : (17/30+1/20:ℝ) ≤ 2/3)).trans (le_of_not_ge hsmall)
    have h1 := (Real.one_le_rpow hz.le (by norm_num : (0:ℝ) ≤ 2/3)).trans (le_of_not_ge hsmall)
    have hs := long_count_error hz hsave hpow hC h1 hupper hcard hlo hhi (by
      rw [primeCount_eq_primeCounting_sub z h h0]
      exact hc h ⟨hlow,hupper⟩)
    exact hs.trans (le_add_of_nonneg_left (by positivity))

/-- The θ hypothesis needed by Abel summation follows from the stated prime-count
estimate for every fixed width exponent and logarithmic saving. -/
theorem GuthMaynardPrimeCount.shortInterval (gm : GuthMaynardPrimeCount)
    (B m : ℝ) (hB : 0 ≤ B) (hm : 0 < m) : ShortIntervalPrimeEstimate B m := by
  obtain ⟨D,hD,hd⟩ := local_theta_estimate gm m
  exact shortIntervalPrimeEstimate_of_local hB hm hD hd

end QuarticChord
