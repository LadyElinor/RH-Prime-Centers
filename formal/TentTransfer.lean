import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Uniform propagation of a conductor-one explicit-formula error through the prime tent. -/
namespace PrimeWindowTransfer

open Set MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def weighted (f : ℝ → E) (u : ℝ) : E := u ^ (-2 : ℤ) • f u

noncomputable def average (f : ℝ → E) (y : ℝ) : E :=
  y • ∫ u in y..2*y, weighted f u

noncomputable def tent (f : ℝ → E) (y : ℝ) : E :=
  (2 : ℝ) • (average f y - average f (2*y))

/-- The positive kernel on a single dyadic interval has mass exactly one half. -/
theorem kernel_mass {y : ℝ} (hy : 0 < y) :
    y * (∫ u in y..2*y, u ^ (-2 : ℤ)) = 1/2 := by
  have hpos : (0 : ℝ) ∉ [[y, 2*y]] := by
    rw [uIcc_of_le (by linarith)]
    exact fun h => (not_le_of_gt hy) h.1
  rw [integral_zpow (Or.inr ⟨by norm_num, hpos⟩)]
  norm_num
  field_simp
  ring

theorem average_le {f : ℝ → E} {y M : ℝ} (hy : 0 < y)
    (bound : ∀ u ∈ Icc y (2*y), ‖f u‖ ≤ M) : ‖average f y‖ ≤ M/2 := by
  have hab : y ≤ 2*y := by linarith
  have hk : ContinuousOn (fun u : ℝ => u ^ (-2 : ℤ)) [[y, 2*y]] := by
    rw [uIcc_of_le hab]
    exact (continuousOn_zpow₀ (-2 : ℤ)).mono fun u hu => (hy.trans_le hu.1).ne'
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := weighted f) (g := fun u : ℝ => M * u^(-2 : ℤ)) hab
    (Filter.Eventually.of_forall fun u hu => by
      have hp : 0 < u := hy.trans hu.1
      rw [weighted, norm_smul, Real.norm_eq_abs, abs_of_pos (zpow_pos hp _) ]
      change _ ≤ M * u ^ (-2 : ℤ)
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (bound u ⟨hu.1.le, hu.2⟩) (zpow_pos hp _).le)
    ((continuousOn_const.mul hk).intervalIntegrable)
  rw [intervalIntegral.integral_const_mul] at h
  rw [average, norm_smul, Real.norm_eq_abs, abs_of_pos hy]
  calc
    _ ≤ y * (M * ∫ u in y..2*y, u ^ (-2 : ℤ)) := mul_le_mul_of_nonneg_left h hy.le
    _ = M * (y * ∫ u in y..2*y, u ^ (-2 : ℤ)) := by ring
    _ = M/2 := by rw [kernel_mass hy]; ring

/-- A single fixed bound on the input interval controls every sliding position. -/
theorem tent_uniform {f : ℝ → E} {Y M : ℝ} (hY : 0 < Y)
    (bound : ∀ u ∈ Icc Y (8*Y), ‖f u‖ ≤ M)
    {y : ℝ} (hy : y ∈ Icc Y (2*Y)) : ‖tent f y‖ ≤ 2*M := by
  have hp := hY.trans_le hy.1
  have h₁ := average_le hp (f := f) (M := M) fun u hu =>
    bound u ⟨hy.1.trans hu.1, by linarith [hu.2, hy.2]⟩
  have h₂ := average_le (show 0 < 2*y by positivity) (f := f) (M := M) fun u hu =>
    bound u ⟨by linarith [hy.1, hu.1], by linarith [hy.2, hu.2]⟩
  rw [tent, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith only [norm_sub_le (average f y) (average f (2*y)), h₁, h₂]

/-- Uniform envelope obtained by choosing the Core 3 truncation height T = Y. -/
noncomputable def envelope (C S Y : ℝ) : ℝ :=
  C * (8 * Real.log (8*Y^2)^2 + Real.log (8*Y) + S)

theorem core3_uniform {err : ℝ → E} {Y C S : ℝ} (hY : 2 ≤ Y) (hC : 0 ≤ C)
    (pointwise : ∀ u ∈ Icc Y (8*Y), ‖err u‖ ≤
      C * (u * Real.log (u*Y)^2 / Y + Real.log u + S))
    {y : ℝ} (hy : y ∈ Icc Y (2*Y)) : ‖tent err y‖ ≤ 2 * envelope C S Y := by
  apply tent_uniform (by linarith : 0 < Y) _ hy
  intro u hu
  have hp : 0 < Y := by linarith
  have hup : 0 < u := hp.trans_le hu.1
  have hprod : u*Y ≤ 8*Y^2 := by nlinarith [mul_le_mul_of_nonneg_right hu.2 hp.le]
  have hlog := Real.log_le_log (mul_pos hup hp) hprod
  have hnonneg : 0 ≤ Real.log (u*Y) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith [hu.1]) (by linarith))
  have hsquare := pow_le_pow_left₀ hnonneg hlog 2
  have hratio : u/Y ≤ 8 := (div_le_iff₀ hp).mpr hu.2
  have hterm := mul_le_mul hratio hsquare (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 8)
  have hlogu := Real.log_le_log hup hu.2
  apply (pointwise u hu).trans
  apply mul_le_mul_of_nonneg_left _ hC
  rw [show u * Real.log (u*Y)^2 / Y = u/Y * Real.log (u*Y)^2 by ring]
  linarith

/-- Subtracting two actual inputs commutes with the smoothing operation
when both weighted inputs are integrable on the interval. -/
theorem average_sub {f g : ℝ → E} {y : ℝ}
    (hf : IntervalIntegrable (weighted f) volume y (2*y))
    (hg : IntervalIntegrable (weighted g) volume y (2*y)) :
    average (fun u => f u - g u) y = average f y - average g y := by
  unfold weighted at hf hg
  simp only [average, weighted, smul_sub]
  rw [intervalIntegral.integral_sub hf hg, smul_sub]

theorem tent_sub {f g : ℝ → E} {y : ℝ}
    (hf₁ : IntervalIntegrable (weighted f) volume y (2*y))
    (hg₁ : IntervalIntegrable (weighted g) volume y (2*y))
    (hf₂ : IntervalIntegrable (weighted f) volume (2*y) (2*(2*y)))
    (hg₂ : IntervalIntegrable (weighted g) volume (2*y) (2*(2*y))) :
    tent (fun u => f u - g u) y = tent f y - tent g y := by
  simp only [tent, average_sub hf₁ hg₁, average_sub hf₂ hg₂, smul_sub]
  abel

/-- Equality in the factor-two bound is attained by a bounded real step. -/
theorem tent_sharp {y : ℝ} (hy : 0 < y) :
    ∃ f : ℝ → ℝ, (∀ u, ‖f u‖ ≤ 1) ∧ tent f y = 2 := by
  let f (u : ℝ) := if u ≤ 2*y then (1 : ℝ) else -1
  refine ⟨f, fun u => by dsimp [f]; split <;> norm_num, ?_⟩
  have h₁ : average f y = 1/2 := by
    unfold average
    rw [intervalIntegral.integral_congr_ae (g := fun u : ℝ => u^(-2 : ℤ)) ?_]
    · exact kernel_mass hy
    filter_upwards with u hu
    rw [uIoc_of_le (by linarith)] at hu
    simp [weighted, f, hu.2]
  have h₂ : average f (2*y) = -(1/2) := by
    unfold average
    rw [intervalIntegral.integral_congr_ae (g := fun u : ℝ => -(u^(-2 : ℤ))) ?_]
    · rw [intervalIntegral.integral_neg, smul_eq_mul, mul_neg, kernel_mass (by linarith)]
    filter_upwards with u hu
    rw [uIoc_of_le (by linarith)] at hu
    simp [weighted, f, not_le_of_gt hu.1]
  rw [tent, h₁, h₂]
  norm_num

/-- A signed term as it occurs in the conductor-one explicit formula. -/
noncomputable def zeroTerm (r : ℂ) (u : ℝ) : ℂ := -(u : ℂ)^r / r

noncomputable def coefficient (r : ℂ) : ℂ :=
  ((2 : ℂ)^r - 1) * ((2 : ℂ)^r - 2) / (r * (r-1))

private theorem weighted_zeroTerm {r : ℂ} {u : ℝ} (hu : 0 < u) :
    weighted (zeroTerm r) u = (-1 / r) * (u : ℂ)^(r-2) := by
  have h : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [weighted, zeroTerm, Complex.real_smul, Complex.ofReal_zpow,
    Complex.cpow_sub _ _ h, Complex.cpow_two]
  simp only [zpow_neg, zpow_ofNat]
  ring

private theorem zeroTerm_average {r : ℂ} (hr₀ : r ≠ 0) (hr₁ : r ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    average (zeroTerm r) y = -(y : ℂ)^r * ((2 : ℂ)^(r-1)-1) / (r*(r-1)) := by
  have hpos : (0 : ℝ) ∉ [[y, 2*y]] := by
    rw [uIcc_of_le (by linarith)]
    exact fun h => (not_le_of_gt hy) h.1
  have hpow : r-2 ≠ -1 := fun h => hr₁ (by linear_combination h)
  have hcast : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  unfold average
  rw [intervalIntegral.integral_congr (g := fun u : ℝ => (-1/r) * (u : ℂ)^(r-2)) ?_]
  · rw [intervalIntegral.integral_const_mul, integral_cpow (Or.inr ⟨hpow, hpos⟩),
      show r-2+1 = r-1 by ring, Complex.real_smul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 2) hy.le,
      Complex.cpow_sub r 1 hcast, Complex.cpow_one]
    push_cast
    field_simp [hcast, hr₀, sub_ne_zero.mpr hr₁]
  · intro u hu
    rw [uIcc_of_le (by linarith)] at hu
    exact weighted_zeroTerm (hy.trans_le hu.1)

/-- The signed coefficient of each complex zero after the two dyadic averages. -/
theorem tent_zeroTerm {r : ℂ} (hr₀ : r ≠ 0) (hr₁ : r ≠ 1) {y : ℝ} (hy : 0 < y) :
    tent (zeroTerm r) y = coefficient r * (y : ℂ)^r := by
  rw [tent, zeroTerm_average hr₀ hr₁ hy, zeroTerm_average hr₀ hr₁ (by positivity),
    Complex.real_smul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 2) hy.le]
  simp only [coefficient, Complex.ofReal_ofNat, Complex.cpow_sub r 1 (by norm_num : (2:ℂ) ≠ 0), Complex.cpow_one]
  ring

/-- Each index represents one occurrence, so repeated values of r encode multiplicity. -/
noncomputable def model {ι : Type*} (s : Finset ι) (r : ι → ℂ) (u : ℝ) : ℂ :=
  ∑ i ∈ s, zeroTerm (r i) u

private theorem zeroTerm_integrable (r : ℂ) {y : ℝ} (hy : 0 < y) :
    IntervalIntegrable (weighted (zeroTerm r)) volume y (2*y) := by
  have hpos : (0 : ℝ) ∉ [[y, 2*y]] := by
    rw [uIcc_of_le (by linarith)]
    exact fun h => (not_le_of_gt hy) h.1
  apply ((intervalIntegral.intervalIntegrable_cpow (μ := volume) (r := r-2) (Or.inr hpos)).const_mul (-1/r)).congr
  intro u hu
  rw [uIoc_of_le (by linarith)] at hu
  exact (weighted_zeroTerm (hy.trans hu.1)).symm

private theorem weighted_model {ι : Type*} (s : Finset ι) (r : ι → ℂ) :
    weighted (model s r) = ∑ i ∈ s, weighted (zeroTerm (r i)) := by
  funext u
  simp only [model, weighted, Finset.smul_sum, Finset.sum_apply]

private theorem model_integrable {ι : Type*} (s : Finset ι) (r : ι → ℂ) {y : ℝ}
    (hy : 0 < y) : IntervalIntegrable (weighted (model s r)) volume y (2*y) := by
  rw [weighted_model]
  exact IntervalIntegrable.sum s fun i _ => zeroTerm_integrable (r i) hy

private theorem model_average {ι : Type*} (s : Finset ι) (r : ι → ℂ) {y : ℝ}
    (hy : 0 < y) : average (model s r) y = ∑ i ∈ s, average (zeroTerm (r i)) y := by
  simp only [average, weighted_model, Finset.sum_apply]
  rw [intervalIntegral.integral_finset_sum (s := s) (fun i _ => zeroTerm_integrable (r i) hy), Finset.smul_sum]

theorem tent_model {ι : Type*} (s : Finset ι) (r : ι → ℂ)
    (hr : ∀ i ∈ s, r i ≠ 0 ∧ r i ≠ 1) {y : ℝ} (hy : 0 < y) :
    tent (model s r) y = ∑ i ∈ s, coefficient (r i) * (y : ℂ) ^ r i := by
  rw [tent, model_average s r hy, model_average s r (by positivity),
    ← Finset.sum_sub_distrib, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i hi => tent_zeroTerm (hr i hi).1 (hr i hi).2 hy

/-- Put the finite-sum identity and the uniform bound together. The hypotheses expose
the exact arithmetic input needed for a conductor-one specialization. -/
theorem finite_formula_transfer {ι : Type*} (s : Finset ι) (r : ι → ℂ)
    (hr : ∀ i ∈ s, r i ≠ 0 ∧ r i ≠ 1) {f : ℝ → ℂ} {C S Y : ℝ}
    (hY : 2 ≤ Y) (hC : 0 ≤ C)
    (pointwise : ∀ u ∈ Icc Y (8*Y), ‖f u - model s r u‖ ≤
      C * (u * Real.log (u*Y)^2 / Y + Real.log u + S))
    {y : ℝ} (hy : y ∈ Icc Y (2*Y))
    (hf₁ : IntervalIntegrable (weighted f) volume y (2*y))
    (hf₂ : IntervalIntegrable (weighted f) volume (2*y) (2*(2*y))) :
    ‖tent f y - ∑ i ∈ s, coefficient (r i) * (y : ℂ) ^ r i‖ ≤ 2 * envelope C S Y := by
  have hp : 0 < y := by linarith [hy.1]
  rw [← tent_model s r hr hp, ← tent_sub hf₁ (model_integrable s r hp)
    hf₂ (model_integrable s r (by positivity))]
  exact core3_uniform hY hC pointwise hy

open Filter Topology

private theorem logPower_small (k : ℕ) :
    Tendsto (fun Y : ℝ => Real.log Y ^ k / Real.sqrt Y) atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow] using
    (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := 1/2) (by norm_num)).tendsto_div_nhds_zero

/-- The explicit uniform envelope is negligible on the square-root scale. -/
theorem envelope_small (C S : ℝ) :
    Tendsto (fun Y : ℝ => 2*envelope C S Y / Real.sqrt Y) atTop (𝓝 0) := by
  let b := Real.log 8
  let k₀ := 2*C*(8*b^2 + b + S)
  let k₁ := 2*C*(32*b+1)
  let k₂ := 64*C
  have lim := (((logPower_small 0).const_mul k₀).add
    ((logPower_small 1).const_mul k₁)).add ((logPower_small 2).const_mul k₂)
  simp only [mul_zero, add_zero] at lim
  apply lim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  simp only [envelope, Real.log_mul (by norm_num : (8:ℝ) ≠ 0) (pow_ne_zero 2 hY.ne'),
    Real.log_mul (by norm_num : (8:ℝ) ≠ 0) hY.ne', Real.log_pow]
  dsimp [k₀, k₁, k₂, b]
  ring

/-- The cut-off and residual may depend on Y. The same starting scale works
for every sliding y in its doubling, with the normalization sqrt(y). -/
theorem core3_uniform_vanishing {err : ℝ → ℝ → E} {C S : ℝ} (hC : 0 ≤ C)
    (pointwise : ∀ Y, 2 ≤ Y → ∀ u ∈ Icc Y (8*Y), ‖err Y u‖ ≤
      C * (u * Real.log (u*Y)^2 / Y + Real.log u + S)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y in atTop, ∀ y ∈ Icc Y (2*Y),
      ‖tent (err Y) y‖ / Real.sqrt y < ε := by
  intro ε hε
  filter_upwards [eventually_ge_atTop (2:ℝ), (envelope_small C S).eventually_lt_const hε]
    with Y hY hbound
  intro y hy
  have hpos : 0 < Real.sqrt Y := Real.sqrt_pos.2 (by linarith)
  calc
    _ ≤ ‖tent (err Y) y‖ / Real.sqrt Y :=
      div_le_div_of_nonneg_left (norm_nonneg _) hpos (Real.sqrt_le_sqrt hy.1)
    _ ≤ 2 * envelope C S Y / Real.sqrt Y :=
      div_le_div_of_nonneg_right (core3_uniform hY hC (pointwise Y hY) hy) hpos.le
    _ < ε := hbound

/-- The finite spectrum may change with the starting scale. Given the pointwise
explicit formula with fixed constants, its smoothed difference is uniformly o(√y). -/
theorem finite_formula_vanishing {ι : Type*} (cut : ℝ → Finset ι) (r : ι → ℂ)
    (hr : ∀ Y, 2 ≤ Y → ∀ i ∈ cut Y, r i ≠ 0 ∧ r i ≠ 1)
    {f : ℝ → ℂ} {C S : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, 2 ≤ z → IntervalIntegrable (weighted f) volume z (2*z))
    (pointwise : ∀ Y, 2 ≤ Y → ∀ u ∈ Icc Y (8*Y), ‖f u - model (cut Y) r u‖ ≤
      C * (u * Real.log (u*Y)^2 / Y + Real.log u + S)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y in atTop, ∀ y ∈ Icc Y (2*Y),
      ‖tent f y - ∑ i ∈ cut Y, coefficient (r i) * (y : ℂ) ^ r i‖ / Real.sqrt y < ε := by
  intro ε hε
  have h := core3_uniform_vanishing hC pointwise ε hε
  filter_upwards [eventually_ge_atTop (2:ℝ), h] with Y hY hbound
  intro y hy
  have h₂ := hY.trans hy.1
  have hp : 0 < y := by linarith
  rw [← tent_model (cut Y) r (hr Y hY) hp, ← tent_sub (hf y h₂)
    (model_integrable (cut Y) r hp) (hf (2*y) (by linarith))
    (model_integrable (cut Y) r (by positivity))]
  exact hbound y hy

end PrimeWindowTransfer

#print axioms PrimeWindowTransfer.tent_uniform
#print axioms PrimeWindowTransfer.tent_sharp
#print axioms PrimeWindowTransfer.tent_model
#print axioms PrimeWindowTransfer.finite_formula_transfer
#print axioms PrimeWindowTransfer.core3_uniform_vanishing
#print axioms PrimeWindowTransfer.finite_formula_vanishing
