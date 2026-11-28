import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Abel summation on the half-open interval of primes `A < d*p ≤ A+u`.
The coefficient estimate below is a parameter, including at every partial endpoint.
All integrations and the coefficient of the common logarithm are computed here. -/

noncomputable section
namespace QuarticChord
open MeasureTheory
open scoped BigOperators Interval

/-- The ordinary-prime Chebyshev increment at dilation `d`. -/
def thetaMass (A d u : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc ⌊A/d⌋₊ ⌊(A+u)/d⌋₊, if p.Prime then Real.log p else 0

/-- The reciprocal-weighted ordinary-prime increment for the slope jumps. -/
def recipMass (A d u : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc ⌊A/d⌋₊ ⌊(A+u)/d⌋₊, if p.Prime then Real.log p / p else 0

/-- Truncating the coefficients at the lower endpoint makes the cumulative sum
in Mathlib's Abel formula count exactly the events after that endpoint. -/
private theorem truncated_prefix (c : ℕ → ℝ) (l r : ℕ) :
    (∑ p ∈ Finset.Icc 0 r, if l < p then c p else 0) = ∑ p ∈ Finset.Ioc l r, c p := by
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp [Finset.mem_Ioc, and_comm]

/-- Reciprocal weighting of a finite atomic measure compared to Lebesgue measure.
The boundary weight and integrated positive kernel have combined mass `1/a`. -/
private theorem abel_recip_error (c : ℕ → ℝ) {a b M : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hc : ∀ t ∈ Set.Icc a b, |(∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c p) - (t-a)| ≤ M) :
    |(∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c p / p) - Real.log (b/a)| ≤ M/a := by
  let cut := fun p : ℕ => if ⌊a⌋₊ < p then c p else 0
  let S := fun x : ℝ => ∑ p ∈ Finset.Icc 0 ⌊x⌋₊, cut p
  let g := fun x : ℝ => (x^2)⁻¹
  have hb := ha.trans_le hab
  have hp (x : ℝ) (hx : x ∈ Set.uIcc a b) : 0 < x :=
    ha.trans_le ((Set.uIcc_of_le hab) ▸ hx).1
  have hg : ContinuousOn g (Set.uIcc a b) :=
    (continuous_id.pow 2).continuousOn.inv₀ fun x hx => pow_ne_zero _ (hp x hx).ne'
  have hgI := hg.intervalIntegrable (μ := volume)
  have hgC : IntegrableOn g (Set.Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hgI
  have hS (x : ℝ) : S x = ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊, c p :=
    truncated_prefix c _ _
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) : |S t - (t-a)| ≤ M := by
    rw [hS]; exact hc t ht
  have habel := sum_mul_eq_sub_sub_integral_mul cut (f := fun x : ℝ => x⁻¹) ha.le hab
    (fun t ht => (hasDerivAt_inv (ha.trans_le ht.1).ne').differentiableAt)
    (by simpa only [deriv_inv'] using hgC.neg)
  have hat : S a = 0 := by rw [hS]; simp
  have hform : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c p / p) =
      b⁻¹ * S b + ∫ x in a..b, g x * S x := by
    calc
      _ = ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (p : ℝ)⁻¹ * cut p := by
        apply Finset.sum_congr rfl
        intro p hp'
        simp [cut, (Finset.mem_Ioc.mp hp').1, div_eq_mul_inv, mul_comm]
      _ = _ := by
        rw [habel]
        change _ * S b - _ * S a - (∫ t in Set.Ioc a b, _ * S t) = _
        simp only [hat, mul_zero, sub_zero, deriv_inv', neg_mul]
        rw [integral_neg, sub_neg_eq_add, intervalIntegral.integral_of_le hab]
  have hmainI : IntervalIntegrable (fun x => g x * (x-a)) volume a b :=
    (hg.mul (continuous_id.sub continuous_const).continuousOn).intervalIntegrable
  have hmain : (∫ x in a..b, g x * (x-a)) = (Real.log b + a*b⁻¹) - (Real.log a + a*a⁻¹) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hmainI
    intro x hx
    convert (Real.hasDerivAt_log (hp x hx).ne').add ((hasDerivAt_inv (hp x hx).ne').const_mul a) using 1
    dsimp [g]
    field_simp [(hp x hx).ne']
    ring
  have hkernel : (∫ x in a..b, g x) = a⁻¹ - b⁻¹ := by
    calc
      _ = -b⁻¹ - -a⁻¹ := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hgI
        intro x hx
        simpa [g] using (hasDerivAt_inv (hp x hx).ne').neg
      _ = _ := by ring
  have hSI : IntervalIntegrable (fun x => g x * S x) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (integrableOn_mul_sum_Icc cut ha.le hgC)
  have hsplit : (∫ x in a..b, g x * (S x - (x-a))) =
      (∫ x in a..b, g x * S x) - ∫ x in a..b, g x * (x-a) := by
    rw [← intervalIntegral.integral_sub hSI hmainI]
    exact intervalIntegral.integral_congr fun x _ => mul_sub ..
  have herror : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c p / p) - Real.log (b/a) =
      b⁻¹*(S b-(b-a)) + ∫ x in a..b, g x * (S x-(x-a)) := by
    rw [hform, hsplit, hmain, Real.log_div hb.ne' ha.ne']
    field_simp [ha.ne', hb.ne']
    ring
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun x => g x * (S x - (x-a))) (g := fun x => M * g x) hab
    (Filter.Eventually.of_forall fun x hx => by
      change ‖g x * (S x - (x-a))‖ ≤ M * g x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x)), mul_comm M]
      exact mul_le_mul_of_nonneg_left (he x ⟨hx.1.le, hx.2⟩) (inv_nonneg.mpr (sq_nonneg x)))
    ((continuousOn_const.mul hg).intervalIntegrable)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, hkernel] at hbound
  rw [herror]
  refine (abs_add_le ..).trans ?_
  rw [abs_mul, abs_of_pos (inv_pos.mpr hb)]
  have hbnd := mul_le_mul_of_nonneg_left (he b ⟨hab, le_rfl⟩) (inv_pos.mpr hb).le
  rw [div_eq_mul_inv]
  linarith only [hbnd, hbound]

/-- After undoing the dilation, the logarithmic main term is independent of `d`.
The error costs at most `d*M/A`, uniformly for every positive interval length,
and the same formula covers the zero-length interval. -/
theorem recipMass_error {A d u M : ℝ} (hA : 0 < A) (hd : 0 < d)
    (hu : 0 ≤ u) (_hM : 0 ≤ M)
    (hθ : ∀ v ∈ Set.Icc 0 u, |thetaMass A d v - v/d| ≤ M) :
    |recipMass A d u - Real.log (1 + u/A)| ≤ d*M/A := by
  let c := fun p : ℕ => if p.Prime then Real.log p else 0
  have hab : A/d ≤ (A+u)/d := by gcongr; linarith
  have h := abel_recip_error c (div_pos hA hd) hab (by
    intro t ht
    have h₁ := (div_le_iff₀ hd).mp ht.1
    have h₂ := (le_div_iff₀ hd).mp ht.2
    have h := hθ (t*d-A) ⟨by linarith, by linarith⟩
    have e : (A + (t*d-A))/d = t := by field_simp [hd.ne']; ring
    have f : (t*d-A)/d = t-A/d := by field_simp [hd.ne', hA.ne']
    simpa only [thetaMass, e, f, c] using h)
  have heq : recipMass A d u = ∑ p ∈ Finset.Ioc ⌊A/d⌋₊ ⌊(A+u)/d⌋₊, c p / p := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.Prime <;> simp [c, h]
  have e : ((A+u)/d)/(A/d) = 1+u/A := by field_simp [hd.ne', hA.ne']
  have f : M/(A/d) = d*M/A := by field_simp [hd.ne', hA.ne']
  simpa only [heq, e, f] using h

end QuarticChord
