import QuarticChord.Elementary
import QuarticChord.PrimeTent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform interpolation on all cells up to the quartic scale. The arithmetic
input is a bound on a cumulative sum of `log p`, before reciprocal weighting,
slope cancellation, interpolation, or normalization. -/
namespace QuarticChord

open Set Filter Topology

noncomputable def width (B A : ℝ) : ℝ := A ^ (3/4 : ℝ) * (Real.log A) ^ B

/-- The same constant and starting threshold work for all offsets and dilations.
This is the dilated θ estimate in the written proof, stated as a hypothesis. -/
def ShortIntervalPrimeEstimate (B m : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ A : ℝ in atTop,
    ∀ d : ℝ, d ∈ ({1, 2, 4} : Set ℝ) → ∀ u ∈ Icc 0 (width B A),
      |thetaMass A d u - u/d| ≤ C * width B A / (Real.log A) ^ m

/-- Uniform little-o, in an epsilon form that does not need a supremum. -/
def UniformChordSmall (F : ℝ → ℝ) (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ A : ℝ in atTop, ∀ H ∈ Ioc 0 (width B A),
    ∀ x ∈ Icc A (A+H), |F x - chord F A H x| ≤ ε * Real.sqrt A

/-- Divide by the positive scale to obtain the usual uniform normalized limit. -/
theorem UniformChordSmall.normalized {F : ℝ → ℝ} {B : ℝ} (h : UniformChordSmall F B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ A : ℝ in atTop, ∀ H ∈ Ioc 0 (width B A),
      ∀ x ∈ Icc A (A+H), |F x - chord F A H x| / Real.sqrt A < ε := by
  intro ε hε
  filter_upwards [h (ε/2) (half_pos hε), eventually_gt_atTop (0:ℝ)] with A hAeq hA
  intro H hH x hx
  have hs := Real.sqrt_pos.2 hA
  exact ((div_le_iff₀ hs).2 (hAeq H hH x hx)).trans_lt (half_lt_self hε)

/-- The square of the maximal width supplies the factor `√A * (log A)^(2B-m)`
after scaling by `A * (log A)^m`. -/
theorem width_envelope {A : ℝ} (hA : 1 < A) (B m C : ℝ) :
    C * width B A ^ 2 / (A * (Real.log A) ^ m) =
      (C * (Real.log A) ^ (2*B-m)) * Real.sqrt A := by
  have ha : 0 < A := zero_lt_one.trans hA
  have hl := Real.log_pos hA
  have haPow : A ^ (3/4 : ℝ) * A ^ (3/4 : ℝ) = Real.sqrt A * A := by
    calc
      _ = A ^ ((1/2 : ℝ) + 1) := by rw [← Real.rpow_add ha]; norm_num
      _ = _ := by rw [Real.rpow_add ha, Real.rpow_one, Real.sqrt_eq_rpow]
  have hlPow : (Real.log A) ^ B * (Real.log A) ^ B = (Real.log A) ^ (2*B) := by
    rw [← Real.rpow_add hl, two_mul]
  calc
    _ = C * ((A ^ (3/4 : ℝ) * A ^ (3/4 : ℝ)) *
          ((Real.log A) ^ B * (Real.log A) ^ B)) / (A * (Real.log A) ^ m) := by
      unfold width
      ring
    _ = _ := by
      rw [haPow, hlPow, Real.rpow_sub hl]
      field_simp [ha.ne', (Real.rpow_pos_of_pos hl m).ne']

/-- Every quantitative envelope with a fixed exponent `m > 2B` gives one
threshold valid for *all* admissible lengths and points. -/
theorem uniformChordSmall_of_envelope {F : ℝ → ℝ} {B m C : ℝ} (hm : 2*B < m)
    (bound : ∀ᶠ A : ℝ in atTop, ∀ H ∈ Ioc 0 (width B A), ∀ x ∈ Icc A (A+H),
      |F x - chord F A H x| ≤ C * width B A ^ 2 / (A * (Real.log A) ^ m)) :
    UniformChordSmall F B := by
  have lim : Tendsto (fun A : ℝ => C * (Real.log A) ^ (2*B-m)) atTop (𝓝 0) := by
    have negExp : 2*B-m = -(m-2*B) := by ring
    rw [negExp]
    simpa only [Function.comp_def, mul_zero] using
      (((tendsto_rpow_neg_atTop (sub_pos.mpr hm)).comp Real.tendsto_log_atTop).const_mul C)
  intro ε hε
  filter_upwards [bound, eventually_gt_atTop (1:ℝ), lim.eventually_lt_const hε] with A h hA hl
  intro H hH x hx
  calc
    _ ≤ C * width B A ^ 2 / (A * (Real.log A) ^ m) := h H hH x hx
    _ = _ := width_envelope hA B m C
    _ ≤ _ := mul_le_mul_of_nonneg_right hl.le (Real.sqrt_nonneg A)

/-- Finite, deterministic transfer on one cell. `M` bounds the unweighted
errors at all earlier offsets. No regularity hypothesis on the prime sum is needed. -/
theorem deficit_chord_of_theta {A H x M : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hM : 0 ≤ M) (hx : x ∈ Icc A (A+H))
    (hθ : ∀ d : ℝ, d ∈ ({1, 2, 4} : Set ℝ) → ∀ v ∈ Icc 0 H,
      |thetaMass A d v - v/d| ≤ M) :
    |deficit x - chord deficit A H x| ≤ 2 * (3 * (4*M/A)) * H := by
  obtain ⟨N, hN⟩ := exists_nat_ge (A+H)
  have hs (t : ℝ) (ht : t ∈ Ico A (A+H)) :
      |finiteSlope N t - finiteSlope N A| ≤ 3 * (4*M/A) := by
    let u := t-A
    have hu : 0 ≤ u := sub_nonneg.2 ht.1
    have htu : A+u = t := by dsimp [u]; ring
    have huH : u ≤ H := by dsimp [u]; linarith [ht.2]
    have single (d : ℝ) (hd : 0 < d) (hd4 : d ≤ 4) (hdset : d ∈ ({1,2,4} : Set ℝ)) :
        |recipMass A d u - Real.log (1 + u/A)| ≤ 4*M/A := by
      exact (recipMass_error hA hd hu hM (fun v hv => hθ d hdset v ⟨hv.1, hv.2.trans huH⟩)).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd4 hM) hA.le)
    have hNu : A+u ≤ (N:ℝ) := htu.trans_le (ht.2.le.trans hN)
    have jumps := finiteSlope_sub N hA.le hu hNu
    rw [htu] at jumps
    rw [jumps]
    exact signed_cancel_bound (single 1 (by norm_num) (by norm_num) (by simp))
      (single 2 (by norm_num) (by norm_num) (by simp))
      (single 4 (by norm_num) (by norm_num) (by simp))
  have h := chord_deviation_of_right_deriv hH (finiteDeficit_continuous N).continuousOn
    (fun t _ => finiteDeficit_rightDeriv N t) hs hx
  have hAN : A ≤ (N:ℝ) := (by linarith : A ≤ A+H).trans hN
  simpa only [chord, finiteDeficit_eq_deficit N (hx.2.trans hN),
    finiteDeficit_eq_deficit N hAN, finiteDeficit_eq_deficit N hN] using h

/-- Conditional uniform asymptotic for the actual ordinary-prime deficit. One
unweighted θ estimate with a sufficient logarithmic saving already suffices. -/
theorem deficit_uniformChordSmall {B m : ℝ} (hm : 2*B < m)
    (short : ShortIntervalPrimeEstimate B m) : UniformChordSmall deficit B := by
  obtain ⟨C, hC, hθ⟩ := short
  apply uniformChordSmall_of_envelope (C := 24*C) hm
  filter_upwards [hθ, eventually_gt_atTop (1:ℝ)] with A h hA
  intro H hH x hx
  have ha : 0 < A := zero_lt_one.trans hA
  have hl := Real.rpow_pos_of_pos (Real.log_pos hA) m
  have hV : 0 ≤ width B A := (hH.1.le.trans hH.2)
  let M := C * width B A / (Real.log A)^m
  have hM : 0 ≤ M := div_nonneg (mul_nonneg hC hV) hl.le
  calc
    _ ≤ 2 * (3 * (4*M/A)) * H := deficit_chord_of_theta ha hH.1 hM hx
      (fun d hd v hv => h d hd v ⟨hv.1, hv.2.trans hH.2⟩)
    _ ≤ 2 * (3 * (4*M/A)) * width B A := mul_le_mul_of_nonneg_left hH.2 (by positivity)
    _ = _ := by dsimp [M]; ring

/-- Version with the quantifiers of the written theorem: for each fixed B, the
constant may depend on B and the requested logarithmic saving. -/
theorem quartic_chord_interpolation
    (short : ∀ B : ℝ, 0 ≤ B → ∀ m : ℝ, 0 < m → ShortIntervalPrimeEstimate B m)
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ A : ℝ in atTop, ∀ H ∈ Ioc 0 (width B A),
      ∀ x ∈ Icc A (A+H), |deficit x - chord deficit A H x| / Real.sqrt A < ε :=
  (deficit_uniformChordSmall (B := B) (m := 2*B+1) (by linarith)
    (short B hB (2*B+1) (by linarith))).normalized

end QuarticChord
