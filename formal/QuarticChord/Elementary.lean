import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Elementary interpolation from one-sided slopes. Right derivatives allow a corner
at any interior point, including a position where several prime events coincide. -/
namespace QuarticChord

open Set

/-- The affine interpolant using the two actual values at the ends of the cell. -/
noncomputable def chord (F : ℝ → ℝ) (A H x : ℝ) : ℝ :=
  (1 - (x - A) / H) * F A + (x - A) / H * F (A + H)

private theorem chord_weight {A H x : ℝ} (hH : 0 < H) (hx : x ∈ Icc A (A+H)) :
    (x - A) / H ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (sub_nonneg.mpr hx.1) hH.le, (div_le_one hH).2 (by linarith [hx.2])⟩

/-- A common lower bound at the two anchors also bounds the whole chord. -/
theorem chord_lower {F : ℝ → ℝ} {A H x m : ℝ} (hH : 0 < H) (hx : x ∈ Icc A (A+H))
    (hl : m ≤ F A) (hr : m ≤ F (A+H)) : m ≤ chord F A H x := by
  have ht := chord_weight hH hx
  unfold chord
  linarith only [mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr ht.2),
    mul_le_mul_of_nonneg_left hr ht.1]

/-- The signed jumps at the three dilations sum to zero. -/
theorem signed_weights_sum : (-1 : ℝ) + 3/2 - 1/2 = 0 := by norm_num

/-- The common main term drops out of the slope change. -/
theorem signed_cancel (s₁ s₂ s₄ main : ℝ) :
    -s₁ + (3/2)*s₂ - (1/2)*s₄ =
      -(s₁-main) + (3/2)*(s₂-main) - (1/2)*(s₄-main) := by ring

/-- The sum of the absolute coefficients is three. -/
theorem signed_cancel_bound {s₁ s₂ s₄ main e : ℝ}
    (h₁ : |s₁-main| ≤ e) (h₂ : |s₂-main| ≤ e) (h₄ : |s₄-main| ≤ e) :
    |-s₁ + (3/2)*s₂ - (1/2)*s₄| ≤ 3*e := by
  rw [signed_cancel s₁ s₂ s₄ main]
  rcases abs_le.mp h₁ with ⟨lo₁, hi₁⟩
  rcases abs_le.mp h₂ with ⟨lo₂, hi₂⟩
  rcases abs_le.mp h₄ with ⟨lo₄, hi₄⟩
  apply abs_le.mpr
  constructor <;> linarith

/-- On a cell of positive width, if every right slope lies within ε of a fixed b,
the graph differs from its chord by at most 2 ε H. Subtract b times the coordinate
before applying the one-sided mean value inequality. -/
theorem chord_deviation_of_right_deriv {F s : ℝ → ℝ} {A H b ε x : ℝ}
    (hH : 0 < H) (hf : ContinuousOn F (Icc A (A+H)))
    (hd : ∀ t ∈ Ico A (A+H), HasDerivWithinAt F (s t) (Ici t) t)
    (hs : ∀ t ∈ Ico A (A+H), |s t-b| ≤ ε) (hx : x ∈ Icc A (A+H)) :
    |F x - chord F A H x| ≤ 2*ε*H := by
  let g (t : ℝ) := F t - b*t
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hs A ⟨le_rfl, by linarith⟩)
  have hgc : ContinuousOn g (Icc A (A+H)) :=
    hf.sub (continuous_const.mul continuous_id).continuousOn
  have hgd : ∀ t ∈ Ico A (A+H), HasDerivWithinAt g (s t-b) (Ici t) t := by
    intro t ht
    simpa [g] using (hd t ht).sub (((hasDerivAt_id t).const_mul b).hasDerivWithinAt)
  have bound := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd
    (fun t ht => by simpa only [Real.norm_eq_abs] using hs t ht)
  have point : |g x - g A| ≤ ε*H := by
    calc
      _ ≤ ε*(x-A) := by simpa only [Real.norm_eq_abs] using bound x hx
      _ ≤ ε*H := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hε
  have endpoint : |g (A+H) - g A| ≤ ε*H := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_left] using
      bound (A+H) ⟨by linarith, le_rfl⟩
  let t := (x-A)/H
  have ht : t ∈ Icc (0 : ℝ) 1 := chord_weight hH hx
  have hid : F x - chord F A H x = (g x - g A) - t*(g (A+H) - g A) := by
    unfold g chord t
    field_simp [hH.ne']
    ring
  rw [hid]
  calc
    _ ≤ |g x - g A| + |t*(g (A+H) - g A)| := abs_sub _ _
    _ = |g x - g A| + t*|g (A+H) - g A| := by rw [abs_mul, abs_of_nonneg ht.1]
    _ ≤ ε*H + 1*(ε*H) := add_le_add point (mul_le_mul ht.2 endpoint (abs_nonneg _) zero_le_one)
    _ = 2*ε*H := by ring

end QuarticChord
