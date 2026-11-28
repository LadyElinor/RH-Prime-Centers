import QuarticChord.PartialSummation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The ordinary-prime deficit, its finite hinge representation, and its right slopes.
The finite cutoff lets us work on a whole closed cell without differentiating a floor. -/
namespace QuarticChord

open Set Filter Topology
noncomputable section

/-- The weight used by the ordinary-prime tent at position `x`. -/
def primeTentWeight (p x : ℝ) : ℝ := max 0 (min (x/p-1) (2-x/(2*p)))

/-- The ordinary deficit in the position variable of the chord, including only primes. -/
def deficit (x : ℝ) : ℝ := x / 2 * Real.log 2 -
  ∑ p ∈ Finset.Iic ⌊x⌋₊, if p.Prime then primeTentWeight p x * Real.log p else 0

private def hinge (t x : ℝ) : ℝ := max 0 (x - t)
private def active (t x : ℝ) : ℝ := if t ≤ x then 1 else 0
private def coeff (p : ℕ) : ℝ := if p.Prime then Real.log p / p else 0

private def pieces (g : ℝ → ℝ → ℝ) (p x : ℝ) : ℝ :=
  -g p x + (3/2)*g (2*p) x - (1/2)*g (4*p) x

def finiteDeficit (N : ℕ) (x : ℝ) : ℝ := x * (Real.log 2 / 2) +
  ∑ p ∈ Finset.Iic N, pieces hinge p x * coeff p

def finiteSlope (N : ℕ) (x : ℝ) : ℝ := Real.log 2 / 2 +
  ∑ p ∈ Finset.Iic N, pieces active p x * coeff p

private theorem hinge_tent {p : ℝ} (hp : 0 < p) (x : ℝ) :
    pieces hinge p x = -(primeTentWeight p x * p) := by
  have he : primeTentWeight p x * p = max 0 (min (x-p) (2*p-x/2)) := by
    unfold primeTentWeight
    rw [max_mul_of_nonneg _ _ hp.le, min_mul_of_nonneg _ _ hp.le, zero_mul]
    congr 2 <;> field_simp
  rw [he]
  unfold pieces hinge
  rcases le_total x p with hx | hx
  · rw [max_eq_left (by linarith : x-p ≤ 0), max_eq_left (by linarith : x-2*p ≤ 0),
      max_eq_left (by linarith : x-4*p ≤ 0), min_eq_left (by linarith : x-p ≤ 2*p-x/2),
      max_eq_left (by linarith : x-p ≤ 0)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ x-p)]
    rcases le_total x (2*p) with hx' | hx'
    · rw [max_eq_left (by linarith : x-2*p ≤ 0), max_eq_left (by linarith : x-4*p ≤ 0),
        min_eq_left (by linarith : x-p ≤ 2*p-x/2), max_eq_right (by linarith : 0 ≤ x-p)]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ x-2*p),
        min_eq_right (by linarith : 2*p-x/2 ≤ x-p)]
      rcases le_total x (4*p) with hx'' | hx''
      · rw [max_eq_left (by linarith : x-4*p ≤ 0), max_eq_right (by linarith : 0 ≤ 2*p-x/2)]
        ring
      · rw [max_eq_right (by linarith : 0 ≤ x-4*p), max_eq_left (by linarith : 2*p-x/2 ≤ 0)]
        ring

/-- Every fixed upper cutoff beyond the position gives the exact ordinary-prime sum. -/
theorem finiteDeficit_eq_deficit (N : ℕ) {x : ℝ} (h : x ≤ N) :
    finiteDeficit N x = deficit x := by
  classical
  have hsub : Finset.Iic ⌊x⌋₊ ⊆ Finset.Iic N :=
    fun p hp => Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hp).trans (Nat.floor_le_of_le h))
  have hsum := Finset.sum_subset (f := fun p : ℕ => pieces hinge p x * coeff p) hsub (by
    intro p _ hp
    by_cases hprime : p.Prime
    · have hpx : x < p := lt_of_not_ge fun hle =>
        hp (Finset.mem_Iic.mpr ((Nat.le_floor_iff' hprime.ne_zero).mpr hle))
      have hpos : (0:ℝ) < p := by exact_mod_cast hprime.pos
      simp [pieces, hinge, max_eq_left (by linarith : x-p ≤ 0),
        max_eq_left (by linarith : x-2*p ≤ 0), max_eq_left (by linarith : x-4*p ≤ 0)]
    · simp [coeff, hprime])
  unfold finiteDeficit deficit
  rw [← hsum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro p _
    by_cases hprime : p.Prime
    · have hpos : (0:ℝ) < p := by exact_mod_cast hprime.pos
      simp only [coeff, hprime, if_true, hinge_tent hpos]
      field_simp
    · simp [coeff, hprime]

theorem finiteDeficit_continuous (N : ℕ) : Continuous (finiteDeficit N) := by
  unfold finiteDeficit pieces hinge
  fun_prop

private theorem hinge_rightDeriv (t x : ℝ) :
    HasDerivWithinAt (hinge t) (active t x) (Ici x) x := by
  by_cases h : t ≤ x
  · rw [active, if_pos h]
    apply ((hasDerivAt_id x).sub_const t).hasDerivWithinAt.congr_of_mem _ (le_refl x)
    intro y hy
    exact max_eq_right (sub_nonneg.mpr (h.trans hy))
  · rw [active, if_neg h]
    apply (hasDerivWithinAt_const x (Ici x) (0:ℝ)).congr_of_eventuallyEq_of_mem _ (le_refl x)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_of_not_ge h))]
      with y hy
    exact max_eq_left (sub_nonpos.mpr hy.le)

/-- At a knot the derivative from the right includes that knot's jump. -/
theorem finiteDeficit_rightDeriv (N : ℕ) (t : ℝ) :
    HasDerivWithinAt (finiteDeficit N) (finiteSlope N t) (Ici t) t := by
  unfold finiteDeficit finiteSlope
  apply HasDerivWithinAt.add
  · simpa using ((hasDerivAt_id t).mul_const (Real.log 2 / 2)).hasDerivWithinAt (s := Ici t)
  · apply HasDerivWithinAt.fun_sum
    intro p _
    exact (((hinge_rightDeriv p t).neg.add
      ((hinge_rightDeriv (2*p) t).const_mul (3/2))).sub
      ((hinge_rightDeriv (4*p) t).const_mul (1/2))).mul_const (coeff p)

private theorem eventMass (N : ℕ) {A u d : ℝ}
    (hA : 0 ≤ A) (hu : 0 ≤ u) (hd : 1 ≤ d) (hN : A+u ≤ N) :
    (∑ p ∈ Finset.Iic N, (active (d*p) (A+u) - active (d*p) A) * coeff p) =
      recipMass A d u := by
  classical
  have hpos : 0 < d := by linarith
  let s := Finset.Ioc ⌊A/d⌋₊ ⌊(A+u)/d⌋₊
  have hmem (p : ℕ) : p ∈ s ↔ A < d*p ∧ d*p ≤ A+u := by
    simp only [s, Finset.mem_Ioc, Nat.floor_lt (div_nonneg hA hpos.le),
      Nat.le_floor_iff (div_nonneg (add_nonneg hA hu) hpos.le),
      div_lt_iff₀ hpos, le_div_iff₀ hpos, mul_comm (p:ℝ) d]
  have hsub : s ⊆ Finset.Iic N := by
    intro p hp
    have hdn : (p:ℝ) ≤ d*p := by nlinarith [mul_nonneg (sub_nonneg.mpr hd) (Nat.cast_nonneg (α := ℝ) p)]
    have hpN : (p:ℝ) ≤ N := (hdn.trans ((hmem p).mp hp).2).trans hN
    exact Finset.mem_Iic.mpr (by exact_mod_cast hpN)
  rw [← Finset.sum_subset (f := fun p : ℕ => (active (d*p) (A+u) - active (d*p) A) * coeff p)
    hsub (by
      intro p _ hp
      by_cases hb : d*p ≤ A
      · simp [active, hb, hb.trans (le_add_of_nonneg_right hu)]
      · have he : ¬d*p ≤ A+u := fun hle => hp ((hmem p).mpr ⟨lt_of_not_ge hb, hle⟩)
        simp [active, hb, he])]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨ha, hb⟩ := (hmem p).mp hp
  simp [active, hb, not_le.mpr ha, coeff]

/-- Exact signed slope increment. The event interval is open at its start, closed at its end. -/
theorem finiteSlope_sub (N : ℕ) {A u : ℝ}
    (hA : 0 ≤ A) (hu : 0 ≤ u) (hN : A+u ≤ N) :
    finiteSlope N (A+u) - finiteSlope N A =
      -(recipMass A 1 u) + (3/2)*recipMass A 2 u - (1/2)*recipMass A 4 u := by
  rw [← eventMass N hA hu (le_refl 1) hN,
    ← eventMass N hA hu (by norm_num : (1:ℝ) ≤ 2) hN,
    ← eventMass N hA hu (by norm_num : (1:ℝ) ≤ 4) hN]
  simp only [finiteSlope, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, one_mul]
  apply Finset.sum_congr rfl
  intro p _
  unfold pieces
  ring

end
end QuarticChord
