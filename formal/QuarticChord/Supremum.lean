import QuarticChord.Asymptotic

/-! Supremum formulation of uniform chord interpolation. -/

namespace QuarticChord

open Set Filter Topology

/-- The normalized departures for all admissible pairs `(H,x)` at one base point.
Their supremum takes both suprema in the written statement at once. -/
def normalizedChordValues (F : ℝ → ℝ) (B A : ℝ) : Set ℝ :=
  {r | ∃ H ∈ Ioc 0 (width B A), ∃ x ∈ Icc A (A+H),
    r = |F x - chord F A H x| / Real.sqrt A}

private theorem zero_mem_normalizedChordValues (F : ℝ → ℝ) (B : ℝ) {A : ℝ} (hA : 1 < A) :
    0 ∈ normalizedChordValues F B A := by
  have hw : 0 < width B A := mul_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans hA) _) (Real.rpow_pos_of_pos (Real.log_pos hA) _)
  refine ⟨width B A, ⟨hw, le_rfl⟩, A, ⟨le_rfl, by linarith⟩, ?_⟩
  simp [chord]

/-- The largest normalized departure tends to zero. For all sufficiently large
`A`, the set contains the endpoint departure zero and has a uniform upper bound. -/
theorem UniformChordSmall.tendsto_sup {F : ℝ → ℝ} {B : ℝ} (small : UniformChordSmall F B) :
    Tendsto (fun A => sSup (normalizedChordValues F B A)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [small.normalized (ε/2) (half_pos hε), eventually_gt_atTop (1:ℝ)] with A h hA
  have upper : ∀ r ∈ normalizedChordValues F B A, r ≤ ε/2 := by
    rintro r ⟨H, hH, x, hx, rfl⟩
    exact (h H hH x hx).le
  have mem := zero_mem_normalizedChordValues F B hA
  have lo := le_csSup (show BddAbove (normalizedChordValues F B A) from ⟨ε/2, upper⟩) mem
  have hi := csSup_le (show (normalizedChordValues F B A).Nonempty from ⟨0, mem⟩) upper
  simpa [Real.dist_eq, abs_of_nonneg lo] using hi.trans_lt (half_lt_self hε)

end QuarticChord
