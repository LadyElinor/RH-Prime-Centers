import QuarticChord.Asymptotic

/-! Fourth-power sampling. Each cell uses its own two endpoint values. -/

namespace QuarticChord

open Set Filter

/-- Real position of the `k`th fourth-power anchor. -/
def anchor (k : ℕ) : ℝ := (k : ℝ) ^ 4

/-- The exact gap to the next anchor. -/
def cellWidth (k : ℕ) : ℝ := anchor (k+1) - anchor k

private theorem cell_end (k : ℕ) : anchor k + cellWidth k = anchor (k+1) := by
  unfold cellWidth
  ring

private theorem cellWidth_pos (k : ℕ) : 0 < cellWidth k := by
  unfold cellWidth anchor
  push_cast
  nlinarith only [Nat.cast_nonneg (α := ℝ) k, sq_nonneg (k : ℝ),
    pow_nonneg (Nat.cast_nonneg k : 0 ≤ (k : ℝ)) 3]

private theorem sqrt_anchor (k : ℕ) : Real.sqrt (anchor k) = (k : ℝ)^2 := by
  rw [anchor, show (k : ℝ)^4 = ((k : ℝ)^2)^2 by ring, Real.sqrt_sq (sq_nonneg _)]

private theorem cast_le_anchor {k : ℕ} (hk : 1 ≤ k) : (k : ℝ) ≤ anchor k := by
  have h : (1:ℝ) ≤ k := by exact_mod_cast hk
  simpa [anchor] using (pow_le_pow_right₀ h (show 1 ≤ 4 by decide))

/-- Once `log(k⁴) ≥ 15`, the `B = 1` range contains the whole next cell. -/
theorem cellWidth_le_width {k : ℕ} (hk : 1 ≤ k) (hlog : 15 ≤ Real.log (anchor k)) :
    cellWidth k ≤ width 1 (anchor k) := by
  have h : (1:ℝ) ≤ k := by exact_mod_cast hk
  have h₁ : (k : ℝ) ≤ (k : ℝ)^3 := by simpa using pow_le_pow_right₀ h (show 1 ≤ 3 by decide)
  have h₂ := pow_le_pow_right₀ h (show 2 ≤ 3 by decide)
  have main : (anchor k) ^ (3/4:ℝ) = (k:ℝ)^3 := by
    unfold anchor
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg k) 4]
    norm_num
  unfold width
  rw [main, Real.rpow_one]
  calc
    cellWidth k ≤ (k:ℝ)^3 * 15 := by
      unfold cellWidth anchor
      push_cast
      nlinarith only [h, h₁, h₂]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)

/-- Epsilon form of the uniform `o(k²)` estimate on full fourth-power cells. -/
theorem fourth_cell_small {F : ℝ → ℝ} (small : UniformChordSmall F 1) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ k : ℕ in atTop, ∀ x ∈ Icc (anchor k) (anchor (k+1)),
      |F x - chord F (anchor k) (cellWidth k) x| ≤ ε * (k:ℝ)^2 := by
  obtain ⟨a, ha⟩ := eventually_atTop.1 (small ε hε)
  obtain ⟨n, hn⟩ := exists_nat_ge (max a (Real.exp 15))
  filter_upwards [eventually_ge_atTop (max n 1)] with k hk
  have hk₁ : 1 ≤ k := (le_max_right _ _).trans hk
  have hnk : (n:ℝ) ≤ k := by exact_mod_cast (le_max_left n 1).trans hk
  have large := hn.trans (hnk.trans (cast_le_anchor hk₁))
  have hlog : 15 ≤ Real.log (anchor k) := by
    simpa using Real.log_le_log (Real.exp_pos 15) ((le_max_right _ _).trans large)
  have hH : cellWidth k ∈ Ioc 0 (width 1 (anchor k)) :=
    ⟨cellWidth_pos k, cellWidth_le_width hk₁ hlog⟩
  intro x hx
  simpa only [sqrt_anchor] using
    ha (anchor k) ((le_max_left _ _).trans large) (cellWidth k) hH x (by rwa [cell_end])

/-- A closed block of at least one cell is covered by its closed consecutive cells,
including the last endpoint. No root rounding is needed. -/
theorem exists_covering_cell {K n : ℕ} {x : ℝ} (hKn : K < n)
    (hx : x ∈ Icc (anchor K) (anchor n)) :
    ∃ k, K ≤ k ∧ k < n ∧ x ∈ Icc (anchor k) (anchor (k+1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases prev : K < n ∧ x ≤ anchor n
    · obtain ⟨k, hk, hkn, hcell⟩ := ih prev.1 ⟨hx.1, prev.2⟩
      exact ⟨k, hk, by omega, hcell⟩
    · refine ⟨n, by omega, by omega, ?_, hx.2⟩
      by_cases eq : K = n
      · simpa only [← eq] using hx.1
      · have hlt : K < n := by omega
        exact le_of_lt (lt_of_not_ge fun hxn => prev ⟨hlt, hxn⟩)

/-- A fixed coefficient must work on arbitrarily late integer blocks, endpoints included. -/
def RecurringAnchors (F : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ N : ℕ, ∃ K ≥ N, ∀ k ∈ Icc K (K^2), c * (k:ℝ)^2 ≤ F (anchor k)

/-- The property holds at every real point of arbitrarily late closed blocks. -/
def RecurringWindows (P : ℝ → Prop) : Prop :=
  ∀ N : ℕ, ∃ K ≥ N, ∀ x ∈ Icc ((K:ℝ)^4) ((K:ℝ)^8), P x

private theorem late_windows_of_cells {F : ℝ → ℝ} {c : ℝ} {P : ℝ → Prop}
    (cells : ∀ᶠ k : ℕ in atTop, c*(k:ℝ)^2 ≤ F (anchor k) →
      c*((k+1:ℕ):ℝ)^2 ≤ F (anchor (k+1)) → ∀ x ∈ Icc (anchor k) (anchor (k+1)), P x) :
    ∀ᶠ K : ℕ in atTop, (∀ k ∈ Icc K (K^2), c*(k:ℝ)^2 ≤ F (anchor k)) →
      ∀ x ∈ Icc ((K:ℝ)^4) ((K:ℝ)^8), P x := by
  obtain ⟨n, hn⟩ := eventually_atTop.1 cells
  filter_upwards [eventually_ge_atTop n, eventually_ge_atTop 2] with K hnK hK₂
  intro nodes x hx
  have htop : anchor (K^2) = (K:ℝ)^8 := by simp [anchor, ← pow_mul]
  have hKK : K < K^2 := by nlinarith [Nat.mul_le_mul_left K hK₂]
  obtain ⟨k, hKk, hkk, hcell⟩ := exists_covering_cell hKK ⟨hx.1, by simpa only [htop] using hx.2⟩
  exact hn k (hnK.trans hKk) (nodes k ⟨hKk, hkk.le⟩)
    (nodes (k+1) ⟨by omega, by omega⟩) x hcell

/-- On every sufficiently late block, positive margins at all its anchors give
strict positivity at every real point of that same block. -/
theorem positive_window_on_late_anchor_blocks {F : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (small : UniformChordSmall F 1) :
    ∀ᶠ K : ℕ in atTop, (∀ k ∈ Icc K (K^2), η*(k:ℝ)^2 ≤ F (anchor k)) →
      ∀ x ∈ Icc ((K:ℝ)^4) ((K:ℝ)^8), 0 < F x := by
  apply late_windows_of_cells (F := F) (c := η) (P := fun x => 0 < F x)
  filter_upwards [fourth_cell_small small (show 0 < η/2 by linarith), eventually_ge_atTop 1]
    with k err hk
  intro left right x hx
  have hpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have scale : (k:ℝ)^2 ≤ ((k+1:ℕ):ℝ)^2 := by push_cast; nlinarith
  have hr := (mul_le_mul_of_nonneg_left scale hη.le).trans right
  have hchord := chord_lower (cellWidth_pos k) (by rwa [cell_end] : x ∈ Icc (anchor k) (anchor k + cellWidth k))
    left (by rwa [cell_end] : η*(k:ℝ)^2 ≤ F (anchor k + cellWidth k))
  have hlo := (abs_le.mp (err x hx)).1
  nlinarith only [hlo, hchord, mul_pos hη (sq_pos_of_pos hpos)]

/-- Even margins `−C k²` give a uniform lower bound on the matching real windows.
The constant `4C+1` uses `(k+1)² ≤ 4k²` for `k ≥ 1`. -/
theorem weak_window_on_late_anchor_blocks {F : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (small : UniformChordSmall F 1) :
    ∀ᶠ K : ℕ in atTop, (∀ k ∈ Icc K (K^2), -C*(k:ℝ)^2 ≤ F (anchor k)) →
      ∀ x ∈ Icc ((K:ℝ)^4) ((K:ℝ)^8), -(4*C+1) * Real.sqrt x ≤ F x := by
  apply late_windows_of_cells (F := F) (c := -C) (P := fun x => -(4*C+1) * Real.sqrt x ≤ F x)
  filter_upwards [fourth_cell_small small (show (0:ℝ) < 1 by norm_num), eventually_ge_atTop 1]
    with k err hk
  intro left right x hx
  have hk₁ : (1:ℝ) ≤ k := by exact_mod_cast hk
  have scale : ((k+1:ℕ):ℝ)^2 ≤ 4*(k:ℝ)^2 := by
    push_cast
    have h := pow_le_pow_left₀ (show 0 ≤ (k:ℝ)+1 by positivity)
      (show (k:ℝ)+1 ≤ 2*k by linarith) 2
    nlinarith only [h]
  have hl : -C * (4*(k:ℝ)^2) ≤ F (anchor k) := by
    nlinarith only [left, mul_nonneg hC (sq_nonneg (k:ℝ))]
  have hr : -C * (4*(k:ℝ)^2) ≤ F (anchor (k+1)) := by
    linarith only [right, mul_le_mul_of_nonneg_left scale hC]
  have hchord := chord_lower (cellWidth_pos k) (by rwa [cell_end] : x ∈ Icc (anchor k) (anchor k + cellWidth k))
    hl (by rwa [cell_end] : -C*(4*(k:ℝ)^2) ≤ F (anchor k + cellWidth k))
  have hs : (k:ℝ)^2 ≤ Real.sqrt x := by simpa only [sqrt_anchor] using Real.sqrt_le_sqrt hx.1
  have hlo := (abs_le.mp (err x hx)).1
  nlinarith only [hchord, hlo, mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*C+1 by linarith)]

private theorem recurring_windows_of_late_transfer {F : ℝ → ℝ} {c : ℝ} {P : ℝ → Prop}
    (transfer : ∀ᶠ K : ℕ in atTop, (∀ k ∈ Icc K (K^2), c*(k:ℝ)^2 ≤ F (anchor k)) →
      ∀ x ∈ Icc ((K:ℝ)^4) ((K:ℝ)^8), P x) (blocks : RecurringAnchors F c) :
    RecurringWindows P := by
  obtain ⟨n, hn⟩ := eventually_atTop.1 transfer
  intro N
  obtain ⟨K, hK, nodes⟩ := blocks (max n N)
  exact ⟨K, (le_max_right n N).trans hK, hn K ((le_max_left n N).trans hK) nodes⟩

/-- Recurring positive anchor margins give recurring strictly positive windows. -/
theorem positive_windows_of_anchors {F : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (small : UniformChordSmall F 1) (blocks : RecurringAnchors F η) :
    RecurringWindows (fun x => 0 < F x) :=
  recurring_windows_of_late_transfer (positive_window_on_late_anchor_blocks hη small) blocks

/-- Recurring weak anchor margins give recurring square-root lower bounds. -/
theorem weak_windows_of_anchors {F : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (small : UniformChordSmall F 1) (blocks : RecurringAnchors F (-C)) :
    RecurringWindows (fun x => -(4*C+1) * Real.sqrt x ≤ F x) :=
  recurring_windows_of_late_transfer (weak_window_on_late_anchor_blocks hC small) blocks

/-- The real-window start `X = K⁴` can exceed any prescribed real threshold. -/
theorem arbitrarily_late_real_windows {P : ℝ → Prop} (windows : RecurringWindows P) :
    ∀ R : ℝ, ∃ X ≥ R, ∀ x ∈ Icc X (X^2), P x := by
  intro R
  obtain ⟨n, hn⟩ := exists_nat_ge R
  obtain ⟨K, hK, hwindow⟩ := windows (max n 1)
  have hnK : (n:ℝ) ≤ K := by exact_mod_cast (le_max_left n 1).trans hK
  refine ⟨anchor K, hn.trans (hnK.trans (cast_le_anchor ((le_max_right _ _).trans hK))), ?_⟩
  simpa [anchor, ← pow_mul] using hwindow

end QuarticChord
