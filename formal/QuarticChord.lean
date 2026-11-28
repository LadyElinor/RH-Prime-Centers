import QuarticChord.GuthMaynard
import QuarticChord.Supremum
import QuarticChord.Windows

/-! Quartic interpolation and anchor transfer for the ordinary-prime deficit.
All number-theoretic input is explicit in the types below. -/

namespace QuarticChord

open Set Filter Topology

/-- The uniform chord estimate with exactly the prime-count input and real width exponent. -/
theorem uniform_interpolation (gm : GuthMaynardPrimeCount) {B : ℝ} (hB : 0 ≤ B) :
    UniformChordSmall deficit B :=
  deficit_uniformChordSmall (m := 2*B+1) (by linarith)
    (gm.shortInterval B (2*B+1) hB (by linarith))

/-- Supremum over all lengths and positions in the written interpolation theorem. -/
theorem quartic_chord_limit (gm : GuthMaynardPrimeCount) {B : ℝ} (hB : 0 ≤ B) :
    Tendsto (fun A => sSup (normalizedChordValues deficit B A)) atTop (𝓝 0) :=
  (uniform_interpolation gm hB).tendsto_sup

/-- The full cell from k⁴ to (k+1)⁴ has uniform error o(k²). -/
theorem fourth_power_cell_limit (gm : GuthMaynardPrimeCount) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ Icc (anchor k) (anchor (k+1)),
      |deficit x - chord deficit (anchor k) (cellWidth k) x| ≤ ε * (k:ℝ)^2 :=
  fourth_cell_small (uniform_interpolation gm (by norm_num : (0:ℝ) ≤ 1)) hε

/-- A sufficiently late positive-margin block certifies that very same real window. -/
theorem positive_quartic_block (gm : GuthMaynardPrimeCount) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ K : ℕ in atTop, (∀ k ∈ Icc K (K^2), η*(k:ℝ)^2 ≤ deficit (anchor k)) →
      ∀ x ∈ Icc ((K:ℝ)^4) ((K:ℝ)^8), 0 < deficit x :=
  positive_window_on_late_anchor_blocks hη (uniform_interpolation gm (by norm_num))

/-- A weak lower bound at the anchors controls the deficit on their whole block. -/
theorem weak_quartic_block (gm : GuthMaynardPrimeCount) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ K : ℕ in atTop, (∀ k ∈ Icc K (K^2), -C*(k:ℝ)^2 ≤ deficit (anchor k)) →
      ∀ x ∈ Icc ((K:ℝ)^4) ((K:ℝ)^8), -(4*C+1) * Real.sqrt x ≤ deficit x :=
  weak_window_on_late_anchor_blocks hC (uniform_interpolation gm (by norm_num))

/-- On arbitrarily late blocks with the specified positive anchor margins, the
ordinary-prime deficit is strictly positive at every real position. -/
theorem positive_quartic_windows (gm : GuthMaynardPrimeCount) {η : ℝ} (hη : 0 < η)
    (blocks : RecurringAnchors deficit η) : RecurringWindows (fun x => 0 < deficit x) :=
  positive_windows_of_anchors hη (uniform_interpolation gm (by norm_num)) blocks

/-- Weak lower margins at the anchors transfer to a square-root lower bound
on the same family of real windows. -/
theorem weak_quartic_windows (gm : GuthMaynardPrimeCount) {C : ℝ} (hC : 0 ≤ C)
    (blocks : RecurringAnchors deficit (-C)) :
    RecurringWindows (fun x => -(4*C+1) * Real.sqrt x ≤ deficit x) :=
  weak_windows_of_anchors hC (uniform_interpolation gm (by norm_num)) blocks

end QuarticChord

#print axioms QuarticChord.quartic_chord_limit
#print axioms QuarticChord.fourth_power_cell_limit
#print axioms QuarticChord.positive_quartic_block
#print axioms QuarticChord.weak_quartic_block
#print axioms QuarticChord.positive_quartic_windows
#print axioms QuarticChord.weak_quartic_windows
