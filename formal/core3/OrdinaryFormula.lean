import HigherPowers
import PinnedFormula

/-! Pi's truncated formula for the discrete ordinary-prime deficit with exact power correction. -/
namespace PrimeWindowCore3

open PrimeWindowDiscrete PrimeWindowTransfer Set Filter
open scoped Topology

noncomputable def ordinaryDeficit (y : ℝ) : ℝ :=
  2*y*Real.log 2 - windowSum primeCoeff y

/-- The two residuals agree exactly, with the same sign and truncation height. -/
theorem ordinary_residual_eq {y : ℝ} (hy : 0 < y) (Y : ℝ) :
    (ordinaryDeficit y : ℂ) - (spectrum Y y + (windowSum powerCoeff y : ℝ)) =
    tent (fun u : ℝ => ((Chebyshev.psi u - u : ℝ) : ℂ)) y - spectrum Y y := by
  rw [ordinaryDeficit, ordinary_prime_identity hy, Complex.ofReal_add,
    tent_ofReal (fun u : ℝ => Chebyshev.psi u - u) y]
  ring

/-- Finite-height bound for the discrete sum of ordinary primes. -/
theorem ordinary_tent_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y → ∀ y ∈ Icc Y (2*Y),
      ‖(ordinaryDeficit y : ℂ) - (spectrum Y y + (windowSum powerCoeff y : ℝ))‖ ≤
        2 * envelope C lowMass Y := by
  obtain ⟨C, hC, h⟩ := chebyshev_tent_bound
  refine ⟨C, hC, fun Y hY y hy => ?_⟩
  rw [ordinary_residual_eq (by linarith [hy.1] : 0 < y)]
  exact h Y hY y hy

/-- The ordinary-prime error after retaining the omitted power mass is uniformly o(√y). -/
theorem ordinary_tent_vanishing :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y in atTop, ∀ y ∈ Icc Y (2*Y),
      ‖(ordinaryDeficit y : ℂ) - (spectrum Y y + (windowSum powerCoeff y : ℝ))‖ /
        Real.sqrt y < ε := by
  intro ε hε
  filter_upwards [eventually_ge_atTop (1:ℝ), chebyshev_tent_vanishing ε hε] with Y hY h
  intro y hy
  rw [ordinary_residual_eq (by linarith [hy.1] : 0 < y)]
  exact h y hy


/-- The same uniform limit holds retaining prime squares alone. -/
theorem square_tent_vanishing :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y in atTop, ∀ y ∈ Icc Y (2*Y),
      ‖(ordinaryDeficit y : ℂ) - (spectrum Y y + (windowSum squareCoeff y : ℝ))‖ /
        Real.sqrt y < ε := by
  intro ε hε
  have hh := higher_window_vanishing.eventually (gt_mem_nhds (show 0 < ε/2 by linarith))
  obtain ⟨A, hA⟩ := eventually_atTop.1 hh
  obtain ⟨C, hC, hc⟩ := higher_window_bound
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop (1:ℝ),
      ordinary_tent_vanishing (ε/2) (by linarith)] with Y hYA hY h
  intro y hy
  have hp : 0 < y := by linarith [hy.1]
  have hn := (hc y (hY.trans hy.1)).1
  let r : ℂ := (ordinaryDeficit y : ℂ) - (spectrum Y y + (windowSum powerCoeff y : ℝ))
  have hsplit : (ordinaryDeficit y : ℂ) - (spectrum Y y + (windowSum squareCoeff y : ℝ)) =
      r + (windowSum higherCoeff y : ℝ) := by
    dsimp [r]
    rw [split_squares_higher, Complex.ofReal_add]
    ring
  have hnorm := norm_add_le r ((windowSum higherCoeff y : ℝ) : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn] at hnorm
  rw [hsplit]
  apply (div_le_div_of_nonneg_right hnorm (Real.sqrt_nonneg y)).trans_lt
  rw [add_div]
  have hr : ‖r‖ / Real.sqrt y < ε/2 := h y hy
  have hs : windowSum higherCoeff y / Real.sqrt y < ε/2 := hA y (hYA.trans hy.1)
  linarith

end PrimeWindowCore3

#print axioms PrimeWindowDiscrete.primePower_identity
#print axioms PrimeWindowDiscrete.ordinary_prime_identity
#print axioms PrimeWindowDiscrete.omitted_nonneg
#print axioms PrimeWindowDiscrete.split_squares_higher
#print axioms PrimeWindowDiscrete.squareCoeff_at_square
#print axioms PrimeWindowDiscrete.higherCoeff_pos_iff
#print axioms PrimeWindowCore3.ordinary_tent_bound
#print axioms PrimeWindowCore3.ordinary_tent_vanishing
#print axioms PrimeWindowDiscrete.higher_window_bound
#print axioms PrimeWindowDiscrete.higher_window_vanishing
#print axioms PrimeWindowCore3.square_tent_vanishing
