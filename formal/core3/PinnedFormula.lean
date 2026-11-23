import PiCore3
import Core3Adapter
import Mathlib.NumberTheory.Chebyshev

/-! The prime-power tent with Pi's verified theorem supplied as a proof term. -/
namespace PrimeWindowCore3

open PrimeWindowTransfer Set Filter
open scoped Topology

private theorem pinnedInput : ExplicitFormula := by
  obtain ⟨C, hC, formula⟩ := AlpogeRHCore3.explicitFormula
  refine ⟨C, hC, fun N _ χ hχ u T hT hTu => ?_⟩
  have h := formula N χ hχ u T hT hTu
  by_cases htriv : χ = 1 <;> simpa only [htriv, ite_true, ite_false, eq_self] using h

theorem psi_eq_chebyshev (u : ℝ) : psi u = Chebyshev.psi u := by
  unfold psi Chebyshev.psi
  rw [show Finset.Icc 1 ⌊u⌋₊ = Finset.Ioc 0 ⌊u⌋₊ from
    Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) _]

theorem primePowerError_eq :
    primePowerError = fun u : ℝ => ((Chebyshev.psi u - u : ℝ) : ℂ) := by
  funext u
  rw [primePowerError, psi_eq_chebyshev]

/-- The low-height correction in the error bound sums over a finite set. -/
theorem low_zeros_finite : (zeros 1).Finite :=
  zeros_finite pinnedInput 1

/-- A uniform bound with an existential constant, as in the upstream declaration. -/
theorem chebyshev_tent_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      ∀ y ∈ Icc Y (2*Y),
        ‖tent (fun u : ℝ => ((Chebyshev.psi u - u : ℝ) : ℂ)) y - spectrum Y y‖ ≤
          2 * envelope C lowMass Y := by
  rw [← primePowerError_eq]
  exact smoothed_bound pinnedInput

/-- With T = Y, the smoothed prime-power residual is uniformly small on a full doubling. -/
theorem chebyshev_tent_vanishing :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y in atTop, ∀ y ∈ Icc Y (2*Y),
      ‖tent (fun u : ℝ => ((Chebyshev.psi u - u : ℝ) : ℂ)) y - spectrum Y y‖ /
        Real.sqrt y < ε := by
  rw [← primePowerError_eq]
  exact smoothed_vanishing pinnedInput

end PrimeWindowCore3

#print axioms AlpogeRHCore3.explicitFormula
#print axioms PrimeWindowCore3.chebyshev_tent_bound
#print axioms PrimeWindowCore3.chebyshev_tent_vanishing
