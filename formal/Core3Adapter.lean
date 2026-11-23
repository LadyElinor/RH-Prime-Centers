import TentTransfer
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! Conductor-one specialization of the truncated explicit formula. -/
noncomputable section

namespace PrimeWindowCore3

open Set MeasureTheory Filter PrimeWindowTransfer
open scoped Interval Topology
open Classical in
/-- Input type of Pi's public theorem. The integration check supplies the actual theorem here. -/
def ExplicitFormula : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
        ∀ u T : ℝ, 2 ≤ T → T ≤ u →
          ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}).Finite ∧
          ‖((∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) -
              (if χ = 1 then (u : ℂ) else 0)) +
            ∑ᶠ ρ ∈ ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}),
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
            C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
              ∑ᶠ ρ ∈ ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ DirichletCharacter.LFunction χ ρ = 0}),
                (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖)

def zeros (T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ riemannZeta ρ = 0}

def multiplicity (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

def lowMass : ℝ := ∑ᶠ ρ ∈ zeros 1, (multiplicity ρ : ℝ) / ‖ρ‖

def psi (u : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ArithmeticFunction.vonMangoldt n

def primePowerError (u : ℝ) : ℂ := ((psi u - u : ℝ) : ℂ)

def spectrum (Y y : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ zeros Y, (multiplicity ρ : ℂ) * (coefficient ρ * (y : ℂ)^ρ)

/-- The pointwise conductor-one formula, before applying the tent. -/
theorem conductor_one (core : ExplicitFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (zeros T).Finite ∧
      ‖primePowerError u +
        ∑ᶠ ρ ∈ zeros T, (multiplicity ρ : ℂ) * ((u : ℂ)^ρ / ρ)‖ ≤
        C * (u * Real.log (u*T)^2 / T + Real.log u + lowMass) := by
  classical
  obtain ⟨C, hC, hall⟩ := core
  refine ⟨C, hC, fun u T hT hTu => ?_⟩
  have h := hall 1 (1 : DirichletCharacter ℂ 1) DirichletCharacter.isPrimitive_one_level_one
    u T hT hTu
  have hχ (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  simpa only [zeros, multiplicity, lowMass, primePowerError, psi, Complex.ofReal_sub,
    Complex.ofReal_sum, hχ, mul_one, eq_self, ite_true, Nat.cast_one, one_mul,
    DirichletCharacter.LFunction_modOne_eq] using h

/-- The height-one correction is a genuine finite sum even though Core 3 assumes T ≥ 2. -/
theorem zeros_finite (core : ExplicitFormula) (T : ℝ) : (zeros T).Finite := by
  obtain ⟨_, _, hall⟩ := conductor_one core
  apply (hall (max 2 T) (max 2 T) (le_max_left _ _) le_rfl).1.subset
  intro ρ h
  exact ⟨h.1, h.2.1, h.2.2.1.trans_le (le_max_right _ _), h.2.2.2⟩

theorem lowMass_nonneg : 0 ≤ lowMass := by
  unfold lowMass
  exact finsum_nonneg fun ρ => finsum_nonneg fun _ =>
    div_nonneg (Nat.cast_nonneg _) (norm_nonneg ρ)

private theorem psi_monotone : Monotone psi := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy)
  · exact fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg

private theorem weighted_psi_integrable {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (weighted primePowerError) volume z (2*z) := by
  have hreal : IntervalIntegrable (fun u : ℝ => psi u - u) volume z (2*z) :=
    psi_monotone.intervalIntegrable.sub (continuous_id.intervalIntegrable _ _)
  have herr : IntervalIntegrable primePowerError volume z (2*z) :=
    ⟨hreal.1.ofReal, hreal.2.ofReal⟩
  have hk : ContinuousOn (fun u : ℝ => u ^ (-2 : ℤ)) [[z, 2*z]] := by
    rw [uIcc_of_le (by linarith)]
    exact (continuousOn_zpow₀ (-2 : ℤ)).mono fun u hu => (hz.trans_le hu.1).ne'
  exact herr.continuousOn_mul (Complex.continuous_ofReal.comp_continuousOn hk)

private abbrev Copy := (Σ _ : ℂ, ℕ)

private def copies {Y : ℝ} (h : (zeros Y).Finite) : Finset Copy :=
  h.toFinset.sigma fun r => Finset.range (multiplicity r)

private theorem sum_copies {Y : ℝ} (h : (zeros Y).Finite) (g : ℂ → ℂ) :
    ∑ i ∈ copies h, g i.1 = ∑ᶠ r ∈ zeros Y, (multiplicity r : ℂ) * g r := by
  rw [finsum_mem_eq_finite_toFinset_sum _ h, copies, Finset.sum_sigma]
  simp

/-- One constant works for all starting scales and all real positions in each doubling. -/
theorem smoothed_bound (core : ExplicitFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      ∀ y ∈ Icc Y (2*Y), ‖tent primePowerError y - spectrum Y y‖ ≤ 2 * envelope C lowMass Y := by
  obtain ⟨C, hC, pointwise⟩ := conductor_one core
  refine ⟨C, hC, fun Y hY y hy => ?_⟩
  have hfin := (pointwise Y Y hY le_rfl).1
  have hr (i : Copy) (hi : i ∈ copies hfin) : i.1 ≠ 0 ∧ i.1 ≠ 1 := by
    have hz : i.1 ∈ zeros Y := hfin.mem_toFinset.mp (Finset.mem_sigma.mp hi).1
    exact ⟨fun h => by simpa [h] using hz.1, fun h => by simpa [h] using hz.2.1⟩
  have hpt (u : ℝ) (hu : u ∈ Icc Y (8*Y)) :
      ‖primePowerError u - model (copies hfin) Sigma.fst u‖ ≤
        C * (u * Real.log (u*Y)^2 / Y + Real.log u + lowMass) := by
    have hm : model (copies hfin) Sigma.fst u =
        -(∑ᶠ r ∈ zeros Y, (multiplicity r : ℂ) * ((u : ℂ)^r / r)) := by
      unfold model zeroTerm
      simp only [neg_div, Finset.sum_neg_distrib]
      rw [sum_copies hfin (fun r => (u : ℂ)^r / r)]
    rw [hm, sub_neg_eq_add]
    exact (pointwise u Y hY hu.1).2
  have hp : 0 < y := by linarith [hy.1]
  have hs := finite_formula_transfer (copies hfin) Sigma.fst hr hY hC.le hpt hy
    (weighted_psi_integrable hp) (weighted_psi_integrable (by positivity))
  simpa only [spectrum, sum_copies hfin (fun r => coefficient r * (y : ℂ)^r)] using hs

theorem smoothed_vanishing (core : ExplicitFormula) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y in atTop, ∀ y ∈ Icc Y (2*Y),
      ‖tent primePowerError y - spectrum Y y‖ / Real.sqrt y < ε := by
  obtain ⟨C, _, h⟩ := smoothed_bound core
  intro ε hε
  filter_upwards [eventually_ge_atTop (2 : ℝ), (envelope_small C lowMass).eventually_lt_const hε]
    with Y hY hsmall
  intro y hy
  have hp : 0 < Real.sqrt Y := Real.sqrt_pos.2 (by linarith)
  exact ((div_le_div_of_nonneg_left (norm_nonneg _) hp (Real.sqrt_le_sqrt hy.1)).trans
    (div_le_div_of_nonneg_right (h Y hY y hy) hp.le)).trans_lt hsmall

end PrimeWindowCore3

#print axioms PrimeWindowCore3.conductor_one
#print axioms PrimeWindowCore3.smoothed_bound
#print axioms PrimeWindowCore3.smoothed_vanishing
