import QuarticChord.PartialSummation
import Mathlib.NumberTheory.PrimeCounting

/-! Converting a count of ordinary primes into a log-weighted sum on the same
half-open interval. All endpoint and integer-count bounds are deterministic. -/
noncomputable section
namespace QuarticChord

/-- Number of primes in (z,z+h] at nonnegative real endpoints. -/
def primeCount (z h : ℝ) : ℝ :=
  ((Finset.Ioc ⌊z⌋₊ ⌊z+h⌋₊).filter Nat.Prime).card

theorem primeCount_nonneg (z h : ℝ) : 0 ≤ primeCount z h := by
  unfold primeCount
  positivity

/-- The finite count is exactly the difference of Mathlib's ordinary prime
counting function at the two floored endpoints, including an integral right end. -/
theorem primeCount_eq_primeCounting_sub (z h : ℝ) (hh : 0 ≤ h) :
    primeCount z h = (Nat.primeCounting ⌊z+h⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊ := by
  let a := ⌊z⌋₊
  let b := ⌊z+h⌋₊
  have hab : a ≤ b := Nat.floor_mono (by linarith)
  have hincl : (a+1).primesBelow ⊆ (b+1).primesBelow := by
    intro p hp
    obtain ⟨hlt, hprime⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩
  have hdiff : (Finset.Ioc a b).filter Nat.Prime =
      (b+1).primesBelow \ (a+1).primesBelow := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesBelow]
    by_cases hp : p.Prime <;> simp [hp]
    omega
  change (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) = _
  rw [hdiff, Finset.card_sdiff_of_subset hincl, Nat.cast_sub (Finset.card_le_card hincl)]
  simp only [Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting, a, b]

/-- On (z,z+h], replacing log p by log z costs at most h/z per prime.
The cardinality of the underlying interval of integers is at most h+1. -/
theorem count_weight_bounds {A d u : ℝ} (hA : 0 < A) (hd : 0 < d) (hu : 0 ≤ u) :
    let z := A/d
    let h := u/d
    let n := primeCount z h
    n*Real.log z ≤ thetaMass A d u ∧ thetaMass A d u ≤ n*(Real.log z + h/z) ∧ n ≤ h+1 := by
  let z := A/d
  let h := u/d
  have hz : 0 < z := div_pos hA hd
  have hh : 0 ≤ h := div_nonneg hu hd.le
  have he : (A+u)/d = z+h := add_div _ _ _
  let S := (Finset.Ioc ⌊z⌋₊ ⌊z+h⌋₊).filter Nat.Prime
  have htheta : thetaMass A d u = ∑ p ∈ S, Real.log p := by
    unfold thetaMass
    rw [he]
    simp only [S, Finset.sum_filter, z]
  have hp {p : ℕ} (hpS : p ∈ S) : z < p ∧ (p : ℝ) ≤ z+h := by
    have hI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpS).1
    exact ⟨Nat.lt_of_floor_lt hI.1, (Nat.le_floor_iff (by linarith : 0 ≤ z+h)).mp hI.2⟩
  have hlog {p : ℕ} (hpS : p ∈ S) : Real.log p ≤ Real.log z + h/z := by
    obtain ⟨hlo, hhi⟩ := hp hpS
    have hpos := hz.trans hlo
    have h1 := Real.log_le_sub_one_of_pos (div_pos hpos hz)
    rw [Real.log_div hpos.ne' hz.ne'] at h1
    have h2 := div_le_div_of_nonneg_right hhi hz.le
    rw [add_div, div_self hz.ne'] at h2
    linarith
  change (S.card : ℝ)*Real.log z ≤ thetaMass A d u ∧
    thetaMass A d u ≤ S.card*(Real.log z + h/z) ∧ (S.card : ℝ) ≤ h+1
  rw [htheta]
  refine ⟨?_, ?_, ?_⟩
  · have hs := Finset.sum_le_sum (s := S) (fun p hpS => Real.log_le_log hz (hp hpS).1.le)
    simpa using hs
  · have hs := Finset.sum_le_sum (s := S) (fun p hpS => hlog hpS)
    simpa [mul_add] using hs
  · have card := Finset.card_le_card (Finset.filter_subset Nat.Prime (Finset.Ioc ⌊z⌋₊ ⌊z+h⌋₊))
    rw [Nat.card_Ioc] at card
    have hm : ⌊z⌋₊ ≤ ⌊z+h⌋₊ := Nat.floor_mono (by linarith)
    have hc : (S.card : ℝ) ≤ ((⌊z+h⌋₊ - ⌊z⌋₊ : ℕ) : ℝ) := by exact_mod_cast card
    rw [Nat.cast_sub hm] at hc
    linarith [Nat.floor_le (by linarith : 0 ≤ z+h), Nat.lt_floor_add_one z]

end QuarticChord
