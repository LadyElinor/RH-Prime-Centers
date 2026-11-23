import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Lower bounds for finite real cosine sums between equally spaced samples. -/
namespace PrimeWindowCertificate

open Set
open scoped BigOperators

/-- With an upper bound on the second derivative, nodal lower bounds
lose at most one eighth of the curvature bound times the squared cell width. -/
theorem cell_lower {f f' f'' : ℝ → ℝ} {K a h A t : ℝ}
    (d₁ : ∀ x, HasDerivAt f (f' x) x) (d₂ : ∀ x, HasDerivAt f' (f'' x) x)
    (upper : ∀ x, f'' x ≤ K) (hK : 0 ≤ K)
    (left : A ≤ f a) (right : A ≤ f (a + h)) (ht : t ∈ Icc 0 1) :
    A - K*h^2/8 ≤ f (a + t*h) := by
  let g := fun x : ℝ => f x - (K/2)*x^2
  have dg (x : ℝ) : HasDerivAt g (f' x - K*x) x := by
    dsimp [g]
    convert (d₁ x).sub ((hasDerivAt_pow 2 x).const_mul (K/2)) using 1
    ring
  have ddg (x : ℝ) : HasDerivAt (fun u => f' u - K*u) (f'' x - K) x := by
    simpa using (d₂ x).sub ((hasDerivAt_id x).const_mul K)
  have conc : ConcaveOn ℝ univ g :=
    concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
      (fun x _ => (dg x).continuousAt.continuousWithinAt)
      (fun x _ => (dg x).hasDerivWithinAt)
      (fun x _ => (ddg x).hasDerivWithinAt)
      (fun x _ => sub_nonpos.mpr (upper x))
  have ht' : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have chord := conc.2 (x := a) (y := a+h) (mem_univ _) (mem_univ _)
    ht' ht.1 (by ring : 1-t+t=1)
  simp only [smul_eq_mul, g] at chord
  rw [show (1-t)*a + t*(a+h) = a+t*h by ring] at chord
  have hleft := mul_le_mul_of_nonneg_left left ht'
  have hright := mul_le_mul_of_nonneg_left right ht.1
  nlinarith only [chord, hleft, hright, mul_nonneg hK (sq_nonneg (h*(2*t-1)))]

/-- Certify every real log position from the lower bound at all grid nodes. -/
theorem grid_lower {f f' f'' : ℝ → ℝ} {K h A : ℝ}
    (d₁ : ∀ x, HasDerivAt f (f' x) x) (d₂ : ∀ x, HasDerivAt f' (f'' x) x)
    (upper : ∀ x, f'' x ≤ K) (hK : 0 ≤ K) (hh : 0 < h)
    (n : ℕ) (nodes : ∀ j : ℕ, j ≤ n → A ≤ f (j*h))
    {x : ℝ} (hx : x ∈ Icc 0 (n*h)) : A - K*h^2/8 ≤ f x := by
  induction n with
  | zero =>
    have hx0 : x = 0 := le_antisymm (by simpa using hx.2) hx.1
    rw [hx0]
    have h0 : A ≤ f 0 := by simpa using nodes 0 (Nat.le_refl 0)
    nlinarith only [h0, mul_nonneg hK (sq_nonneg h)]
  | succ n ih =>
    by_cases prev : x ≤ (n:ℝ)*h
    · exact ih (fun j hj => nodes j (Nat.le_succ_of_le hj)) ⟨hx.1, prev⟩
    · let a : ℝ := n*h
      have hxlo : a ≤ x := le_of_lt (lt_of_not_ge prev)
      have hxhi : x ≤ a+h := by simpa [a, Nat.cast_succ, add_mul] using hx.2
      have ht : (x-a)/h ∈ Icc 0 1 :=
        ⟨div_nonneg (sub_nonneg.mpr hxlo) hh.le, (div_le_one hh).mpr (by linarith)⟩
      have right : A ≤ f (a+h) := by
        simpa [a, Nat.cast_succ, add_mul] using nodes (n+1) (Nat.le_refl _)
      have hc := cell_lower d₁ d₂ upper hK (nodes n (Nat.le_succ n)) right ht
      convert hc using 1
      congr 1
      dsimp [a]
      field_simp
      ring

/-- A finite tent spectrum in amplitude-phase form. The logarithmic start
of the interval is absorbed in the phases. -/
noncomputable def spectrum {ι : Type*} (s : Finset ι) (amp freq phase : ι → ℝ) (v : ℝ) : ℝ :=
  ∑ i ∈ s, amp i * Real.cos (freq i * v + phase i)

def curvatureBound {ι : Type*} (s : Finset ι) (amp freq : ι → ℝ) : ℝ :=
  ∑ i ∈ s, amp i * (freq i)^2

/-- All positions in a finite grid of cells are covered, including both ends.
The amplitudes are nonnegative; phases absorb any coefficient signs. -/
theorem spectrum_grid_lower {ι : Type*} (s : Finset ι) (amp freq phase : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ amp i) {A h : ℝ} (hh : 0 < h) (n : ℕ)
    (nodes : ∀ j : ℕ, j ≤ n → A ≤ spectrum s amp freq phase (j*h))
    {v : ℝ} (hv : v ∈ Icc 0 (n*h)) :
    A - curvatureBound s amp freq * h^2/8 ≤ spectrum s amp freq phase v := by
  let d := fun v : ℝ => ∑ i ∈ s, (-amp i * freq i) * Real.sin (freq i*v + phase i)
  let dd := fun v : ℝ => ∑ i ∈ s, (amp i * (freq i)^2) * (-Real.cos (freq i*v + phase i))
  have arg (i : ι) (v : ℝ) :
      HasDerivAt (fun u : ℝ => freq i*u + phase i) (freq i) v := by
    simpa using (((hasDerivAt_id v).const_mul (freq i)).add_const (phase i))
  apply grid_lower (f' := d) (f'' := dd) _ _ _ _ hh n nodes hv
  · intro x
    apply HasDerivAt.fun_sum
    intro i _
    convert ((((Real.hasDerivAt_cos _).comp x (arg i x)).const_mul (amp i))) using 1
    ring
  · intro x
    apply HasDerivAt.fun_sum
    intro i _
    convert ((((Real.hasDerivAt_sin _).comp x (arg i x)).const_mul (-amp i*freq i))) using 1
    ring
  · intro x
    apply Finset.sum_le_sum
    intro i hi
    have bound := mul_le_mul_of_nonneg_left (neg_le.mpr (Real.neg_one_le_cos (freq i*x+phase i)))
      (mul_nonneg (ha i hi) (sq_nonneg (freq i)))
    linarith
  · exact Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (sq_nonneg (freq i))

/-- Complex sum used by the interval checker. The two counts conjugate pairs. -/
noncomputable def zeroSum {ι : Type*} (s : Finset ι) (coeff : ι → ℂ)
    (freq : ι → ℝ) (start v : ℝ) : ℝ :=
  2 * (∑ i ∈ s, coeff i * Complex.exp ((freq i*(start+v) : ℝ) * Complex.I)).re

theorem zeroSum_eq_spectrum {ι : Type*} (s : Finset ι) (coeff : ι → ℂ)
    (freq : ι → ℝ) (start v : ℝ) :
    zeroSum s coeff freq start v =
      spectrum s (fun i => 2*‖coeff i‖) freq
        (fun i => freq i*start + (coeff i).arg) v := by
  unfold zeroSum spectrum
  rw [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      show freq i*v + (freq i*start + (coeff i).arg) =
        freq i*(start+v) + (coeff i).arg by ring, Real.cos_add]
  rw [← Complex.norm_mul_cos_arg (coeff i), ← Complex.norm_mul_sin_arg (coeff i)]
  ring

/-- Transfer outward bounds at 257 nodes and on curvature to a floor throughout
a doubling. The decimal in the arithmetic premise bounds log 2 from above. -/
theorem doubling_floor {ι : Type*} (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (start A M L : ℝ)
    (nodes : ∀ j : ℕ, j ≤ 256 → A ≤ zeroSum s coeff freq start (j*(Real.log 2/256)))
    (curv : curvatureBound s (fun i => 2*‖coeff i‖) freq ≤ M)
    (arith : L ≤ A - M*(0.6931471808/256)^2/8)
    {v : ℝ} (hv : v ∈ Icc 0 (Real.log 2)) :
    L ≤ zeroSum s coeff freq start v := by
  let amp := fun i => 2*‖coeff i‖
  let phase := fun i => freq i*start + (coeff i).arg
  have ha : ∀ i ∈ s, 0 ≤ amp i := fun i _ => mul_nonneg (by norm_num) (norm_nonneg _)
  have hK : 0 ≤ curvatureBound s amp freq :=
    Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)
  have hp : 0 < Real.log 2 / 256 := by positivity
  have hu : Real.log 2 / 256 ≤ 0.6931471808 / 256 := by
    linarith only [Real.log_two_lt_d9]
  have width := pow_le_pow_left₀ hp.le hu 2
  have err := mul_le_mul curv width (sq_nonneg _) (hK.trans curv)
  have nodeBound (j : ℕ) (hj : j ≤ 256) :
      A ≤ spectrum s amp freq phase (j*(Real.log 2/256)) := by
    simpa only [zeroSum_eq_spectrum, amp, phase] using nodes j hj
  have inside : v ∈ Icc 0 ((256 : ℕ) * (Real.log 2/256)) := by
    constructor
    · exact hv.1
    · convert hv.2 using 1
      push_cast
      ring
  have lower := spectrum_grid_lower s amp freq phase ha hp 256 nodeBound inside
  have hl : L ≤ A - curvatureBound s amp freq * (Real.log 2/256)^2/8 :=
    arith.trans (sub_le_sub_left (div_le_div_of_nonneg_right err (by norm_num)) A)
  rw [zeroSum_eq_spectrum]
  exact hl.trans lower

/-- The three arithmetic obligations, with FLINT inputs rounded outwards.
Each row supplies the final arithmetic premise of doubling_floor. -/
theorem recorded_floors :
    let valid := fun (a m l : ℝ) =>
      l/1000000 ≤ a/1000000000 - (m/1000000000)*(0.6931471808/256)^2/8
    valid (-129507246) 49223601912 (-129553) ∧
    valid (-75190770) 155325919655 (-75334) ∧
    valid (-86210961) 427664801569 (-86603) := by
  norm_num

end PrimeWindowCertificate

#print axioms PrimeWindowCertificate.doubling_floor
#print axioms PrimeWindowCertificate.recorded_floors
