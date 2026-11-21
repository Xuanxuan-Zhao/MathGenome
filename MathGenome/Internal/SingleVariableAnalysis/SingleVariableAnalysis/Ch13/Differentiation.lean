import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.CompactUniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Differentiation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
K03.13.termwise: real-variable differentiation of scalar power series.

On |x-c| < r < ρ < R, the upstream descending-factorial geometric
majorant is summable for every order. `hasDerivAt_tsum_of_isPreconnected`
applies on the open real interval (c-r,c+r), with convergence at c proved
by that same majorant. Induction then identifies every iterated derivative.
Ordinary-sum uniqueness transports this to any representative of the source
sum; no derivative or convergence certificate is an input hypothesis.

All uses of unconditional `HasSum`/`tsum` are backed by proved summability.
The exported values are limits of the original ordered inclusive partial
sums. The real-scalar formulation handles complex coefficients using real
increments, without invoking complex differentiation.

For the exact radius, compact absolute convergence gives the forward bound.
Conversely, at t ≥ 0 the shifted original magnitude series is bounded by
`t * ((n+1) * ‖a(n+1)‖ * t^n)`. Testing finite distances strictly between
unequal extended radii proves equality, also at radius 0 or ∞.

A comparison reference is J. Lebl, Basic Analysis I, §6.2.4,
https://www.jirka.org/ra/realanal.pdf, Corollary 6.2.13. The radius proof
here uses the direct comparison in the source manuscript rather than the
reference's root-limsup proof under a positive-radius hypothesis.
-/

noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped BigOperators Topology ENNReal

namespace PowerSeriesDifferentiation

/-- Ordinary convergence of a nonnegative series implies library summability.
The shift from inclusive partial sums to `range n` is dealt with explicitly. -/
theorem summable_of_nonnegative_converges (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (h : RealSeriesConverges b) : Summable b := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨M, hM, hbound⟩ := real_convergent_bounded _ S hS
  apply summable_of_sum_range_le hb (c := M)
  intro n
  calc
    ∑ i ∈ Finset.range n, b i ≤ realPartialSum b n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
        (fun i _ _ => hb i)
    _ ≤ |realPartialSum b n| := le_abs_self _
    _ ≤ M := hbound n

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Real-scalar formulation, used for both real and complex coefficients. -/
def term (a : ℕ → F) (c : ℝ) (k : ℕ) (x : ℝ) (n : ℕ) : F :=
  ((n.descFactorial k : ℝ) * (x-c)^(n-k)) • a n

omit [CompleteSpace F] in
theorem term_hasDerivAt (a : ℕ → F) (c : ℝ) (k n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => term a c k y n) (term a c (k+1) x n) x := by
  have h := ((((hasDerivAt_id x).sub_const c).pow (n-k)).const_mul
    (n.descFactorial k : ℝ)).smul_const (a n)
  convert h using 1
  · rfl
  change ((n.descFactorial (k+1) : ℝ) * (x-c)^(n-(k+1))) • a n = _
  rw [Nat.descFactorial_succ, Nat.cast_mul]
  have he : n - (k+1) = n-k-1 := by omega
  rw [he]
  congr 1
  simp only [id_eq]
  ring

omit [CompleteSpace F] in
theorem norm_term (a : ℕ → F) (c : ℝ) (k n : ℕ) (x : ℝ) :
    ‖term a c k x n‖ = (n.descFactorial k : ℝ) * ‖a n‖ * |x-c|^(n-k) := by
  simp only [term, norm_smul, Real.norm_eq_abs, abs_mul, Nat.abs_cast, abs_pow]
  ring

/-- On a smaller open real interval, numerical convergence at ρ supplies a
summable uniform majorant of every formal derivative. -/
theorem term_majorant (a : ℕ → F) (c r ρ : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ)
    (hc : RealSeriesConverges (fun n => ‖a n‖ * ρ^n)) (k : ℕ) :
    ∃ B : ℕ → ℝ, Summable B ∧
      ∀ n x, |x-c| ≤ r → ‖term a c k x n‖ ≤ B n := by
  obtain ⟨B, hB0, hB, hb⟩ := PowerSeriesCompact.derivative_majorant
    (fun n => ‖a n‖) (fun n => norm_nonneg _) r ρ hr hrρ hc k
  refine ⟨B, summable_of_nonnegative_converges B hB0 hB, ?_⟩
  intro n x hx
  rw [norm_term]
  exact hb n |x-c| (abs_nonneg _) hx

theorem term_summable (a : ℕ → F) (c r ρ : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ)
    (hc : RealSeriesConverges (fun n => ‖a n‖ * ρ^n))
    (k : ℕ) (x : ℝ) (hx : |x-c| ≤ r) : Summable (term a c k x) := by
  obtain ⟨B, hB, hb⟩ := term_majorant a c r ρ hr hrρ hc k
  exact hB.of_norm_bounded (fun n => hb n x hx)

theorem sum_hasDerivAt (a : ℕ → F) (c r ρ : ℝ) (hr : 0 < r) (hrρ : r < ρ)
    (hc : RealSeriesConverges (fun n => ‖a n‖ * ρ^n))
    (k : ℕ) (x : ℝ) (hx : x ∈ Ioo (c-r) (c+r)) :
    HasDerivAt (fun y => ∑' n, term a c k y n)
      (∑' n, term a c (k+1) x n) x := by
  obtain ⟨B, hB, hb⟩ := term_majorant a c r ρ hr.le hrρ hc (k+1)
  apply hasDerivAt_tsum_of_isPreconnected hB isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun n y _ => term_hasDerivAt a c k n y) (fun n y hy => ?_)
    (show c ∈ Ioo (c-r) (c+r) by constructor <;> linarith)
    (term_summable a c r ρ hr.le hrρ hc k c (by simpa using hr.le)) hx
  exact hb n y (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)

/-- A representative of the ordinary sum can be arbitrary off this interval. -/
theorem all_derivatives_local (a : ℕ → F) (c r ρ : ℝ) (hr : 0 < r) (hrρ : r < ρ)
    (hc : RealSeriesConverges (fun n => ‖a n‖ * ρ^n)) (f : ℝ → F)
    (hf : ∀ x ∈ Ioo (c-r) (c+r), f x = ∑' n, term a c 0 x n) :
    ∀ (k : ℕ) (x : ℝ), x ∈ Ioo (c-r) (c+r) →
      iteratedDeriv k f x = ∑' n, term a c k x n := by
  intro k
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
    intro x hx
    have he : iteratedDeriv k f =ᶠ[𝓝 x] (fun y => ∑' n, term a c k y n) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact ih y hy
    rw [iteratedDeriv_succ]
    exact ((sum_hasDerivAt a c r ρ hr hrρ hc k x hx).congr_of_eventuallyEq he).deriv

theorem real_hasSum_of_hasSum {b : ℕ → ℝ} {S : ℝ} (h : HasSum b S) :
    RealSeriesHasSum b S := by
  apply (realSequenceConverges_iff _ _).mpr
  exact h.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem complex_hasSum_of_hasSum {b : ℕ → ℂ} {S : ℂ} (h : HasSum b S) :
    ComplexSeriesHasSum b S := by
  apply (complexSequenceConverges_iff _ _).mpr
  exact h.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem real_term_eq (a : ℕ → ℝ) (c : ℝ) (k n : ℕ) (x : ℝ) :
    term a c k x n = realFormalDerivativeTerm a c k x n := by
  dsimp [term, realFormalDerivativeTerm]
  ring

theorem complex_term_eq (a : ℕ → ℂ) (c : ℝ) (k n : ℕ) (x : ℝ) :
    term a c k x n = complexFormalDerivativeTerm a c k (x : ℂ) n := by
  simp only [term, complexFormalDerivativeTerm, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_natCast]
  ring

theorem real_terms_eq (a : ℕ → ℝ) (c : ℝ) (k : ℕ) (x : ℝ) :
    term a c k x = realFormalDerivativeTerm a c k x :=
  funext fun n => real_term_eq a c k n x

theorem complex_terms_eq (a : ℕ → ℂ) (c : ℝ) (k : ℕ) (x : ℝ) :
    term a c k x = complexFormalDerivativeTerm a c k (x : ℂ) :=
  funext fun n => complex_term_eq a c k n x

theorem real_terms_zero (a : ℕ → ℝ) (c x : ℝ) :
    term a c 0 x = realPowerSeriesTerm a c x := by
  funext n
  rw [real_term_eq, real_formalDerivative_zero]

theorem complex_terms_zero (a : ℕ → ℂ) (c x : ℝ) :
    term a c 0 x = complexPowerSeriesTerm a c (x : ℂ) := by
  funext n
  rw [complex_term_eq, complex_formalDerivative_zero]

/-- The unshifted first derivative has the same summability as its coefficient
series indexed from zero; the vanished degree-zero term is harmless. -/
theorem shifted_derivative_summable (b : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ n, 0 ≤ b n)
    (h : RealSeriesConverges (fun n => (n : ℝ) * b n * t^(n-1))) :
    Summable (fun n : ℕ => (n+1 : ℝ) * b (n+1) * t^n) := by
  have hs := summable_of_nonnegative_converges _
    (fun n => mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (hb n)) (pow_nonneg ht _)) h
  have hs' := (summable_nat_add_iff 1).mpr hs
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hs'

/-- Absolute convergence of a derivative series recovers absolute convergence
of its original series at the same nonnegative distance, including zero. -/
theorem original_summable (b : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ n, 0 ≤ b n)
    (h : Summable (fun n : ℕ => (n+1 : ℝ) * b (n+1) * t^n)) :
    Summable (fun n => b n * t^n) := by
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hb _) (pow_nonneg ht _)) (fun n => ?_) (h.mul_left t)
  calc
    b (n+1) * t^(n+1) = t * (b (n+1) * t^n) := by ring
    _ ≤ t * ((n+1 : ℝ) * b (n+1) * t^n) := by
      apply mul_le_mul_of_nonneg_left _ ht
      have hnonneg : 0 ≤ b (n+1) * t^n := mul_nonneg (hb _) (pow_nonneg ht _)
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hnonneg]

/-- Compare extended radii using only finite nonnegative test distances. -/
theorem radius_le_of_interior_convergence (P : ℝ → Prop) (r s : ℝ≥0∞)
    (hi : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < r → P t)
    (ho : ∀ t : ℝ, 0 ≤ t → s < ENNReal.ofReal t → ¬ P t) : r ≤ s := by
  apply le_of_not_gt
  intro h
  obtain ⟨t, ht, hst, htr⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
  exact ho t ht hst (hi t ht htr)

end PowerSeriesDifferentiation

open PowerSeriesDifferentiation

theorem real_powerSeries_sum_exists :
    Specs.SingleVariableAnalysis.Ch13.Differentiation.realSumExists := by
  intro a c
  change ∃ f : ℝ → ℝ, ∀ x, ENNReal.ofReal |x-c| < realPowerSeriesRadius a →
    RealPowerSeriesHasSum a c x (f x)
  classical
  let f : ℝ → ℝ := fun x => if h : RealPowerSeriesConverges a c x then h.choose else 0
  refine ⟨f, fun x hx => ?_⟩
  have h : RealPowerSeriesConverges a c x :=
    real_absolute_converges _ (real_powerSeries_radius_absolute a c x hx)
  simpa only [f, dite_eq_left h] using h.choose_spec

theorem complex_powerSeries_sum_exists :
    Specs.SingleVariableAnalysis.Ch13.Differentiation.complexSumExists := by
  intro a c
  change ∃ f : ℝ → ℂ, ∀ x, ENNReal.ofReal |x-c| < complexPowerSeriesRadius a →
    ComplexPowerSeriesHasSum a c (x : ℂ) (f x)
  classical
  let f : ℝ → ℂ := fun x => if h : ComplexPowerSeriesConverges a c (x : ℂ) then h.choose else 0
  refine ⟨f, fun x hx => ?_⟩
  have h : ComplexPowerSeriesConverges a c (x : ℂ) :=
    complex_absolute_converges _ (complex_powerSeries_radius_absolute a c _
      (by simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hx))
  simpa only [f, dite_eq_left h] using h.choose_spec

theorem real_powerSeries_all_derivatives :
    Specs.SingleVariableAnalysis.Ch13.Differentiation.realAllDerivatives := by
  intro a c f hf k x hx
  change ∀ y, ENNReal.ofReal |y-c| < realPowerSeriesRadius a →
    RealPowerSeriesHasSum a c y (f y) at hf
  change ENNReal.ofReal |x-c| < realPowerSeriesRadius a at hx
  change RealSeriesHasSum (realFormalDerivativeTerm a c k x) (iteratedDeriv k f x) ∧
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k+1) f x) x
  obtain ⟨ρ, hρ0, hxρ, hρR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx
  have hxρ' : |x-c| < ρ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)).mp hxρ
  let r := (|x-c|+ρ)/2
  have hr : 0 < r := by dsimp [r]; linarith [abs_nonneg (x-c)]
  have hrρ : r < ρ := by dsimp [r]; linarith
  have hxr : x ∈ Ioo (c-r) (c+r) := by
    have : |x-c| < r := by dsimp [r]; linarith
    obtain ⟨h1, h2⟩ := abs_lt.mp this
    constructor <;> linarith
  have hc : RealSeriesConverges (fun n => ‖a n‖ * ρ^n) := by
    simpa only [RealPowerSeriesAbsolutelyConverges, real_powerSeries_term_magnitude,
      sub_zero, abs_of_nonneg hρ0, Real.norm_eq_abs] using
      real_powerSeries_radius_absolute a 0 ρ (by simpa [abs_of_nonneg hρ0] using hρR)
  have hf' : ∀ y ∈ Ioo (c-r) (c+r), f y = ∑' n, term a c 0 y n := by
    intro y hy
    have hyr : |y-c| ≤ r := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hyR : ENNReal.ofReal |y-c| < realPowerSeriesRadius a :=
      (ENNReal.ofReal_le_ofReal hyr).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < ρ)).mpr hrρ |>.trans hρR)
    apply real_series_sum_unique _ _ _ (hf y hyR)
    simpa only [real_terms_zero] using
      real_hasSum_of_hasSum (term_summable a c r ρ hr.le hrρ hc 0 y hyr).hasSum
  have hall := all_derivatives_local a c r ρ hr hrρ hc f hf'
  have he : iteratedDeriv k f =ᶠ[𝓝 x] (fun y => ∑' n, term a c k y n) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxr] with y hy
    exact hall k y hy
  constructor
  · rw [hall k x hxr]
    simpa only [real_terms_eq] using
      real_hasSum_of_hasSum (term_summable a c r ρ hr.le hrρ hc k x
        (abs_le.mpr ⟨by linarith [hxr.1], by linarith [hxr.2]⟩)).hasSum
  · rw [hall (k+1) x hxr]
    exact (sum_hasDerivAt a c r ρ hr hrρ hc k x hxr).congr_of_eventuallyEq he

theorem complex_powerSeries_all_derivatives :
    Specs.SingleVariableAnalysis.Ch13.Differentiation.complexAllDerivatives := by
  intro a c f hf k x hx
  change ∀ y, ENNReal.ofReal |y-c| < complexPowerSeriesRadius a →
    ComplexPowerSeriesHasSum a c (y : ℂ) (f y) at hf
  change ENNReal.ofReal |x-c| < complexPowerSeriesRadius a at hx
  change ComplexSeriesHasSum (complexFormalDerivativeTerm a c k (x : ℂ)) (iteratedDeriv k f x) ∧
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k+1) f x) x
  obtain ⟨ρ, hρ0, hxρ, hρR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx
  have hxρ' : |x-c| < ρ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)).mp hxρ
  let r := (|x-c|+ρ)/2
  have hr : 0 < r := by dsimp [r]; linarith [abs_nonneg (x-c)]
  have hrρ : r < ρ := by dsimp [r]; linarith
  have hxr : x ∈ Ioo (c-r) (c+r) := by
    have : |x-c| < r := by dsimp [r]; linarith
    obtain ⟨h1, h2⟩ := abs_lt.mp this
    constructor <;> linarith
  have hc : RealSeriesConverges (fun n => ‖a n‖ * ρ^n) := by
    simpa only [ComplexPowerSeriesAbsolutelyConverges, complex_powerSeries_term_magnitude,
      Complex.ofReal_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using
      complex_powerSeries_radius_absolute a 0 (ρ : ℂ)
        (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using hρR)
  have hf' : ∀ y ∈ Ioo (c-r) (c+r), f y = ∑' n, term a c 0 y n := by
    intro y hy
    have hyr : |y-c| ≤ r := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hyR : ENNReal.ofReal |y-c| < complexPowerSeriesRadius a :=
      (ENNReal.ofReal_le_ofReal hyr).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < ρ)).mpr hrρ |>.trans hρR)
    apply complex_series_sum_unique _ _ _ (hf y hyR)
    simpa only [complex_terms_zero] using
      complex_hasSum_of_hasSum (term_summable a c r ρ hr.le hrρ hc 0 y hyr).hasSum
  have hall := all_derivatives_local a c r ρ hr hrρ hc f hf'
  have he : iteratedDeriv k f =ᶠ[𝓝 x] (fun y => ∑' n, term a c k y n) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxr] with y hy
    exact hall k y hy
  constructor
  · rw [hall k x hxr]
    simpa only [complex_terms_eq] using
      complex_hasSum_of_hasSum (term_summable a c r ρ hr.le hrρ hc k x
        (abs_le.mpr ⟨by linarith [hxr.1], by linarith [hxr.2]⟩)).hasSum
  · rw [hall (k+1) x hxr]
    exact (sum_hasDerivAt a c r ρ hr hrρ hc k x hxr).congr_of_eventuallyEq he

/-- Equality in ℝ≥0∞ covers the degenerate radii 0 and ∞ as well. -/
theorem real_powerSeries_derivative_radius :
    Specs.SingleVariableAnalysis.Ch13.Differentiation.realDerivativeRadius := by
  intro a
  change realPowerSeriesRadius (fun n : ℕ => (n+1 : ℝ) * a (n+1)) = realPowerSeriesRadius a
  let d : ℕ → ℝ := fun n : ℕ => (n+1 : ℝ) * a (n+1)
  have hdn (n : ℕ) : |d n| = (n+1 : ℝ) * |a (n+1)| := by
    dsimp only [d]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  apply le_antisymm
  · apply radius_le_of_interior_convergence (fun t => RealPowerSeriesConverges a 0 t)
    · intro t ht htd
      have hc := real_powerSeries_radius_absolute d 0 t (by simpa [abs_of_nonneg ht] using htd)
      have hc' : RealSeriesConverges (fun n : ℕ => (n+1 : ℝ) * |a (n+1)| * t^n) := by
        simpa only [RealPowerSeriesAbsolutelyConverges, real_powerSeries_term_magnitude,
          sub_zero, abs_of_nonneg ht, hdn] using hc
      have hs := original_summable (fun n => |a n|) t ht (fun n => abs_nonneg _)
        (summable_of_nonnegative_converges _ (fun n => by positivity) hc')
      apply real_absolute_converges
      have h := PowerSeriesCompact.ordinary_converges_of_summable _ hs
      simpa [RealSeriesAbsolutelyConverges, realPowerSeriesTerm, abs_mul, abs_pow,
        abs_of_nonneg ht] using h
    · intro t ht hta
      exact real_powerSeries_radius_diverges a 0 t (by simpa [abs_of_nonneg ht] using hta)
  · apply radius_le_of_interior_convergence (fun t => RealPowerSeriesConverges d 0 t)
    · intro t ht hta
      have hc := (real_formalDerivative_compact_uniform a 0 t ht hta 1).2.2
        ⟨t, by simp [abs_of_nonneg ht]⟩
      have hc' : RealSeriesConverges (fun n => (n : ℝ) * |a n| * t^(n-1)) := by
        simpa [realFormalDerivativeTerm, Nat.descFactorial_one, abs_mul, abs_pow,
          abs_of_nonneg ht] using hc
      have hs := shifted_derivative_summable (fun n => |a n|) t ht (fun n => abs_nonneg _) hc'
      apply real_absolute_converges
      have h := PowerSeriesCompact.ordinary_converges_of_summable _ hs
      simpa only [RealSeriesAbsolutelyConverges, real_powerSeries_term_magnitude,
        sub_zero, abs_of_nonneg ht, hdn] using h
    · intro t ht htd
      exact real_powerSeries_radius_diverges d 0 t (by simpa [abs_of_nonneg ht] using htd)

theorem complex_powerSeries_derivative_radius :
    Specs.SingleVariableAnalysis.Ch13.Differentiation.complexDerivativeRadius := by
  intro a
  change complexPowerSeriesRadius (fun n => (n+1 : ℂ) * a (n+1)) = complexPowerSeriesRadius a
  let d : ℕ → ℂ := fun n => (n+1 : ℂ) * a (n+1)
  have hdn (n : ℕ) : ‖d n‖ = (n+1 : ℝ) * ‖a (n+1)‖ := by
    dsimp [d]
    rw [norm_mul, show (n : ℂ) + 1 = ((n+1 : ℕ) : ℂ) by simp,
      Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
  have hdt (t : ℝ) (ht : 0 ≤ t) : ‖(t : ℂ)‖ = t := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  apply le_antisymm
  · apply radius_le_of_interior_convergence (fun t => ComplexPowerSeriesConverges a 0 (t : ℂ))
    · intro t ht htd
      have hc := complex_powerSeries_radius_absolute d 0 (t : ℂ) (by simpa only [Complex.ofReal_zero, sub_zero, hdt t ht] using htd)
      have hc' : RealSeriesConverges (fun n : ℕ => (n+1 : ℝ) * ‖a (n+1)‖ * t^n) := by
        simpa only [ComplexPowerSeriesAbsolutelyConverges, complex_powerSeries_term_magnitude,
          Complex.ofReal_zero, sub_zero, hdt t ht, hdn] using hc
      have hs := original_summable (fun n => ‖a n‖) t ht (fun n => norm_nonneg _)
        (summable_of_nonnegative_converges _ (fun n => by positivity) hc')
      apply complex_absolute_converges
      have h := PowerSeriesCompact.ordinary_converges_of_summable _ hs
      simpa only [ComplexSeriesAbsolutelyConverges, complexPowerSeriesTerm, norm_mul,
        norm_pow, Complex.ofReal_zero, sub_zero, hdt t ht] using h
    · intro t ht hta
      exact complex_powerSeries_radius_diverges a 0 (t : ℂ) (by simpa only [Complex.ofReal_zero, sub_zero, hdt t ht] using hta)
  · apply radius_le_of_interior_convergence (fun t => ComplexPowerSeriesConverges d 0 (t : ℂ))
    · intro t ht hta
      have hc := (complex_formalDerivative_compact_uniform a 0 t ht hta 1).2.2
        ⟨(t : ℂ), by simpa only [Complex.ofReal_zero, sub_zero, hdt t ht] using le_refl t⟩
      have hc' : RealSeriesConverges (fun n => (n : ℝ) * ‖a n‖ * t^(n-1)) := by
        simpa only [complexFormalDerivativeTerm, Nat.descFactorial_one, norm_mul, norm_pow,
          Complex.norm_natCast, Complex.ofReal_zero, sub_zero, hdt t ht] using hc
      have hs := shifted_derivative_summable (fun n => ‖a n‖) t ht (fun n => norm_nonneg _) hc'
      apply complex_absolute_converges
      have h := PowerSeriesCompact.ordinary_converges_of_summable _ hs
      simpa only [ComplexSeriesAbsolutelyConverges, complexPowerSeriesTerm, norm_mul,
        norm_pow, Complex.ofReal_zero, sub_zero, hdt t ht, hdn] using h
    · intro t ht htd
      exact complex_powerSeries_radius_diverges d 0 (t : ℂ) (by simpa only [Complex.ofReal_zero, sub_zero, hdt t ht] using htd)

end SingleVariableAnalysis
