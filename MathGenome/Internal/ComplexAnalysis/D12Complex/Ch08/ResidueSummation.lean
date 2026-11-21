import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.ResidueSummation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The unordered series is summable by inverse-square comparison, independently
of its value. Mathlib's proved `cot_series_rep` (derived there from Euler's
sine product) at `a * I` gives the evaluation after pairing positive and
negative integers. Thus this alternative to the square-contour proof uses
no assumed partial-fraction identity and no principal-value interpretation.
-/

noncomputable section
open Complex

namespace D12Complex.ResidueSummation

/-- Inverse-square comparison after removing the first term. -/
lemma summable_nat (a : ℝ) :
    Summable (fun n : ℕ => (1 / ((n : ℝ)^2 + a^2) : ℝ)) := by
  rw [← summable_nat_add_iff 1]
  have hs : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)^2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      (i := fun n : ℕ => n + 1) (fun _ _ h => Nat.add_right_cancel h)
  refine hs.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  exact one_div_le_one_div_of_le (by positivity)
    (le_add_of_nonneg_right (sq_nonneg a))

lemma summable_int (a : ℝ) :
    Summable (fun n : ℤ => (1 / ((n : ℝ)^2 + a^2) : ℝ)) := by
  apply Summable.of_nat_of_neg
  · simpa using summable_nat a
  · simpa using summable_nat a

lemma cot_imaginary (t : ℂ) :
    Complex.cot (t * Complex.I) = -Complex.I * (Complex.cosh t / Complex.sinh t) := by
  rw [Complex.cot, Complex.cos_mul_I, Complex.sin_mul_I]
  rw [← div_div, Complex.div_I]
  ring

lemma paired_term (a : ℝ) (ha : 0 < a) (n : ℕ+) :
    (1 / ((a : ℂ) * I - n) + 1 / ((a : ℂ) * I + n)) =
      (-2 * (a : ℂ) * I) * (1 / ((n : ℂ)^2 + (a : ℂ)^2)) := by
  have hp : 0 < (n : ℝ)^2 + a^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos ha)
  have hd : (n : ℂ)^2 + (a : ℂ)^2 ≠ 0 := by exact_mod_cast hp.ne'
  have hm : (a : ℂ) * I - n ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ha.ne' this
  have hplus : (a : ℂ) * I + n ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ha.ne' this
  field_simp [hd, hm, hplus]
  ring_nf
  norm_num

lemma tsum_complex (a : ℝ) (ha : 0 < a) :
    (∑' n : ℤ, (1 / ((n : ℂ)^2 + (a : ℂ)^2) : ℂ)) =
      (Real.pi : ℂ) / a * (Complex.cosh (Real.pi * a) / Complex.sinh (Real.pi * a)) := by
  have hs : Summable (fun n : ℤ => (1 / ((n : ℂ)^2 + (a : ℂ)^2) : ℂ)) := by
    simpa only [ofReal_div, ofReal_one, ofReal_add, ofReal_pow, ofReal_intCast] using
      (Complex.summable_ofReal.mpr (summable_int a))
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (fun n => by simp) hs]
  have hx : (a : ℂ) * I ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨(a : ℂ) * I, by simpa using ha⟩
  have hc := cot_series_rep hx
  rw [show (Real.pi : ℂ) * ((a : ℂ) * I) = ((Real.pi : ℂ) * a) * I by ring,
    cot_imaginary] at hc
  simp_rw [paired_term a ha] at hc
  rw [tsum_mul_left] at hc
  simp only [Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add, nsmul_eq_mul,
    Nat.cast_ofNat, Int.cast_natCast] at *
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have he := congrArg (fun z : ℂ => z * (I / (a : ℂ))) hc
  generalize (Complex.cosh ((Real.pi : ℂ) * a) / Complex.sinh ((Real.pi : ℂ) * a)) = c at *
  field_simp [ha0] at he ⊢
  simp only [I_sq] at he
  linear_combination -he

theorem absoluteSummability :
    Specs.D12Complex.Ch08.ResidueSummation.absoluteSummability_type := by
  intro a _
  convert summable_int a using 1
  ext n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem tsum_eq : Specs.D12Complex.Ch08.ResidueSummation.tsum_eq_type := by
  intro a ha
  apply Complex.ofReal_injective
  simpa only [ofReal_tsum, ofReal_div, ofReal_one, ofReal_add, ofReal_pow,
    ofReal_intCast, ofReal_mul, ofReal_cosh, ofReal_sinh] using tsum_complex a ha

theorem hasSum : Specs.D12Complex.Ch08.ResidueSummation.hasSum_type := by
  intro a ha
  rw [← tsum_eq a ha]
  exact (summable_int a).hasSum

theorem tsum_eq_coth : Specs.D12Complex.Ch08.ResidueSummation.tsum_eq_coth_type := by
  intro a ha
  exact tsum_complex a ha

end D12Complex.ResidueSummation
