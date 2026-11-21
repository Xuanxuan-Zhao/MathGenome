import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.RootUniqueness
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.IntermediateValues
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Monotonicity

/-!
# Existence and uniqueness of roots

K03.05.root_uniqueness, paper.tex:860–869. A negative product puts zero
strictly between the endpoint values, so the upstream open intermediate
value theorem supplies the root. Strict monotonicity gives injectivity on
the closed interval. The upstream derivative criteria supply either strict
increase or strict decrease under precisely the interior sign hypotheses.
-/

namespace SingleVariableAnalysis

open Set

theorem root_exists_of_endpoint_product_neg (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : RelativeContinuous f (Icc a b)) (hs : f a * f b < 0) :
    ∃ c ∈ Ioo a b, f c = 0 := by
  apply intermediate_value_open f a b hab hf 0
  rcases mul_neg_iff.mp hs with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.1, h.2⟩

theorem root_unique_of_strictMonotone (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : RelativeContinuous f (Icc a b)) (hs : f a * f b < 0)
    (hm : StrictMonoOn f (Icc a b) ∨ StrictAntiOn f (Icc a b)) :
    ∃ c ∈ Ioo a b, f c = 0 ∧ ∀ x ∈ Icc a b, f x = 0 → x = c := by
  obtain ⟨c, hc, hz⟩ := root_exists_of_endpoint_product_neg f a b hab hf hs
  refine ⟨c, hc, hz, fun x hx hxz => ?_⟩
  have hcc : c ∈ Icc a b := ⟨hc.1.le, hc.2.le⟩
  rcases hm with hm | hm
  · exact hm.injOn hx hcc (hxz.trans hz.symm)
  · exact hm.injOn hx hcc (hxz.trans hz.symm)

theorem root_unique_of_positive_derivative (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : RelativeContinuous f (Icc a b)) (hs : f a * f b < 0)
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Ioo a b, 0 < deriv f x) :
    ∃ c ∈ Ioo a b, f c = 0 ∧ ∀ x ∈ Icc a b, f x = 0 → x = c := by
  apply root_unique_of_strictMonotone f a b hab hf hs
  exact Or.inl (positive_derivative_strictMono f (Icc a b) ordConnected_Icc
    (relativeContinuous_continuousOn f (Icc a b) hf)
    (by simpa only [interior_Icc] using hd)
    (by simpa only [interior_Icc] using hp))

theorem root_unique_of_negative_derivative (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : RelativeContinuous f (Icc a b)) (hs : f a * f b < 0)
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hn : ∀ x ∈ Ioo a b, deriv f x < 0) :
    ∃ c ∈ Ioo a b, f c = 0 ∧ ∀ x ∈ Icc a b, f x = 0 → x = c := by
  apply root_unique_of_strictMonotone f a b hab hf hs
  exact Or.inr (negative_derivative_strictAnti f (Icc a b) ordConnected_Icc
    (relativeContinuous_continuousOn f (Icc a b) hf)
    (by simpa only [interior_Icc] using hd)
    (by simpa only [interior_Icc] using hn))

theorem root_unique_of_realIncrement_derivative (f d : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : RelativeContinuous f (Icc a b)) (hs : f a * f b < 0)
    (hd : ∀ x ∈ Ioo a b, HasRealIncrementDerivativeWithin f (d x) (Icc a b) x)
    (hsgn : (∀ x ∈ Ioo a b, 0 < d x) ∨ (∀ x ∈ Ioo a b, d x < 0)) :
    ∃ c ∈ Ioo a b, f c = 0 ∧ ∀ x ∈ Icc a b, f x = 0 → x = c := by
  have hm := realIncrement_monotonicity f d (Icc a b) ordConnected_Icc hf
    (by simpa only [interior_Icc] using hd)
  apply root_unique_of_strictMonotone f a b hab hf hs
  rcases hsgn with hp | hn
  · exact Or.inl (hm.2.1 (by simpa only [interior_Icc] using hp))
  · exact Or.inr (hm.2.2.2 (by simpa only [interior_Icc] using hn))

private theorem cubic_zero_iff (x : ℝ) :
    x * (x ^ 2 - 1) = 0 ↔ x = -1 ∨ x = 0 ∨ x = 1 := by
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with hz | hz
    · exact Or.inr (Or.inl hz)
    · have hfactor : (x - 1) * (x + 1) = 0 := by nlinarith [hz]
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inr (Or.inr (by linarith))
      · exact Or.inl (by linarith)
  · rintro (rfl | rfl | rfl) <;> norm_num

theorem cubic_root_counterexample :
    let f : ℝ → ℝ := fun x => x * (x ^ 2 - 1)
    ContinuousOn f (Icc (-2) 2) ∧
      f (-2) = -6 ∧ f 2 = 6 ∧ f (-2) * f 2 < 0 ∧
      (∀ x : ℝ, (x ∈ Ioo (-2) 2 ∧ f x = 0) ↔ x = -1 ∨ x = 0 ∨ x = 1) ∧
      ¬ (∃! x : ℝ, x ∈ Icc (-2) 2 ∧ f x = 0) := by
  dsimp only
  refine ⟨(continuous_id.mul ((continuous_id.pow 2).sub continuous_const)).continuousOn,
    by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      exact (cubic_zero_iff x).mp hx.2
    · intro hx
      refine ⟨?_, (cubic_zero_iff x).mpr hx⟩
      rcases hx with rfl | rfl | rfl <;> constructor <;> norm_num
  · rintro ⟨c, _, hu⟩
    have hneg := hu (-1) (by constructor <;> norm_num)
    have hzero := hu 0 (by constructor <;> norm_num)
    linarith

end SingleVariableAnalysis
