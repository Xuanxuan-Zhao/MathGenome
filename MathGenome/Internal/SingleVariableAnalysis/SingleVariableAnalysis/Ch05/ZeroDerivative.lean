import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.ZeroDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.MeanInequality
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.LinearRules

/-!
# Zero derivatives and constants

K03.05.zero_derivative. Apply the proved scalar mean inequality with bound
zero to each segment in the interval. Its open segment is contained in the
interior of the original interval, so no endpoint derivative is required.
Subtract functions for the equal-derivative assertion. Empty sets admit the
constant zero, and the same statements include singletons without exceptions.
-/

namespace SingleVariableAnalysis

open Set
open scoped Topology

private theorem exists_constant_of_ordered_eq {F : Type*} [Zero F]
    (f : ℝ → F) (I : Set ℝ)
    (h : ∀ x ∈ I, ∀ y ∈ I, x < y → f x = f y) :
    ∃ c : F, ∀ x ∈ I, f x = c := by
  by_cases hI : I.Nonempty
  · obtain ⟨a, ha⟩ := hI
    refine ⟨f a, fun x hx => ?_⟩
    rcases lt_trichotomy x a with hxa | hxa | hax
    · exact h x hx a ha hxa
    · rw [hxa]
    · exact (h a ha x hx hax).symm
  · exact ⟨0, fun x hx => (hI ⟨x, hx⟩).elim⟩

theorem real_zero_derivative_constant (f : ℝ → ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hf : ContinuousOn f I)
    (hd : ∀ x ∈ interior I, DifferentiableAt ℝ f x)
    (hz : ∀ x ∈ interior I, deriv f x = 0) :
    ∃ c : ℝ, ∀ x ∈ I, f x = c := by
  apply exists_constant_of_ordered_eq f I
  intro x hx y hy hxy
  have hseg : Icc x y ⊆ I := hI.out hx hy
  have hint : Ioo x y ⊆ interior I := by
    simpa only [interior_Icc] using interior_mono hseg
  have hb := real_mean_inequality f x y 0 hxy le_rfl (hf.mono hseg)
    (fun t ht => hd t (hint ht)) (fun t ht => by rw [hz t (hint ht), abs_zero])
  have heq : f y - f x = 0 := abs_nonpos_iff.mp (by simpa using hb)
  exact (sub_eq_zero.mp heq).symm

theorem complex_zero_derivative_constant (f : ℝ → ℂ) (I : Set ℝ)
    (hI : I.OrdConnected) (hf : ContinuousOn f I)
    (hd : ∀ x ∈ interior I, DifferentiableAt ℝ f x)
    (hz : ∀ x ∈ interior I, deriv f x = 0) :
    ∃ c : ℂ, ∀ x ∈ I, f x = c := by
  apply exists_constant_of_ordered_eq f I
  intro x hx y hy hxy
  have hseg : Icc x y ⊆ I := hI.out hx hy
  have hint : Ioo x y ⊆ interior I := by
    simpa only [interior_Icc] using interior_mono hseg
  have hb := complex_mean_inequality f x y 0 hxy le_rfl (hf.mono hseg)
    (fun t ht => hd t (hint ht)) (fun t ht => by rw [hz t (hint ht), norm_zero])
  have heq : f y - f x = 0 := norm_le_zero_iff.mp (by simpa using hb)
  exact (sub_eq_zero.mp heq).symm

theorem real_equal_derivatives_differ_by_constant (f g : ℝ → ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hdf : ∀ x ∈ interior I, DifferentiableAt ℝ f x)
    (hdg : ∀ x ∈ interior I, DifferentiableAt ℝ g x)
    (heq : ∀ x ∈ interior I, deriv f x = deriv g x) :
    ∃ c : ℝ, ∀ x ∈ I, f x - g x = c := by
  apply real_zero_derivative_constant (fun x => f x - g x) I hI (hf.sub hg)
    (fun x hx => (hdf x hx).sub (hdg x hx))
  intro x hx
  change deriv (f - g) x = 0
  rw [((hdf x hx).hasDerivAt.sub (hdg x hx).hasDerivAt).deriv, heq x hx, sub_self]

theorem complex_equal_derivatives_differ_by_constant (f g : ℝ → ℂ) (I : Set ℝ)
    (hI : I.OrdConnected) (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hdf : ∀ x ∈ interior I, DifferentiableAt ℝ f x)
    (hdg : ∀ x ∈ interior I, DifferentiableAt ℝ g x)
    (heq : ∀ x ∈ interior I, deriv f x = deriv g x) :
    ∃ c : ℂ, ∀ x ∈ I, f x - g x = c := by
  apply complex_zero_derivative_constant (fun x => f x - g x) I hI (hf.sub hg)
    (fun x hx => (hdf x hx).sub (hdg x hx))
  intro x hx
  change deriv (f - g) x = 0
  rw [((hdf x hx).hasDerivAt.sub (hdg x hx).hasDerivAt).deriv, heq x hx, sub_self]

theorem disconnected_zero_derivative_example :
    Specs.SingleVariableAnalysis.Ch05.ZeroDerivative.disconnectedZeroDerivativeExample := by
  let I : Set ℝ := Ioo (-2) (-1) ∪ Ioo 1 2
  let f : ℝ → ℝ := fun x => if x < 0 then 0 else 1
  change ContinuousOn f I ∧ (∀ x ∈ I, HasDerivAt f 0 x) ∧
    (∀ x ∈ Ioo (-2 : ℝ) (-1), f x = 0) ∧
    (∀ x ∈ Ioo (1 : ℝ) 2, f x = 1) ∧ ¬ (∃ c : ℝ, ∀ x ∈ I, f x = c)
  have hder (x : ℝ) (hx : x ∈ I) : HasDerivAt f 0 x := by
    rcases hx with hx | hx
    · have hx0 : x < 0 := lt_trans hx.2 (by norm_num)
      apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isOpen_Iio.mem_nhds hx0] with y hy
      change y < 0 at hy
      simp only [f, ite_eq_left hy]
    · have hx0 : 0 < x := lt_trans (by norm_num) hx.1
      apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
      change 0 < y at hy
      simp only [f, ite_eq_right (not_lt.mpr hy.le)]
  refine ⟨fun x hx => (hder x hx).continuousAt.continuousWithinAt, hder, ?_, ?_, ?_⟩
  · intro x hx
    exact ite_eq_left (lt_trans hx.2 (by norm_num))
  · intro x hx
    exact ite_eq_right (not_lt.mpr (le_trans (by norm_num) hx.1.le))
  · rintro ⟨c, hc⟩
    have hleft := hc (-3 / 2) (by norm_num [I])
    have hright := hc (3 / 2) (by norm_num [I])
    norm_num [f] at hleft hright
    linarith

end SingleVariableAnalysis
