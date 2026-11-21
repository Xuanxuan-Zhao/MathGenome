import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Darboux
import Mathlib.Analysis.Calculus.Darboux

/-!
# The intermediate value property of real derivatives

K03.05.darboux, paper.tex:884–892. Mathlib's Darboux theorem uses a
minimum of f(t) - m*t on the compact segment, excludes its endpoints by
the strict derivative inequalities, and applies Fermat at the minimum.
It requires derivatives within the segment, which follow here from ordinary
differentiability on the given open interval. It makes no continuity
assumption on the derivative. Both endpoint orders are handled explicitly.
-/

namespace SingleVariableAnalysis

open Set

theorem darboux_closed (f : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hinterval : OrdConnected I) (hf : DifferentiableOn ℝ f I)
    (u v : ℝ) (hu : u ∈ I) (hv : v ∈ I) (huv : u < v)
    (m : ℝ) (hm : m ∈ uIcc (deriv f u) (deriv f v)) :
    ∃ c ∈ Icc u v, deriv f c = m := by
  have hd : ∀ x ∈ Icc u v, HasDerivWithinAt f (deriv f x) (Icc u v) x := by
    intro x hx
    have hxI := hinterval.out hu hv hx
    exact ((hf x hxI).differentiableAt (hI.mem_nhds hxI)).hasDerivAt.hasDerivWithinAt
  rcases mem_uIcc.mp hm with h | h
  · exact exists_hasDerivWithinAt_eq_of_ge_of_le huv.le hd h.1 h.2
  · exact exists_hasDerivWithinAt_eq_of_le_of_ge huv.le hd h.2 h.1

theorem darboux_strict (f : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hinterval : OrdConnected I) (hf : DifferentiableOn ℝ f I)
    (u v : ℝ) (hu : u ∈ I) (hv : v ∈ I) (huv : u < v)
    (m : ℝ)
    (hm : (deriv f u < m ∧ m < deriv f v) ∨
      (deriv f v < m ∧ m < deriv f u)) :
    ∃ c ∈ Ioo u v, deriv f c = m := by
  have hd : ∀ x ∈ Icc u v, HasDerivWithinAt f (deriv f x) (Icc u v) x := by
    intro x hx
    have hxI := hinterval.out hu hv hx
    exact ((hf x hxI).differentiableAt (hI.mem_nhds hxI)).hasDerivAt.hasDerivWithinAt
  rcases hm with h | h
  · exact exists_hasDerivWithinAt_eq_of_gt_of_lt huv.le hd h.1 h.2
  · exact exists_hasDerivWithinAt_eq_of_lt_of_gt huv.le hd h.2 h.1

/-- Darboux rules out opposite signs even without continuity of the derivative. -/
theorem derivative_constant_sign (f : ℝ → ℝ) (I : Set ℝ)
    (hinterval : OrdConnected I) (hf : ∀ x ∈ I, DifferentiableAt ℝ f x)
    (hn : ∀ x ∈ I, deriv f x ≠ 0) :
    (∀ x ∈ I, 0 < deriv f x) ∨ (∀ x ∈ I, deriv f x < 0) := by
  exact (hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hinterval.convex
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) hn).symm

theorem derivative_constant_sign_on_open_interval (f : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hinterval : OrdConnected I) (hf : DifferentiableOn ℝ f I)
    (hn : ∀ x ∈ I, deriv f x ≠ 0) :
    (∀ x ∈ I, 0 < deriv f x) ∨ (∀ x ∈ I, deriv f x < 0) := by
  exact derivative_constant_sign f I hinterval
    (fun x hx => (hf x hx).differentiableAt (hI.mem_nhds hx)) hn

end SingleVariableAnalysis
