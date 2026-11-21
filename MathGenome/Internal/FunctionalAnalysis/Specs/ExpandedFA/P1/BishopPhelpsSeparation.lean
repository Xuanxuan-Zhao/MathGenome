import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Preserving a bounded separation, paper.tex:3495–3502, in its inherited
real or complex Banach-space setting. A strict separation is expressed by a
real upper bound on C and a uniform positive gap to A. This also expresses
the usual extended-infimum convention when A is empty. The conclusion says
that the norm-one functional attains its supremum on C and retains a uniform
gap to A; its nonzero norm makes the maximizing point a support point.
-/
namespace ExpandedFA.P1.BishopPhelpsSeparation.Spec
open Set
universe u

def RealSeparation : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (C A : Set E), C.Nonempty → IsClosed C → Convex ℝ C → Bornology.IsBounded A →
    ∀ (f : E →L[ℝ] ℝ), ‖f‖ = 1 →
    (∃ M d : ℝ, 0 < d ∧ (∀ y ∈ C, f y ≤ M) ∧ (∀ a ∈ A, M + d ≤ f a)) →
    ∀ ε : ℝ, 0 < ε → ∃ x ∈ C, ∃ g : E →L[ℝ] ℝ,
      ‖g‖ = 1 ∧ ‖g - f‖ < ε ∧ (∀ y ∈ C, g y ≤ g x) ∧
      ∃ η : ℝ, 0 < η ∧ ∀ a ∈ A, g x + η ≤ g a

def ComplexSeparation : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (C A : Set E), C.Nonempty → IsClosed C → Convex ℝ C → Bornology.IsBounded A →
    ∀ (f : E →L[ℂ] ℂ), ‖f‖ = 1 →
    (∃ M d : ℝ, 0 < d ∧ (∀ y ∈ C, (f y).re ≤ M) ∧
      (∀ a ∈ A, M + d ≤ (f a).re)) →
    ∀ ε : ℝ, 0 < ε → ∃ x ∈ C, ∃ g : E →L[ℂ] ℂ,
      ‖g‖ = 1 ∧ ‖g - f‖ < ε ∧ (∀ y ∈ C, (g y).re ≤ (g x).re) ∧
      ∃ η : ℝ, 0 < η ∧ ∀ a ∈ A, (g x).re + η ≤ (g a).re

end ExpandedFA.P1.BishopPhelpsSeparation.Spec
