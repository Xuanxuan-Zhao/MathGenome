import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace ProbabilityFoundations.Ch06.Specs

/-- The finite transportation assertion, including a non-strict defect bound.
The empty cut forces the defect to be nonnegative. -/
def FiniteTransportation : Prop := by
  classical
  exact ∀ (L R : Type) [Fintype L] [Fintype R]
    (p : L → ℝ) (q : R → ℝ) (E : L → R → Prop) (δ : ℝ),
    (∀ i, 0 ≤ p i) → (∀ j, 0 ≤ q j) →
    (∑ i, p i) = 1 → (∑ j, q j) = 1 →
    (∀ I : Finset L, (∑ i ∈ I, p i) ≤
      (∑ j ∈ Finset.univ.filter (fun j => ∃ i ∈ I, E i j), q j) + δ) →
    ∃ m : L → R → ℝ,
      (∀ i j, 0 ≤ m i j) ∧
      (∀ i, ∑ j, m i j = p i) ∧
      (∀ j, ∑ i, m i j = q j) ∧
      (∑ i, ∑ j, if E i j then 0 else m i j) ≤ δ

end ProbabilityFoundations.Ch06.Specs
