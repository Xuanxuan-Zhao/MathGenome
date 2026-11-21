import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
Independent specification for the bounded positive decomposition assertion in
`fa2:p2:positive-automatic-continuity`, paper.tex:8781–8828.

`ConvexCone` requires addition and multiplication by strictly positive reals.
Closedness and the generating hypothesis imply membership of zero, so this
representation also covers the usual convention requiring zero in a cone.
No salience, order normality, or nonempty interior is required.
-/

universe u

namespace Specs.ExpandedFA.Ordered.PositiveDecompositions

/-- A closed generating convex cone in a real Banach space admits positive
decompositions with a uniform bound on each of the two summands. -/
def boundedPositiveDecompositions : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) →
    (∀ x : X, ∃ y ∈ P, ∃ z ∈ P, x = y - z) →
    ∃ C : ℝ, 0 < C ∧ ∀ x : X, ∃ y ∈ P, ∃ z ∈ P,
      x = y - z ∧ ‖y‖ ≤ C * ‖x‖ ∧ ‖z‖ ≤ C * ‖x‖

end Specs.ExpandedFA.Ordered.PositiveDecompositions
