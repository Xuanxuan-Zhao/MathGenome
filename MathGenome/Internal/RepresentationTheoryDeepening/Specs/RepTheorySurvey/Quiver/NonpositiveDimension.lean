import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.Forms

/-! A nonpositive integral dimension vector for a Tits form that fails positive definiteness. -/

universe u v

namespace RepTheorySurvey.Quiver.NonpositiveDimensionSpec

/-- Failure of real positive definiteness gives a nonzero, nonnegative integral vector
on which the Tits form is nonpositive. -/
def ExistsNonpositiveDimension : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → ¬ FormsSpec.PositiveDefinite Q →
      ∃ d : FormsSpec.DimensionVector Q,
        d ≠ 0 ∧ (∀ i, 0 ≤ d i) ∧ FormsSpec.titsForm d ≤ 0

end RepTheorySurvey.Quiver.NonpositiveDimensionSpec
