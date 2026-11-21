import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects

/-! Independent statement of the uniqueness stage of `cor:laplace-cont`,
`paper.tex` lines 2573–2583. Both laws are Borel probability measures on the
closed orthant; there is no moment, density, or positive-dimension assumption. -/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch07.LaplaceUniqueness

open _root_.ProbabilityFoundations.Ch07

/-- Equality of all nonnegative-parameter Laplace values determines the law. -/
def laplaceUniquenessType : Prop :=
  ∀ {d : ℕ} (μ ν : Measure (PositiveOrthant d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    (∀ t : PositiveOrthant d,
      TransformObjects.laplaceTransformValue μ t =
        TransformObjects.laplaceTransformValue ν t) → μ = ν

end Specs.ProbabilityFoundations.Ch07.LaplaceUniqueness
