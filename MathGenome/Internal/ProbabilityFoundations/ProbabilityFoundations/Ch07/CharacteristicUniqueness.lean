import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.CharacteristicUniqueness

/-!
Uniqueness in `paper.tex`, Theorem 7.3 (lines 2464–2466).
Mathlib's uniqueness theorem applies to finite measures on complete
second-countable real inner product spaces. Every Euclidean space here has
these instances, including dimension zero, and probability measures are finite.
-/

open MeasureTheory

namespace ProbabilityFoundations.Ch07

/-- The characteristic function determines a Borel probability law on ℝ^d. -/
theorem measure_eq_of_characteristicFunction_eq {d : ℕ}
    (μ ν : Measure (Euclidean d))
    (hμ : IsProbabilityMeasure μ) (hν : IsProbabilityMeasure ν)
    (h : ∀ t : Euclidean d, characteristicFunction μ t = characteristicFunction ν t) :
    μ = ν := by
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  exact Measure.ext_of_charFun (funext h)

end ProbabilityFoundations.Ch07
