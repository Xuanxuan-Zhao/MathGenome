import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects

/-!
The uniqueness assertion of `paper.tex`, Theorem 7.3 (lines 2464–2466).
The characteristic function is the shared canonical value, identified upstream
with the plus-sign integral without a factor of 2π. Euclidean space carries
its Borel sigma-algebra, and dimension zero is included.
-/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch07.CharacteristicUniqueness

open _root_.ProbabilityFoundations.Ch07
open Specs.ProbabilityFoundations.Ch07.TransformObjects

/-- Equality at every frequency determines the full original probability law. -/
def characteristicFunctionUniqueness : Prop :=
  ∀ {d : ℕ} (μ ν : Measure (Euclidean d)),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    (∀ t : Euclidean d, characteristicFunctionValue μ t = characteristicFunctionValue ν t) →
    μ = ν

end Specs.ProbabilityFoundations.Ch07.CharacteristicUniqueness
