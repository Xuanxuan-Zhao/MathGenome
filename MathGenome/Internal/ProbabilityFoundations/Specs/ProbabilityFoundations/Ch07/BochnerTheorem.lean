import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Independent statement of `paper.tex:2642–2686`, the Euclidean Bochner
theorem in probability normalization. Euclidean space carries its Borel
sigma algebra; the dimension can be zero. -/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch07.BochnerTheorem

open _root_.ProbabilityFoundations.Ch07
open Specs.ProbabilityFoundations.Ch07.TransformObjects

/-- Every normalized continuous positive definite function is the
characteristic function of exactly one Borel probability law. Positivity is
the full finite complex quadratic-form condition from the shared interface. -/
def Bochner : Prop :=
  ∀ {d : ℕ} (φ : Euclidean d → ℂ), Continuous φ →
    isPositiveDefiniteValue φ → φ 0 = 1 →
    ∃! μ : ProbabilityMeasure (Euclidean d),
      ∀ t, characteristicFunctionValue (μ : Measure (Euclidean d)) t = φ t

end Specs.ProbabilityFoundations.Ch07.BochnerTheorem
