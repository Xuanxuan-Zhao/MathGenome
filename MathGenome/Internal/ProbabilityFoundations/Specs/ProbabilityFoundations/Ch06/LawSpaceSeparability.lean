import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ProkhorovMetric
import Mathlib.Data.NNRat.Defs

/-! The separability assertion of `thm:p06-polish-laws`, paper.tex 2208–2227.
The specified metric is the source's π, including for incomplete spaces.
Weights are nonnegative rationals and their finite sum is exactly one.
Repeated support points and zero weights are permitted. -/
open MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

namespace Specs.ProbabilityFoundations.Ch06.LawSpaceSeparability
universe u
noncomputable section

def rationalFiniteLawsType := ∀ {S : Type u} [MeasurableSpace S],
  Set S → Set (ProbabilityMeasure S)

def rationalFiniteLawsValue : rationalFiniteLawsType := fun {S} _ D =>
  {μ | ∃ (n : ℕ) (x : Fin n → S) (q : Fin n → ℚ≥0),
    (∀ i, x i ∈ D) ∧ ∑ i, q i = 1 ∧
    (μ : Measure S) = ∑ i, ((q i : ℝ≥0) : ℝ≥0∞) • Measure.dirac (x i)}

def countableType : Prop := ∀ {S : Type u} [MeasurableSpace S]
  (D : Set S), D.Countable → (rationalFiniteLawsValue D).Countable

def denseType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (D : Set S), D.Countable → Dense D →
  @Dense (ProbabilityMeasure S)
    (ProkhorovMetric.metricSpaceValue (S := S)).toUniformSpace.toTopologicalSpace
    (rationalFiniteLawsValue D)

def separableType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SeparableSpace S],
  @SeparableSpace (ProbabilityMeasure S)
    (ProkhorovMetric.metricSpaceValue (S := S)).toUniformSpace.toTopologicalSpace

def emptyType : Prop := ∀ {S : Type u} [MeasurableSpace S] [IsEmpty S],
  IsEmpty (ProbabilityMeasure S)

end
end Specs.ProbabilityFoundations.Ch06.LawSpaceSeparability
