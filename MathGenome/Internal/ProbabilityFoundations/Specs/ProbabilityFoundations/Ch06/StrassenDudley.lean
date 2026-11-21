import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakMetrics
import Mathlib.MeasureTheory.Measure.Prod

/-!
Independent specification of paper.tex 2119–2123 and Theorem
`thm:p06-strassen` (2167–2175). The product carries the product measurable
structure; on a separable metric space it is exactly the product Borel structure.
There is no completeness assumption. All defect masses are finite real masses.
-/

open MeasureTheory TopologicalSpace

namespace Specs.ProbabilityFoundations.Ch06.StrassenDudley

universe u
noncomputable section

def couplingType := ∀ {S : Type u} [MeasurableSpace S],
  ProbabilityMeasure S → ProbabilityMeasure S → ProbabilityMeasure (S × S) → Prop

def couplingValue : couplingType := fun {S} _ μ ν γ =>
  Measure.map Prod.fst (γ : Measure (S × S)) = (μ : Measure S) ∧
  Measure.map Prod.snd (γ : Measure (S × S)) = (ν : Measure S)

def productBorelType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SeparableSpace S],
  (inferInstance : MeasurableSpace (S × S)) = borel (S × S)

def distanceEventMeasurableType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SeparableSpace S] (a : ℝ),
  MeasurableSet {z : S × S | a < dist z.1 z.2}

def productCouplingType : Prop := ∀ {S : Type u} [MeasurableSpace S]
  (μ ν : ProbabilityMeasure S),
  ∃ γ : ProbabilityMeasure (S × S), couplingValue μ ν γ

def forwardType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SeparableSpace S]
  (μ ν : ProbabilityMeasure S) (a : ℝ), 0 < a →
  WeakMetrics.prokhorovDistValue μ ν < a →
  ∃ γ : ProbabilityMeasure (S × S), couplingValue μ ν γ ∧
    (γ : Measure (S × S)).real {z | a < dist z.1 z.2} < a

def converseType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SeparableSpace S]
  (μ ν : ProbabilityMeasure S) (a : ℝ), 0 < a →
  ∀ γ : ProbabilityMeasure (S × S), couplingValue μ ν γ →
    (γ : Measure (S × S)).real {z | a < dist z.1 z.2} ≤ a →
    WeakMetrics.prokhorovDistValue μ ν ≤ a

end
end Specs.ProbabilityFoundations.Ch06.StrassenDudley
