import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuityPartitions
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-! Independent statements for paper.tex, Proposition `p06-finite-products`.
The index type is any finite type, including the empty type. Each factor carries
its original metric and Borel sigma algebra; completeness is not assumed. -/

open MeasureTheory Filter Topology TopologicalSpace Set

namespace Specs.ProbabilityFoundations.Ch06.FiniteProductConvergence

universe u v
noncomputable section

def rectangleCriterionType : Prop :=
  ∀ {I : Type u} [Fintype I] {S : I → Type v}
    [∀ i, MetricSpace (S i)] [∀ i, MeasurableSpace (S i)]
    [∀ i, BorelSpace (S i)] [∀ i, SeparableSpace (S i)]
    (νs : ℕ → ProbabilityMeasure (∀ i, S i)) (ν : ProbabilityMeasure (∀ i, S i)),
    WeakFramework.weaklyConvergesValue atTop νs ν ↔
      ∀ A : ∀ i, Set (S i),
        (∀ i, ContinuityPartitions.isContinuitySetValue
          (ν.map (Function.eval i) : Measure (S i)) (A i)) →
        Tendsto (fun n => (νs n : Measure (∀ i, S i)) (univ.pi A)) atTop
          (𝓝 ((ν : Measure (∀ i, S i)) (univ.pi A)))

def productCriterionType : Prop :=
  ∀ {I : Type u} [Fintype I] {S : I → Type v}
    [∀ i, MetricSpace (S i)] [∀ i, MeasurableSpace (S i)]
    [∀ i, BorelSpace (S i)] [∀ i, SeparableSpace (S i)]
    (μs : ℕ → ∀ i, ProbabilityMeasure (S i)) (μ : ∀ i, ProbabilityMeasure (S i)),
    WeakFramework.weaklyConvergesValue atTop
      (fun n => ProbabilityMeasure.pi (μs n)) (ProbabilityMeasure.pi μ) ↔
        ∀ i, WeakFramework.weaklyConvergesValue atTop (fun n => μs n i) (μ i)

end
end Specs.ProbabilityFoundations.Ch06.FiniteProductConvergence
