import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuityPartitions
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.RealDistributionFunctions
import Mathlib.Topology.MetricSpace.Basic

/-! Independent statements for paper.tex 1535–1565. The topology and sigma algebra
are those of the given metric space. Real mass values express convergence of
finite probability masses without imposing any absence of atoms. -/

open MeasureTheory Filter Topology Set Metric TopologicalSpace

namespace Specs.ProbabilityFoundations.Ch06.DeterminingTests

universe u
noncomputable section

def continuityBallBasisType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SeparableSpace S] (μ : ProbabilityMeasure S),
    ∃ B : Set (Set S), B.Countable ∧ IsTopologicalBasis B ∧
      ∀ A ∈ B, ∃ (x : S) (r : ℝ), 0 < r ∧ A = ball x r ∧
        ContinuityPartitions.isContinuitySetValue (μ : Measure S) A

def basisIntersectionCriterionType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SeparableSpace S] (B : Set (Set S)), IsTopologicalBasis B →
    ∀ (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
    (∀ F : Finset (Set S), (∀ A ∈ F, A ∈ B) →
      Tendsto (fun n => (μs n : Measure S).real (⋂ A ∈ F, A)) atTop
        (𝓝 ((μ : Measure S).real (⋂ A ∈ F, A)))) →
    WeakFramework.weaklyConvergesValue atTop μs μ

def distributionFunctionCriterionType : Prop :=
  ∀ (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ),
    WeakFramework.weaklyConvergesValue atTop μs μ ↔
      ∀ t : ℝ,
        ContinuousAt (Ch01.RealDistributionFunctions.distributionFunctionValue
          (μ : Measure ℝ)) t →
        Tendsto (fun n => Ch01.RealDistributionFunctions.distributionFunctionValue
          (μs n : Measure ℝ) t) atTop
          (𝓝 (Ch01.RealDistributionFunctions.distributionFunctionValue (μ : Measure ℝ) t))

end
end Specs.ProbabilityFoundations.Ch06.DeterminingTests
