import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import Mathlib.MeasureTheory.Measure.Regular

/-!
Independent statements for Proposition 6.1 (paper.tex, lines 1437–1443)
and the Hausdorff consequence for the weak topology of lines 1423–1426.
The measurable space is exactly the Borel sigma algebra. No countability,
completeness, or compact approximation hypothesis is imposed.
-/

open Set MeasureTheory BoundedContinuousFunction

namespace Specs.ProbabilityFoundations.Ch06.BorelRegularity

universe u

/-- Simultaneous closed inner and open outer approximation, in measure. -/
def closedOpenApproximationType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (A : Set S), MeasurableSet A →
    ∀ ε : ℝ, 0 < ε → ∃ F G : Set S,
      IsClosed F ∧ IsOpen G ∧ F ⊆ A ∧ A ⊆ G ∧ μ (G \ F) < ENNReal.ofReal ε

/-- All bounded continuous real integral tests determine a Borel probability law. -/
def probabilityMeasureDeterminationType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ ν : ProbabilityMeasure S),
    (∀ f : S →ᵇ ℝ, (∫ x, f x ∂(μ : Measure S)) = ∫ x, f x ∂(ν : Measure S)) →
    μ = ν

/-- The initial topology of the real integral tests is Hausdorff. -/
def weakTopologyHausdorffType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S],
    @T2Space (ProbabilityMeasure S) (WeakFramework.weakTopologyValue (S := S))

end Specs.ProbabilityFoundations.Ch06.BorelRegularity
