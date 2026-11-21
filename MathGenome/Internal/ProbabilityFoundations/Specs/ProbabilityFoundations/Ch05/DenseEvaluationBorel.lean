import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.ContinuousPathGeometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! Independent statements for the Borel assertion of `thm:path-borel`,
paper.tex §5.5. The path topology is the canonical compact-open topology,
identified with the uniform metric topology by the upstream geometry result.
The supremum of comaps is precisely the least sigma-algebra making all
specified evaluations measurable. -/

open TopologicalSpace

namespace ProbabilityFoundations.Ch05.Specs

/-- All time evaluations are continuous, including times outside the chosen dense set. -/
def PathEvaluationContinuous : Prop :=
  ∀ (S : Type*) [MetricSpace S] [Nonempty S] [SeparableSpace S]
    (T : ℝ), 0 < T → ∀ t : Set.Icc (0 : ℝ) T,
    Continuous (fun f : C(Set.Icc (0 : ℝ) T, S) => f t)

/-- Evaluations are measurable for the Borel structures on paths and states. -/
def PathEvaluationMeasurable : Prop :=
  ∀ (S : Type*) [MetricSpace S] [Nonempty S] [SeparableSpace S]
    (T : ℝ), 0 < T → ∀ t : Set.Icc (0 : ℝ) T,
    @Measurable C(Set.Icc (0 : ℝ) T, S) S (borel _) (borel S) (fun f => f t)

/-- Any countable dense family of times generates the entire path Borel sigma-algebra.
No endpoint membership or completeness of the state space is assumed. -/
def DenseEvaluationBorel : Prop :=
  ∀ (S : Type*) [MetricSpace S] [Nonempty S] [SeparableSpace S]
    (T : ℝ), 0 < T → ∀ D : Set (Set.Icc (0 : ℝ) T),
    D.Countable → Dense D →
    borel C(Set.Icc (0 : ℝ) T, S) =
      ⨆ t : D, (borel S).comap (fun f : C(Set.Icc (0 : ℝ) T, S) => f t.1)

end ProbabilityFoundations.Ch05.Specs
