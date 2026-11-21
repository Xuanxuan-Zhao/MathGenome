import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent statements for the geometry part of `thm:path-borel`
(paper.tex, §5.5). Paths have the usual compact-open topology; no
boundedness or completeness assumption is imposed on the state metric.
The subsequent Borel assertion is a separate obligation. -/

open TopologicalSpace

namespace ProbabilityFoundations.Ch05.Specs

/-- Identification of the canonical metric with the source's uniform distance. -/
def UniformDistance : Prop :=
  ∀ (S : Type*) [MetricSpace S] [Nonempty S] [SeparableSpace S]
    (T : ℝ), 0 < T → ∀ (f g : C(Set.Icc (0 : ℝ) T, S)),
    dist f g = ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g t)

/-- The pointwise distances admit a finite real bound, even for unbounded S. -/
def UniformDistanceFinite : Prop :=
  ∀ (S : Type*) [MetricSpace S] [Nonempty S] [SeparableSpace S]
    (T : ℝ), 0 < T → ∀ (f g : C(Set.Icc (0 : ℝ) T, S)),
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, dist (f t) (g t) ≤ M

/-- The topology of that very metric is exactly the compact-open topology. -/
def UniformMetricTopology : Prop :=
  ∀ (S : Type*) [MetricSpace S] [Nonempty S] [SeparableSpace S]
    (T : ℝ), 0 < T →
    (inferInstance : MetricSpace C(Set.Icc (0 : ℝ) T, S)).toUniformSpace.toTopologicalSpace =
      ContinuousMap.compactOpen

/-- Separability for arbitrary separable metric state spaces. -/
def PathSpaceSeparable : Prop :=
  ∀ (S : Type*) [MetricSpace S] [Nonempty S] [SeparableSpace S]
    (T : ℝ), 0 < T → SeparableSpace C(Set.Icc (0 : ℝ) T, S)

/-- Completeness under exactly the additional completeness hypothesis on S. -/
def PathSpaceComplete : Prop :=
  ∀ (S : Type*) [MetricSpace S] [Nonempty S] [SeparableSpace S] [CompleteSpace S]
    (T : ℝ), 0 < T → CompleteSpace C(Set.Icc (0 : ℝ) T, S)

end ProbabilityFoundations.Ch05.Specs
