import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.GDelta.Basic

/-!
Independent specification for paper.tex:6598–6603.
The domain is the real closed interval with its subspace topology. Consequently
its punctured neighborhood filter approaches from the right at 0, from the left
at 1, and from both sides at interior points. The codomain is scalar, and the
real difference in the denominator is embedded into that scalar field.
`ContinuousMap` on this compact interval carries its usual supremum norm.
-/
open Set Filter
open scoped Topology

namespace ExpandedFA.Supplements.GenericNondifferentiability

abbrev Interval := Set.Icc (0 : ℝ) 1

/-- Existence of a finite scalar limit of the real-parameter secant quotients.
This includes the appropriate one-sided derivative at each endpoint. -/
def HasFiniteDerivative {𝕜 : Type*} [RCLike 𝕜]
    (f : C(Interval, 𝕜)) (x : Interval) : Prop :=
  ∃ d : 𝕜, Tendsto (fun y : Interval =>
    (f y - f x) / (((y : ℝ) - (x : ℝ) : ℝ) : 𝕜)) (𝓝[≠] x) (𝓝 d)

namespace Spec

/-- The nowhere differentiable functions contain a dense G-delta.
The single quantifier over the closed interval includes both endpoints. -/
def GenericNondifferentiability : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜], ∃ G : Set C(Interval, 𝕜),
    Dense G ∧ IsGδ G ∧ ∀ f ∈ G, ∀ x : Interval, ¬ HasFiniteDerivative f x

end Spec
end ExpandedFA.Supplements.GenericNondifferentiability
