import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.Cauchy

/-!
Independent specification of `fa2:p1:baire-one`, paper.tex:6572–6577.
The set is the full set of ambient continuity points of the given pointwise
limit. No nonemptiness, separability, or uniform convergence is assumed.
-/

open Set Filter TopologicalSpace
open scoped Topology

universe u

namespace Specs.ExpandedFA.Supplements.BaireOneContinuity

/-- The continuity points of a pointwise limit of continuous real functions on
any complete metric space form a dense Gδ set, including for the empty space. -/
def continuityPointsDenseGDelta : Prop :=
  ∀ {X : Type u} [MetricSpace X] [CompleteSpace X]
    (fseq : ℕ → X → ℝ) (f : X → ℝ),
    (∀ n, Continuous (fseq n)) →
    (∀ x, Tendsto (fun n => fseq n x) atTop (𝓝 (f x))) →
    Dense {x | ContinuousAt f x} ∧ IsGδ {x | ContinuousAt f x}

end Specs.ExpandedFA.Supplements.BaireOneContinuity
