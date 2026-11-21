import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions
import Mathlib.Topology.MetricSpace.Basic

/-!
Independent statement of paper.tex, Lemma d10:15:metric-sigma.
The refinement is indexed by a natural-number layer and an original cover
index. Its local discreteness counts indices, including repeated sets.
No countability of the original cover or nonemptiness of the space is assumed.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch15.MetricSigmaRefinement

open Specs.D10Topology.Ch15.LocallyFiniteConventions

/-- Every metric open cover has an open, sigma-locally discrete refinement.
The extra final condition records that the second coordinate assigns each
refining member to an original cover member. -/
def metric_sigma_refinement : Prop :=
  ∀ {X : Type u} {I : Type v} [MetricSpace X] (U : I → Set X),
    (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
    ∃ V : ℕ × I → Set X,
      (∀ j, IsOpen (V j)) ∧ CoverRefinement U V ∧
        SigmaLocallyDiscrete V ∧ ∀ j, V j ⊆ U j.2

end Specs.D10Topology.Ch15.MetricSigmaRefinement
