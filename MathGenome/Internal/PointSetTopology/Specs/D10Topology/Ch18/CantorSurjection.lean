import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.CantorModel
import Mathlib.Topology.MetricSpace.Basic

/-! Independent specification of paper.tex, d10:18:cantor-surjection.
The domain is the canonical positive-indexed binary product with its product
topology. The target may have isolated points, and may be finite or a singleton.
-/

universe u

namespace Specs.D10Topology.Ch18.CantorSurjection

def cantor_surjection : Prop :=
  ∀ (K : Type u) [MetricSpace K] [CompactSpace K] [Nonempty K],
    ∃ f : CantorModel.CantorSpace → K, Continuous f ∧ Function.Surjective f

/-- The nonemptiness condition is also necessary, as noted at the end of
the source proof. -/
def cantor_surjection_iff_nonempty : Prop :=
  ∀ (K : Type u) [MetricSpace K] [CompactSpace K],
    (∃ f : CantorModel.CantorSpace → K, Continuous f ∧ Function.Surjective f) ↔
      Nonempty K

end Specs.D10Topology.Ch18.CantorSurjection
