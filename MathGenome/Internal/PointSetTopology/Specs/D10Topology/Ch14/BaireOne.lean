import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.CategoryInterface
import Mathlib.Topology.MetricSpace.Defs

/-! The full continuity set in paper.tex, d10:14:baire-one.
The domain has only a topology and the Baire property. In particular it
need not be metrizable, first countable, separated, or nonempty. -/

open Set Filter
open scoped Topology
universe u v

namespace Specs.D10Topology.Ch14.BaireOne

def baire_one_continuity_set : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y],
    CategoryInterface.baireValue X →
    ∀ (g : ℕ → X → Y) (f : X → Y),
      (∀ n, Continuous (g n)) →
      (∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))) →
      Dense {x | ContinuousAt f x} ∧ IsGδ {x | ContinuousAt f x} ∧
        CategoryInterface.residualValue {x | ContinuousAt f x}

end Specs.D10Topology.Ch14.BaireOne
