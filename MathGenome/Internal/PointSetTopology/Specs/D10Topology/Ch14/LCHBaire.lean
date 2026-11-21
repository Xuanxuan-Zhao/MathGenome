import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.CategoryInterface
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions

/-!
Independent statements for paper.tex, d10:14:baire-lch.
Local compactness means one compact neighborhood at each point. Compactness
means the finite-subcover property. Neither statement requires nonemptiness,
countability of the topology, or a compatible metric.
-/

universe u

namespace Specs.D10Topology.Ch14.LCHBaire

/-- Every locally compact Hausdorff space is Baire in the source convention. -/
def lch_baire : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    Specs.D10Topology.Ch11.LocalCompactConventions.LCH X →
      Specs.D10Topology.Ch14.CategoryInterface.baireValue X

/-- In particular, every compact Hausdorff space is Baire, including the empty space. -/
def compact_hausdorff_baire : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    Specs.D10Topology.Ch05.Compactness.CoverCompact X → T2Space X →
      Specs.D10Topology.Ch14.CategoryInterface.baireValue X

end Specs.D10Topology.Ch14.LCHBaire
