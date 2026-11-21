import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.Connectedness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import Mathlib.Topology.Separation.Hausdorff

/-!
Independent statement of paper.tex, `d10:06:filtered-continua`.
The ambient type K is the compact Hausdorff space, and every A i is a
closed subset of K with its induced topology. The index type is arbitrary
and explicitly nonempty. Connectedness is the source's absence of a
separation, using the shared canonical predicate.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch06.FilteredContinua

def filtered_continua : Prop :=
  ∀ {K : Type u} [TopologicalSpace K] [T2Space K]
    {ι : Type v} [Nonempty ι] (A : ι → Set K),
    Specs.D10Topology.Ch05.Compactness.CoverCompact K →
    (∀ i, (A i).Nonempty) →
    (∀ i, IsClosed (A i)) →
    (∀ i, _root_.D10Topology.Ch06.ConnectednessData.ConnectedSubset (A i)) →
    (∀ i j, ∃ k, A k ⊆ A i ∩ A j) →
    (⋂ i, A i).Nonempty ∧
      _root_.D10Topology.Ch06.ConnectednessData.ConnectedSubset (⋂ i, A i)

end Specs.D10Topology.Ch06.FilteredContinua
