import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.ParacompactNormal

/-!
Independent statement of paper.tex, d10:15:shrinking.
The shrinking has precisely the original index type, with indexed local
finiteness counting repeated members. Empty spaces, index types and members
are allowed. Hausdorffness is separate from paracompactness.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch15.IndexedShrinking

open Specs.D10Topology.Ch15.LocallyFiniteConventions
open Specs.D10Topology.Ch07.SeparationConventions

def indexed_shrinking : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X],
    Paracompact X → t2Value X →
    ∀ U : I → Set X, (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
      ∃ V : I → Set X, (∀ i, IsOpen (V i)) ∧ LocallyFiniteFamily V ∧
        (⋃ i, V i) = univ ∧ ∀ i, closure (V i) ⊆ U i

end Specs.D10Topology.Ch15.IndexedShrinking
