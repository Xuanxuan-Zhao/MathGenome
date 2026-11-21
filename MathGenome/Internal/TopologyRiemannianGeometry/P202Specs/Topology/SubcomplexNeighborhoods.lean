import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures

/-!
The first conclusion of paper.tex, Proposition `prop:p202-cw-neighborhood`.
The homotopy uses the ordinary product topology and takes values in the
neighborhood itself. No restriction on the number or dimensions of cells is
made, and neither the subcomplex nor its complement is assumed nonempty.
-/

open Set
universe u

namespace P202.Cellular

/-- An actual strong deformation retraction of `W` onto the ambient subset `A`.
The final membership condition, together with `fixed`, makes the terminal map
a retraction onto all of `A`. -/
def StrongDeformationRetracts {X : Type u} [TopologicalSpace X]
    (A W : Set X) : Prop :=
  A ⊆ W ∧ ∃ H : C(W × Interval, W),
    (∀ x : W, H (x, 0) = x) ∧
    (∀ x : W, (H (x, 1)).1 ∈ A) ∧
    (∀ (x : W) (t : Interval), x.1 ∈ A → H (x, t) = x)

end P202.Cellular

namespace P202Specs.Topology.SubcomplexNeighborhoods
open P202.Cellular

/-- Every subcomplex of an arbitrary Hausdorff CW complex strongly deformation
retracts from an open neighborhood. -/
def subcomplexNeighborhood : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X] (A : Subcomplex X),
    ∃ W : Set X, IsOpen W ∧ StrongDeformationRetracts A.carrier W

end P202Specs.Topology.SubcomplexNeighborhoods
