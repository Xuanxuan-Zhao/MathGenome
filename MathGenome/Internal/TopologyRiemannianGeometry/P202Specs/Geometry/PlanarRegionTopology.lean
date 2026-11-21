import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionCornerCollar
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionComponents

/-!
The topology part of the planar-region lemma (paper.tex 4762–4813).
All geometric input and objects are the canonical ones from the foundation.
The two imported independent interfaces state the local corner/collar and
complementary-component conclusions, without assuming them of a region.
The Euler characteristic calculation is allocated separately.
-/

noncomputable section
open Set Topology

namespace P202Specs.PlanarRegionTopology.Expected

/-- Full assigned obligation. None of the geometric conclusions is an
assumption in `PlanarRegion`. This definition is not an axiom. -/
def planarRegionTopology : Prop := ∀ R : PlanarRegion,
  IsCompact R.carrier ∧ IsConnected R.carrier ∧
    interior R.carrier = R.domain ∧ frontier R.carrier = R.boundary ∧
    IsSurfaceWithBoundary R.carrier R.boundary ∧
    LocallyContractibleSpace R.carrier ∧
    Nonempty (BoundaryCollar R.carrier R.boundary) ∧
    InteriorInclusionEquivalence R.carrier ∧
    ∃ S : ComplementData R, BoundaryOrientationConclusion R S.sides

/-- Assembly of the full conclusion from the independently proved geometric
and component results. The unconditional result below is the parent target. -/
def assembly : Prop := localGeometry → complementComponents → planarRegionTopology

end P202Specs.PlanarRegionTopology.Expected
