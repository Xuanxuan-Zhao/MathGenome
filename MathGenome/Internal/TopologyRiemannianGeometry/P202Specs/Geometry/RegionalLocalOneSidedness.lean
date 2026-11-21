import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ArrangementGraphGeometry

/-! Independent statement for paper.tex 5061–5074 and 4762–4772.
The domain below is the coordinate image of an actual global complementary
component of the supplied graph. The graph and its link to the actual
arrangement are the upstream graph-stage output. No regional boundary curves,
collars, planar-region values or topology of region closures are assumed.
All coordinate closures and frontiers are in the full ambient plane.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BoundaryData
open P202Specs.PlanarRegionTopology (Plane LocallyOneSided)
universe u

namespace P202Specs.SurfaceRegionConstruction.Expected

/-- Actual component domains in every original chart containing the closure,
including at the seam and at interior points of half-space charts. No
orientation or connectedness of the original compact surface is required. -/
def regionalLocalOneSidedness : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) (D : SmoothSurfaceDouble.SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold},
    B.carrier = SmoothSurfaceDouble.seam (intrinsicBoundary S) →
    ∀ (T : TransverseDiskArrangement D.manifold
        (range (SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
      (H : ArrangementGraphGeometryData S D s T)
      (a : ConnectedComponents (H.graph.carrierᶜ : Set M))
      (e : ModelChart 2 kind M),
      e ∈ S.smoothStructure.val →
      closure (componentSet H.graph.carrierᶜ a) ⊆ e.source →
      let C := componentSet H.graph.carrierᶜ a
      let U := coordinates e '' C
      U.Nonempty ∧ IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
        closure U = coordinates e '' closure C ∧
        frontier U = coordinates e '' frontier C ∧
        (frontier U).Nonempty ∧ LocallyOneSided U

end P202Specs.SurfaceRegionConstruction.Expected
