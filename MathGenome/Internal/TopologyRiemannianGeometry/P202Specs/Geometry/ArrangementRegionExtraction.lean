import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ArrangementGraphGeometry

/-!
Independent full extraction statement for paper.tex 5053–5076. Canonical graph,
component, star, decomposition and arrangement-provenance objects are shared
with the upstream graph stage. No implementation module or parent draft is
imported, and no component region or boundary certificate is assumed.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BoundaryData
universe u

namespace P202Specs.SurfaceRegionConstruction

namespace Expected

/-- Full generic extraction theorem. Empty, disconnected and nonorientable
surfaces and either original model are included. The smooth double and
arrangement are explicit geometric input; graph and region data are outputs. -/
def arrangementRegionExtraction : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) (D : SmoothSurfaceDouble.SmoothDouble S) (s : Bool)
    (A : Set (ModelChart 2 .euclidean (SmoothSurfaceDouble.SurfaceDouble S))),
    A ⊆ D.manifold.smoothStructure.val → CopySubordinate S D s A →
    ∀ (B : CompactSmoothSeam D.manifold),
      B.carrier = SmoothSurfaceDouble.seam (intrinsicBoundary S) →
      ∀ T : TransverseDiskArrangement D.manifold
        (range (SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B,
        ∃ R : RegionDecomposition S, ArrangementExtractionData S D s T R

end Expected
end P202Specs.SurfaceRegionConstruction
