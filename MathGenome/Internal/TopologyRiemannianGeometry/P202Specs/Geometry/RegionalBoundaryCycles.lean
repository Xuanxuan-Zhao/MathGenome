import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ArrangementGraphGeometry

/-!
The genuine boundary-curve output of paper.tex 5061–5074. All curves use the
shared R/Z parametrization and the shared smooth, regular, noncuspidal join
predicate. The frontier is taken in the entire coordinate plane, including
the image of any original surface boundary. Multiple boundary components
are permitted. No regional degree, cycle, curve or PlanarRegion certificate
is an input.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BoundaryData
open P202Specs.PlanarRegionTopology
universe u

namespace P202Specs.SurfaceRegionConstruction

/-- A positive finite family of actual regular Jordan curves exhausting the
full ambient frontier of the specified coordinate domain. -/
structure RegionalBoundaryCurves (U : Set Plane) where
  count : ℕ
  count_pos : 1 ≤ count
  curve : Fin count → RegularJordanCurve
  disjoint : Pairwise (fun i j => Disjoint (curve i).trace (curve j).trace)
  frontier_eq : frontier U = ⋃ i, (curve i).trace

namespace Expected

/-- The actual graph output is supplied by the preceding construction, not
an extra hypothesis on the original compact surface. Every actual component
and every original chart containing its closure are covered. Empty surfaces
have no component indices. No connectedness or orientation is assumed. -/
def regionalBoundaryCycles : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) (D : SmoothSurfaceDouble.SmoothDouble S) (s : Bool)
    (A : Set (ModelChart 2 .euclidean (SmoothSurfaceDouble.SurfaceDouble S))),
    A ⊆ D.manifold.smoothStructure.val → CopySubordinate S D s A →
    ∀ B : CompactSmoothSeam D.manifold,
      B.carrier = SmoothSurfaceDouble.seam (intrinsicBoundary S) →
      ∀ (T : TransverseDiskArrangement D.manifold
          (range (SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
        (H : ArrangementGraphGeometryData S D s T)
        (a : ConnectedComponents (H.graph.carrierᶜ : Set M))
        (e : ModelChart 2 kind M),
        e ∈ S.smoothStructure.val →
        closure (componentSet H.graph.carrierᶜ a) ⊆ e.source →
        Nonempty (RegionalBoundaryCurves (coordinates e '' componentSet H.graph.carrierᶜ a))

end Expected
end P202Specs.SurfaceRegionConstruction
