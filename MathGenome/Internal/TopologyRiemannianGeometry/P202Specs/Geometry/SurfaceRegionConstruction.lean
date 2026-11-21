import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ArrangementRegionExtraction

/-!
Independent interface for the construction and region geometry of
paper.tex 5003–5076. The canonical graph, component, star, chart-disk and
decomposition objects are shared with the upstream construction stages.
No decomposition, triangulation, double, collar or transversality certificate
is a hypothesis of the original construction target. The Euler identity is
allocated separately to SurfaceRegionsEuler.
-/
set_option autoImplicit false
noncomputable section
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData
universe u

namespace P202Specs.SurfaceRegionConstruction.Expected

/-- Every compact smooth surface, with either model and with no connectedness,
orientation or nonemptiness assumption, admits the required decomposition. -/
def construction : Prop := ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  [CompactSpace M] (S : SmoothManifold 2 kind M), Nonempty (RegionDecomposition S)

end P202Specs.SurfaceRegionConstruction.Expected
