import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SurfaceRegionConstruction
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.EulerPoincare

/-!
The complete conclusion of `lem:p202-surface-regions`, paper.tex 5003–5091.
The regions in the sum are the actual closures of complementary components
in the original surface, with their subspace topologies. Their planar chart
models are part of `RegionDecomposition`, not replacement spaces assumed to
have the same homology. The Euler invariant is the canonical rational singular
homology invariant; its finite-type domain is a conclusion.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData
universe u

namespace P202Specs.SurfaceRegionsEuler
open P202Specs.SurfaceRegionConstruction P202Specs.EulerPoincare

abbrev regionInterior {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (R : RegionDecomposition S) (j : Fin R.regionCount) :
    Set M := componentSet R.graph.carrierᶜ (R.component j)

abbrev regionClosure {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (R : RegionDecomposition S) (j : Fin R.regionCount) :
    Set M := closure (regionInterior R j)

def EulerConclusion {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (R : RegionDecomposition S) : Prop :=
  ∃ hS : HomologyFiniteType ℚ M,
    ∃ hD : ∀ j : Fin R.regionCount, HomologyFiniteType ℚ (regionClosure R j),
      topologicalEuler M hS =
        (R.graph.vertexCount : ℤ) - (R.graph.edgeCount : ℤ) +
          ∑ j : Fin R.regionCount, topologicalEuler (regionClosure R j) (hD j)

namespace Expected

/-- No connectedness, orientability, nonemptiness, or empty-boundary
assumption is imposed on the original surface. -/
def surfaceRegionsEuler : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M),
    ∃ R : RegionDecomposition S, EulerConclusion R

end Expected
end P202Specs.SurfaceRegionsEuler
