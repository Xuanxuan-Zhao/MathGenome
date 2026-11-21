import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetCornerGluing
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RegionalVertexCorners

/-!
Corner gluing for paper.tex 5117–5133, for every original regional
presentation. The upstream local ledger proves occupied-sector geometry,
metric angle transport, refinement invariance and vanishing off vertices.
Here each literal corner term is assigned to its unique original graph vertex,
then finite summation and the loop-sensitive half-edge identity give 2*pi*(E-V).
The independent Spec retains both model kinds and arbitrary compact surfaces.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set
open scoped BigOperators Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData
open P202.MetricData
open P202Specs.SurfaceRegionConstruction P202Specs.GlobalGaussBonnet
open P202Specs.PlanarRegionTopology P202Specs.PlaneTurning
open P202Specs.RegionalVertexCorners

namespace P202.GlobalGaussBonnet.CornerGluing
universe u

/-- The sum at graph vertices recovers every literal corner term: a corner at
an unlisted original point has zero contribution, and a vertex is counted once. -/
theorem cornerTerm_eq_sum_vertices
    {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {S : SmoothManifold 2 kind M}
    (g : RiemannianMetric S) (D : RegionDecomposition S)
    (G : ∀ r, RegionalChartGeometry g D r)
    (A : ∀ r i, ArcPresentation ((D.region r).curve i))
    (s : ∀ r, Fin (D.region r).boundaryCount → ℝ)
    (hs : ∀ r, IsInducedBoundaryOrientation (D.region r) (s r))
    (r : Fin D.regionCount) (i : Fin (D.region r).boundaryCount)
    (k : Fin (A r i).count) :
    cornerTerm g D r (G r) i (A r i) (s r i) k =
      ∑ v, if CornerAt D r i (A r i) k (D.graph.vertex v) then
        cornerTerm g D r (G r) i (A r i) (s r i) k else 0 := by
  classical
  let p := VertexCorners.originalCornerPoint D r i (A r i) k
  have hp : CornerAt D r i (A r i) k p :=
    (VertexCorners.originalCornerPoint_mem D r i (A r i) k).2
  by_cases hvertex : p ∈ range D.graph.vertex
  · obtain ⟨v, hv⟩ := hvertex
    have hvp : CornerAt D r i (A r i) k (D.graph.vertex v) := hv.symm ▸ hp
    symm
    rw [Finset.sum_eq_single v]
    · exact if_pos hvp
    · intro w _ hw
      apply if_neg
      intro hwp
      apply hw
      apply D.graph.vertex_injective
      exact VertexCorners.cornerAt_unique D r i (A r i) k hwp hvp
    · simp
  · have hz := VertexCorners.offVertexContribution_zero g D G A s hs r i k p hp hvertex
    simp only [hz, ite_self, Finset.sum_const_zero]

/-- Finite summation of the complete local ledger over the original vertices. -/
theorem regionalExteriorAngleSum :
    P202Specs.GlobalGaussBonnet.CornerGluingExpected.regionalExteriorAngleSum.{u} := by
  intro kind M _ S _ g D G A s hs
  classical
  calc
    (∑ r, P202Specs.LocalGaussBonnet.exteriorAngleSum
        (G r).metric (G r).orientation (G r).ambientChart (G r).ambientChart_mem
        (D.region r) (A r) (s r)) =
        ∑ v, cornerSumAt g D G A s (D.graph.vertex v) := by
      let f (r : Fin D.regionCount) (i : Fin (D.region r).boundaryCount)
          (k : Fin (A r i).count) (v : Fin D.graph.vertexCount) : ℝ :=
        if CornerAt D r i (A r i) k (D.graph.vertex v) then
          cornerTerm g D r (G r) i (A r i) (s r i) k else 0
      change (∑ r, ∑ i, ∑ k, cornerTerm g D r (G r) i (A r i) (s r i) k) =
        ∑ v, ∑ r, ∑ i, ∑ k, f r i k v
      calc
        _ = ∑ r, ∑ i, ∑ k, ∑ v, f r i k v := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          exact cornerTerm_eq_sum_vertices g D G A s hs r i k
        _ = ∑ r, ∑ i, ∑ v, ∑ k, f r i k v := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = ∑ r, ∑ v, ∑ i, ∑ k, f r i k v := by
          apply Finset.sum_congr rfl
          intro r _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = 2 * Real.pi * ((D.graph.edgeCount : ℝ) - (D.graph.vertexCount : ℝ)) := by
      apply P202.GlobalGaussBonnet.sum_vertex_exterior
      intro v
      simpa only [VertexCorners.vertexDegree_eq_valence] using
        VertexCorners.vertexCornerIdentity g D G A s hs v

end P202.GlobalGaussBonnet.CornerGluing
