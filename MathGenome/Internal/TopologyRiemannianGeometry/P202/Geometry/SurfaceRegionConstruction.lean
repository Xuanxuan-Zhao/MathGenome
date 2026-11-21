import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SurfaceRegionConstruction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothSurfaceDouble
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.TransverseDiskArrangement
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ArrangementRegionExtraction
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.TransversePreimage

/-!
The construction and region geometry of paper.tex 5003–5076. The actual
collar-built double, generic transverse disk arrangement and regional extraction
are supplied by the upstream stages. Their canonical objects are shared through
the independent Specs. This module supplies the original-chart subordination
and seam adapters and assembles the unconditional construction.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.BoundaryData SmoothManifolds.MapData SmoothManifolds.MapClassData
open P202Specs.SurfaceRegionConstruction
universe u

namespace P202.SurfaceRegionConstruction
variable {X : Type u} [TopologicalSpace X]

/-- The complete empty-surface case uses the same graph and region objects. -/
def emptyDecomposition {kind : ModelKind} [IsEmpty X]
    (S : SmoothManifold 2 kind X) : RegionDecomposition S where
  graph := EmbeddedGraph.empty S
  contains_boundary := fun p => isEmptyElim p
  regionCount := 0
  component := by
    letI : IsEmpty (ConnectedComponents ((EmbeddedGraph.empty S).carrierᶜ : Set X)) :=
      ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
    exact Equiv.equivOfIsEmpty _ _
  region := fun i => Fin.elim0 i
  chart := fun i => Fin.elim0 i
  chart_mem := fun i => Fin.elim0 i
  closure_in_chart := fun i => Fin.elim0 i
  domain_coordinates := fun i => Fin.elim0 i
  closure_coordinates := fun i => Fin.elim0 i
  open_components := fun i => Fin.elim0 i
  compact_closures := fun i => Fin.elim0 i
  connected_closures := fun i => Fin.elim0 i
  frontiers_on_graph := fun i => Fin.elim0 i
  disjoint_interiors := fun i => Fin.elim0 i
  sectors := fun p => isEmptyElim p
  empty_case := fun _ => ⟨rfl, rfl, rfl⟩


/-- Double charts can cover the designated copy while refining original
surface charts on that entire copy-preimage. This is the subordination needed
to put each extracted region in one original chart. -/
theorem exists_copySubordinate_chartFamily {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool) :
    ∃ A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)),
      A ⊆ D.manifold.smoothStructure.val ∧ CopySubordinate S D s A ∧
      ∀ p ∈ range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s),
        ∃ d ∈ A, p ∈ d.source := by
  let A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)) :=
    {d | d ∈ D.manifold.smoothStructure.val ∧
      ∃ e ∈ S.smoothStructure.val,
        P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' d.source ⊆ e.source}
  refine ⟨A, fun _ hd => hd.1, fun _ hd => hd.2, ?_⟩
  rintro p ⟨x, rfl⟩
  obtain ⟨e, he, hx⟩ := S.smoothStructure.property.1.1 x
  obtain ⟨d, hd, hxd, hde⟩ := D.chart_refinement s e he x hx
  exact ⟨d, ⟨hd, e, he, hde⟩, hxd⟩

namespace Seam
open P202Specs.SmoothSurfaceDouble
variable {M : Type u} [TopologicalSpace M] {kind : ModelKind}
    {S : SmoothManifold 2 kind M}

/-- Projection onto boundary coordinates is a smooth local left inverse to
seam inclusion, so the seam is immersed as well as topologically embedded. -/
theorem seamMap_embedding (D : SmoothDouble S) :
    IsSmoothEmbedding D.boundary D.manifold (seamMap (intrinsicBoundary S)) := by
  refine ⟨D.seam_smooth, D.seam_closedEmbedding.injective, ?_,
    ⟨D.seam_closedEmbedding.isEmbedding.toHomeomorph, fun _ => rfl⟩⟩
  intro p
  obtain ⟨b,hb,hpb⟩ := D.boundary.smoothStructure.property.1.1 p
  obtain ⟨d,hd,hcoords,_⟩ := P202.SmoothSurfaceDouble.seam_standard_coordinates D b hb
  apply SmoothManifolds.SliceStructures.immersion_of_coordinate_retraction
    D.boundary D.manifold (seamMap (intrinsicBoundary S)) D.seam_smooth p b d
    hb hd hpb (hcoords p hpb).1
  refine ⟨univ,isOpen_univ,mem_univ _, Fin.init, ?_, ?_⟩
  · exact (contDiff_pi.mpr (fun (i : Fin 1) =>
      contDiff_apply ℝ (fun _ : Fin 2 => ℝ) i.castSucc)).contDiffOn
  · filter_upwards [b.open_source.mem_nhds hpb] with q hq
    rw [(hcoords q hq).2]
    exact Fin.init_snoc _ _

def boundaryToSeam (D : SmoothDouble S) :
    intrinsicBoundary S ≃ₜ seam (intrinsicBoundary S) :=
  D.seam_closedEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P202.SmoothSurfaceDouble.seam_eq_range
      (intrinsicBoundary S)).symm)

theorem exists_compactSmoothSeam (D : SmoothDouble S) :
    ∃ B : P202Specs.SurfaceRegionConstruction.CompactSmoothSeam D.manifold,
      B.carrier = seam (intrinsicBoundary S) := by
  let H := boundaryToSeam D
  obtain ⟨Q,hQ,_⟩ := SmoothManifolds.TransversePreimage.transport_embedded
    D.boundary D.manifold (seamMap (intrinsicBoundary S)) (seamMap_embedding D) H
  have hfun : (seamMap (intrinsicBoundary S) ∘ H.symm) =
      (Subtype.val : seam (intrinsicBoundary S) → SurfaceDouble S) := by
    funext x
    have h := congrArg Subtype.val (H.apply_symm_apply x)
    exact h
  rw [hfun] at hQ
  refine ⟨⟨seam (intrinsicBoundary S), ?_, Q,hQ⟩,rfl⟩
  let := D.seam_compact
  rw [P202.SmoothSurfaceDouble.seam_eq_range]
  exact isCompact_range D.seam_closedEmbedding.continuous
end Seam

/-- The finite embedded graph and chartwise planar regions on every compact
smooth surface, including empty, disconnected and nonorientable surfaces. -/
theorem construction : Expected.construction.{u} := by
  intro kind M _ _ S
  obtain ⟨D⟩ := P202.SmoothSurfaceDouble.construction S
  obtain ⟨A, hA, hsub, hcover⟩ := exists_copySubordinate_chartFamily S D false
  obtain ⟨B, hB⟩ := Seam.exists_compactSmoothSeam D
  have hK : IsCompact (range (P202Specs.SmoothSurfaceDouble.copy
      (intrinsicBoundary S) false)) :=
    isCompact_range (D.copy_closedEmbedding false).continuous
  obtain ⟨T⟩ := transverseDiskArrangement D.manifold _ hK A hA hcover B
  obtain ⟨R, _⟩ := arrangementRegionExtraction S D false A hA hsub B hB T
  exact ⟨R⟩

end P202.SurfaceRegionConstruction
