import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.Foundations

/-! Polygonal plane drawings and their actual sphere-complement faces.
The canonical geometric definitions are in the independent Specs module. -/

universe u
noncomputable section

namespace FiniteCombinatorics.Graph.Plane

abbrev Point :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.Point

abbrev Sphere :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.Sphere

abbrev sphereHomeomorph :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.sphereHomeomorph

abbrev IsPolygonal :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.IsPolygonal

abbrev IsSimplePolygonalArc :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.IsSimplePolygonalArc

abbrev PlaneEmbedding :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.Drawing

abbrev Planar :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.Planar

abbrev planeImage :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.planeImage

abbrev sphereImage :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.sphereImage

abbrev PlaneComplement :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.PlaneComplement

abbrev SphereComplement :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.SphereComplement

abbrev PlaneFace :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.PlaneFace

abbrev Face :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.Face

abbrev faceRegion :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.faceRegion

abbrev unboundedFace :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.unboundedFace

abbrev unboundedRegion :=
  @Specs.FiniteCombinatorics.Graph.Plane.Foundations.unboundedRegion

theorem polygonal_arc_endpoints :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.polygonal_arc_endpointsType := by
  rintro a b s ⟨_, p, _, hps⟩
  constructor
  · rw [← hps]
    exact ⟨0, p.source⟩
  · rw [← hps]
    exact ⟨1, p.target⟩

theorem polygonal_arc_reverse :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.polygonal_arc_reverseType := by
  rintro a b s ⟨hs, p, hp, hps⟩
  exact ⟨hs, p.symm, hp.comp unitInterval.symm_involutive.injective,
    p.symm_range.trans hps⟩

theorem vertices_distinct :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.vertices_distinctType := by
  intro V _ G D a b
  exact D.point_injective.eq_iff

theorem simple_polygonal_edge :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.simple_polygonal_edgeType := by
  intro V _ G D a b h
  exact D.edge_arc a b h

theorem vertex_on_edge :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.vertex_on_edgeType := by
  intro V _ G D a b v h
  exact (D.vertex_edge ⟨s(a, b), h⟩ v).trans Sym2.mem_iff

theorem edge_intersection :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.edge_intersectionType := by
  intro V _ G D e f h
  exact D.edge_intersection e f h

theorem planar_iff :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.planar_iffType := by
  intro V _ G
  rfl

theorem sphere_image_membership :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.sphere_image_membershipType := by
  intro V _ G D x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact OnePoint.coe_injective heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem infinity_not_in_image :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.infinity_not_in_imageType := by
  intro V _ G D
  exact OnePoint.infty_notMem_image_coe

theorem face_region_component :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.face_region_componentType := by
  intro V _ G D x
  change Subtype.val '' {y : SphereComplement D | ConnectedComponents.mk y =
    ConnectedComponents.mk x} = connectedComponentIn (sphereImage D)ᶜ x.val
  rw [connectedComponentIn_eq_image x.property]
  congr 1
  ext y
  exact ConnectedComponents.coe_eq_coe'

theorem face_region_connected :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.face_region_connectedType := by
  intro V _ G D F
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe F
  rw [face_region_component D x]
  exact isConnected_connectedComponentIn_iff.mpr x.property

theorem face_region_subset :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.face_region_subsetType := by
  intro V _ G D F y hy
  obtain ⟨x, _, rfl⟩ := hy
  exact x.property

theorem unbounded_face_component :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.unbounded_face_componentType := by
  intro V _ G D
  exact face_region_component D ⟨OnePoint.infty, OnePoint.infty_notMem_image_coe⟩

theorem unbounded_region_iff :
    Specs.FiniteCombinatorics.Graph.Plane.Foundations.unbounded_region_iffType := by
  intro V _ G D x
  exact Iff.of_eq (congrArg (fun s : Set Sphere => OnePoint.some x ∈ s)
    (unbounded_face_component D))

end FiniteCombinatorics.Graph.Plane
