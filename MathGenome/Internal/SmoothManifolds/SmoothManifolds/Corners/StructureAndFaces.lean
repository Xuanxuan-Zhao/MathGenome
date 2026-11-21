import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Corners.FaceOrientations
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.StructureAndFaces

/-! Assembly of the accepted local geometry, products, and outward-first
orientations for M10.06, on their shared canonical corner objects. -/

namespace SmoothManifolds.CornerAssembly

theorem local_geometry :
    Specs.SmoothManifolds.Corners.StructureAndFaces.local_geometryType :=
  ⟨SmoothManifolds.Corners.corner_atlas_extension,
   SmoothManifolds.Corners.model_corner_structure,
   SmoothManifolds.Corners.empty_corner_structure,
   SmoothManifolds.Corners.countable_chart_cover,
   SmoothManifolds.Corners.locally_compact,
   SmoothManifolds.Corners.model_velocity_cone,
   SmoothManifolds.Corners.model_lineality,
   SmoothManifolds.Corners.model_lineality_codimension,
   SmoothManifolds.Corners.transition_cone,
   SmoothManifolds.Corners.cone_facets,
   SmoothManifolds.Corners.chart_depth,
   SmoothManifolds.Corners.coordinate_germs_injective,
   SmoothManifolds.Corners.chart_face_germ_transition,
   SmoothManifolds.Corners.chart_face_germs,
   SmoothManifolds.Corners.local_face_cardinality,
   SmoothManifolds.Corners.face_projection_continuous,
   SmoothManifolds.Corners.resolved_face_hausdorff,
   SmoothManifolds.Corners.resolved_face_second_countable,
   SmoothManifolds.Corners.face_sheet_embedding,
   SmoothManifolds.Corners.face_projection_proper,
   SmoothManifolds.Corners.face_compact_support,
   SmoothManifolds.Corners.resolved_corner_structure,
   SmoothManifolds.Corners.face_projection_smooth,
   SmoothManifolds.Corners.model_face_projection_proper,
   SmoothManifolds.Corners.zero_faces,
   SmoothManifolds.Corners.coordinate_face_chart,
   SmoothManifolds.Corners.model_face_compact_support,
   SmoothManifolds.CornerExamples.simplex_corner_structure,
   SmoothManifolds.CornerExamples.simplex_charts_affine,
   SmoothManifolds.CornerExamples.box_corner_structure,
   SmoothManifolds.CornerExamples.box_corner_charts,
   SmoothManifolds.CornerExamples.square_corner_two_faces⟩

theorem corner_products :
    Specs.SmoothManifolds.Corners.StructureAndFaces.corner_productsType :=
  ⟨SmoothManifolds.CornerProducts.orthant_product_coordinates,
   SmoothManifolds.CornerProducts.product_chart,
   SmoothManifolds.CornerProducts.product_atlas,
   SmoothManifolds.CornerProducts.product_corner_structure,
   SmoothManifolds.CornerProducts.ordinary_model_coordinates,
   SmoothManifolds.CornerProducts.ordinary_corner_bridge,
   SmoothManifolds.CornerProducts.product_projections,
   SmoothManifolds.CornerProducts.product_inclusions,
   SmoothManifolds.CornerProducts.boundary_product,
   SmoothManifolds.CornerProducts.coordinate_tangent_sum,
   SmoothManifolds.CornerProducts.transition_derivative,
   SmoothManifolds.CornerProducts.labelled_product_coordinates,
   SmoothManifolds.CornerProducts.product_face_germs,
   SmoothManifolds.CornerProducts.interval_charts,
   SmoothManifolds.CornerProducts.interval_boundary_product,
   SmoothManifolds.CornerProducts.boundary_product_original_charts,
   SmoothManifolds.CornerProducts.product_canonical,
   SmoothManifolds.CornerProducts.ordinary_canonical,
   SmoothManifolds.CornerProducts.ordinary_boundary_faces⟩

theorem face_orientations :
    Specs.SmoothManifolds.Corners.StructureAndFaces.face_orientationsType :=
  ⟨SmoothManifolds.CornerFaceOrientations.orientation_extension,
   SmoothManifolds.CornerFaceOrientations.normal_half_line,
   SmoothManifolds.CornerFaceOrientations.outward_independent,
   SmoothManifolds.CornerFaceOrientations.coordinate_face_sign,
   SmoothManifolds.CornerFaceOrientations.cone_face_orientation,
   SmoothManifolds.CornerFaceOrientations.face_sign_gluing,
   SmoothManifolds.CornerFaceOrientations.resolved_orientation,
   SmoothManifolds.CornerFaceOrientations.resolved_orientation_unique,
   SmoothManifolds.CornerFaceOrientations.normal_quotient_transport,
   SmoothManifolds.CornerFaceOrientations.local_face_ray,
   SmoothManifolds.CornerFaceOrientations.ordinary_orientation,
   SmoothManifolds.CornerFaceOrientations.ordinary_orientation_equiv,
   SmoothManifolds.CornerFaceOrientations.product_orientation,
   SmoothManifolds.CornerFaceOrientations.local_product_ray,
   SmoothManifolds.CornerFaceOrientations.product_left_wedge,
   SmoothManifolds.CornerFaceOrientations.product_right_wedge,
   SmoothManifolds.CornerFaceOrientations.simplex_source_orientation,
   SmoothManifolds.CornerFaceOrientations.box_source_orientation,
   SmoothManifolds.CornerFaceOrientations.interval_source_orientation,
   SmoothManifolds.CornerFaceOrientations.interval_resolved_endpoints,
   SmoothManifolds.CornerFaceOrientations.product_orientation_coordinates_independent,
   SmoothManifolds.CornerFaceOrientations.product_orientation_all_coordinates,
   SmoothManifolds.CornerFaceOrientations.product_left_resolved_sheet_orientation,
   SmoothManifolds.CornerFaceOrientations.product_right_resolved_sheet_orientation,
   SmoothManifolds.CornerFaceOrientations.product_factor_face_germs_distinct⟩

open ModelData CornerData CornerProductData CornerOrientationData OrientationData Set
open scoped Classical

theorem resolved_oriented_faces :
    Specs.SmoothManifolds.Corners.StructureAndFaces.resolved_oriented_facesType := by
  intro n M _ S o
  obtain ⟨T, b, hb⟩ := CornerFaceOrientations.resolved_orientation o
  refine ⟨T, b, hb, Corners.face_projection_smooth S T hb.1,
    Corners.face_projection_proper S, ?_⟩
  intro F _ s hs
  exact Corners.face_compact_support S s hs

theorem ordinary_oriented_boundary_product :
    Specs.SmoothManifolds.Corners.StructureAndFaces.ordinary_oriented_boundary_productType := by
  intro n m a b M N _ _ S T s t
  obtain ⟨E, F, R, Q, C, P, hR, hQ, hP, hfst, hsnd, hleft, hright, hRfaces,
    hQfaces⟩ := CornerProducts.boundary_product S T
  have hRsub : ordinaryCornerAtlas E S.smoothStructure.val ⊆ R.atlas := by
    rw [hR]
    exact Corners.cornerAtlas_subset_maximalExtension
      (CornerProducts.ordinary_atlas E S.smoothStructure.property.1)
  have hQsub : ordinaryCornerAtlas F T.smoothStructure.val ⊆ Q.atlas := by
    rw [hQ]
    exact Corners.cornerAtlas_subset_maximalExtension
      (CornerProducts.ordinary_atlas F T.smoothStructure.property.1)
  obtain ⟨eR, heR⟩ := CornerFaceOrientations.ordinary_orientation_equiv S E R hRsub
  obtain ⟨eQ, heQ⟩ := CornerFaceOrientations.ordinary_orientation_equiv T F Q hQsub
  let oR := eR.symm s
  let oQ := eQ.symm t
  have hoR : IsOrdinaryOrientation S E R hRsub oR s := by
    simpa only [oR, Equiv.apply_symm_apply] using heR (eR.symm s)
  have hoQ : IsOrdinaryOrientation T F Q hQsub oQ t := by
    simpa only [oQ, Equiv.apply_symm_apply] using heQ (eQ.symm t)
  obtain ⟨oP, hoP, _⟩ :=
    CornerFaceOrientations.product_orientation_all_coordinates R Q C P hP oR oQ
  exact ⟨E, F, R, Q, C, P, hRsub, hQsub, oR, oQ, oP,
    hR, hQ, hP, hoR, hoQ, (hoP C).2, hoP, hfst, hsnd, hleft, hright, hRfaces, hQfaces⟩

theorem structure_and_faces :
    Specs.SmoothManifolds.Corners.StructureAndFaces.structure_and_facesType :=
  ⟨local_geometry, corner_products, face_orientations, resolved_oriented_faces,
    ordinary_oriented_boundary_product⟩

end SmoothManifolds.CornerAssembly
