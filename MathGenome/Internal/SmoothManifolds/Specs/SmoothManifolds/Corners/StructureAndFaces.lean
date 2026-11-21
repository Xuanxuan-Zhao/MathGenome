import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.FaceOrientations

/-! The complete geometric and orientation interface for paper.tex M10.06.

Canonical corner objects are imported from the accepted geometric foundation.
The proposition aliases below retain the original parent interface and collect
the accepted product and orientation statements without redefining their objects.
The Stokes integral itself is allocated to SmoothManifolds.Corners.Stokes. -/

namespace Specs.SmoothManifolds.Corners.StructureAndFaces

universe u v

def corner_atlas_extensionType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.corner_atlas_extensionType.{u}

def model_corner_structureType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_corner_structureType

def empty_corner_structureType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.empty_corner_structureType

def countable_chart_coverType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.countable_chart_coverType.{u}

def locally_compactType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.locally_compactType.{u}

def model_velocity_coneType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_velocity_coneType

def model_linealityType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_linealityType

def model_lineality_codimensionType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_lineality_codimensionType

def transition_coneType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.transition_coneType

def cone_facetsType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.cone_facetsType

def chart_depthType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.chart_depthType.{u}

def coordinate_germs_injectiveType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.coordinate_germs_injectiveType

def chart_face_germ_transitionType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.chart_face_germ_transitionType.{u}

def chart_face_germsType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.chart_face_germsType.{u}

def local_face_cardinalityType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.local_face_cardinalityType.{u}

def face_projection_continuousType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_projection_continuousType.{u}

def resolved_face_hausdorffType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.resolved_face_hausdorffType.{u}

def resolved_face_second_countableType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.resolved_face_second_countableType.{u}

def face_sheet_embeddingType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_sheet_embeddingType.{u}

def face_projection_properType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_projection_properType.{u}

def face_compact_supportType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_compact_supportType.{u, v}

def resolved_corner_structureType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.resolved_corner_structureType.{u}

def face_projection_smoothType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_projection_smoothType.{u}

def model_face_projection_properType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_face_projection_properType

def zero_facesType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.zero_facesType.{u}

def coordinate_face_chartType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.coordinate_face_chartType

def model_face_compact_supportType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_face_compact_supportType.{u}

def simplex_corner_structureType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.simplex_corner_structureType

def simplex_charts_affineType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.simplex_charts_affineType

def box_corner_structureType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.box_corner_structureType

def box_corner_chartsType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.box_corner_chartsType

def square_corner_two_facesType : Prop :=
  Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.square_corner_two_facesType

/-- All claims of the accepted LocalAndResolvedGeometry interface, with their full hypotheses. -/
def local_geometryType : Prop :=
  corner_atlas_extensionType.{u} ∧
  model_corner_structureType ∧
  empty_corner_structureType ∧
  countable_chart_coverType.{u} ∧
  locally_compactType.{u} ∧
  model_velocity_coneType ∧
  model_linealityType ∧
  model_lineality_codimensionType ∧
  transition_coneType ∧
  cone_facetsType ∧
  chart_depthType.{u} ∧
  coordinate_germs_injectiveType ∧
  chart_face_germ_transitionType.{u} ∧
  chart_face_germsType.{u} ∧
  local_face_cardinalityType.{u} ∧
  face_projection_continuousType.{u} ∧
  resolved_face_hausdorffType.{u} ∧
  resolved_face_second_countableType.{u} ∧
  face_sheet_embeddingType.{u} ∧
  face_projection_properType.{u} ∧
  face_compact_supportType.{u, v} ∧
  resolved_corner_structureType.{u} ∧
  face_projection_smoothType.{u} ∧
  model_face_projection_properType ∧
  zero_facesType.{u} ∧
  coordinate_face_chartType ∧
  model_face_compact_supportType.{u} ∧
  simplex_corner_structureType ∧
  simplex_charts_affineType ∧
  box_corner_structureType ∧
  box_corner_chartsType ∧
  square_corner_two_facesType

def orthant_product_coordinatesType : Prop :=
  Specs.SmoothManifolds.Corners.Products.orthant_product_coordinatesType

def product_chartType : Prop :=
  Specs.SmoothManifolds.Corners.Products.product_chartType.{u, v}

def product_atlasType : Prop :=
  Specs.SmoothManifolds.Corners.Products.product_atlasType.{u, v}

def product_corner_structureType : Prop :=
  Specs.SmoothManifolds.Corners.Products.product_corner_structureType.{u, v}

def ordinary_model_coordinatesType : Prop :=
  Specs.SmoothManifolds.Corners.Products.ordinary_model_coordinatesType

def ordinary_corner_bridgeType : Prop :=
  Specs.SmoothManifolds.Corners.Products.ordinary_corner_bridgeType.{u}

def product_projectionsType : Prop :=
  Specs.SmoothManifolds.Corners.Products.product_projectionsType.{u}

def product_inclusionsType : Prop :=
  Specs.SmoothManifolds.Corners.Products.product_inclusionsType.{u}

def boundary_productType : Prop :=
  Specs.SmoothManifolds.Corners.Products.boundary_productType.{u}

def coordinate_tangent_sumType : Prop :=
  Specs.SmoothManifolds.Corners.Products.coordinate_tangent_sumType.{u, v}

def transition_derivativeType : Prop :=
  Specs.SmoothManifolds.Corners.Products.transition_derivativeType

def labelled_product_coordinatesType : Prop :=
  Specs.SmoothManifolds.Corners.Products.labelled_product_coordinatesType

def product_face_germsType : Prop :=
  Specs.SmoothManifolds.Corners.Products.product_face_germsType.{u}

def interval_chartsType : Prop :=
  Specs.SmoothManifolds.Corners.Products.interval_chartsType

def interval_boundary_productType : Prop :=
  Specs.SmoothManifolds.Corners.Products.interval_boundary_productType

def boundary_product_original_chartsType : Prop :=
  Specs.SmoothManifolds.Corners.Products.boundary_product_original_chartsType.{u}

def product_canonicalType : Prop :=
  Specs.SmoothManifolds.Corners.Products.product_canonicalType.{u, v}

def ordinary_canonicalType : Prop :=
  Specs.SmoothManifolds.Corners.Products.ordinary_canonicalType.{u}

def ordinary_boundary_facesType : Prop :=
  Specs.SmoothManifolds.Corners.Products.ordinary_boundary_facesType.{u}

/-- All claims of the accepted Products interface, with their full hypotheses. -/
def corner_productsType : Prop :=
  orthant_product_coordinatesType ∧
  product_chartType.{u, v} ∧
  product_atlasType.{u, v} ∧
  product_corner_structureType.{u, v} ∧
  ordinary_model_coordinatesType ∧
  ordinary_corner_bridgeType.{u} ∧
  product_projectionsType.{u} ∧
  product_inclusionsType.{u} ∧
  boundary_productType.{u} ∧
  coordinate_tangent_sumType.{u, v} ∧
  transition_derivativeType ∧
  labelled_product_coordinatesType ∧
  product_face_germsType.{u} ∧
  interval_chartsType ∧
  interval_boundary_productType ∧
  boundary_product_original_chartsType.{u} ∧
  product_canonicalType.{u, v} ∧
  ordinary_canonicalType.{u} ∧
  ordinary_boundary_facesType.{u}

def orientation_extensionType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.orientation_extensionType.{u}

def normal_half_lineType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.normal_half_lineType

def outward_independentType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.outward_independentType

def coordinate_face_signType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.coordinate_face_signType

def cone_face_orientationType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.cone_face_orientationType

def face_sign_gluingType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.face_sign_gluingType

def resolved_orientationType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.resolved_orientationType.{u}

def resolved_orientation_uniqueType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.resolved_orientation_uniqueType.{u}

def normal_quotient_transportType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.normal_quotient_transportType

def local_face_rayType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.local_face_rayType

def ordinary_orientationType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.ordinary_orientationType.{u}

def ordinary_orientation_equivType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.ordinary_orientation_equivType.{u}

def product_orientationType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.product_orientationType.{u, v}

def local_product_rayType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.local_product_rayType.{u, v}

def product_left_wedgeType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.product_left_wedgeType

def product_right_wedgeType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.product_right_wedgeType

def simplex_source_orientationType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.simplex_source_orientationType

def box_source_orientationType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.box_source_orientationType

def interval_source_orientationType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.interval_source_orientationType

def interval_resolved_endpointsType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.interval_resolved_endpointsType

def product_orientation_coordinates_independentType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.product_orientation_coordinates_independentType.{u, v}

def product_orientation_all_coordinatesType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.product_orientation_all_coordinatesType.{u, v}

def product_left_resolved_sheet_orientationType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.product_left_resolved_sheet_orientationType.{u}

def product_right_resolved_sheet_orientationType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.product_right_resolved_sheet_orientationType.{u}

def product_factor_face_germs_distinctType : Prop :=
  Specs.SmoothManifolds.Corners.FaceOrientations.product_factor_face_germs_distinctType.{u}

/-- All claims of the accepted FaceOrientations interface, with their full hypotheses. -/
def face_orientationsType : Prop :=
  orientation_extensionType.{u} ∧
  normal_half_lineType ∧
  outward_independentType ∧
  coordinate_face_signType ∧
  cone_face_orientationType ∧
  face_sign_gluingType ∧
  resolved_orientationType.{u} ∧
  resolved_orientation_uniqueType.{u} ∧
  normal_quotient_transportType ∧
  local_face_rayType ∧
  ordinary_orientationType.{u} ∧
  ordinary_orientation_equivType.{u} ∧
  product_orientationType.{u, v} ∧
  local_product_rayType.{u, v} ∧
  product_left_wedgeType ∧
  product_right_wedgeType ∧
  simplex_source_orientationType ∧
  box_source_orientationType ∧
  interval_source_orientationType ∧
  interval_resolved_endpointsType ∧
  product_orientation_coordinates_independentType.{u, v} ∧
  product_orientation_all_coordinatesType.{u, v} ∧
  product_left_resolved_sheet_orientationType.{u} ∧
  product_right_resolved_sheet_orientationType.{u} ∧
  product_factor_face_germs_distinctType.{u}

open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.CornerData _root_.SmoothManifolds.CornerProductData
  _root_.SmoothManifolds.CornerOrientationData _root_.SmoothManifolds.OrientationData Set
open scoped Classical

/-- The orientation, smooth projection and properness refer to one and the same
canonical resolved corner structure. Compact support is taken on the full face space. -/
def resolved_oriented_facesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : _root_.SmoothManifolds.CornerData.CornerManifold (n+1) M}
    (o : _root_.SmoothManifolds.CornerOrientationData.CornerOrientation S),
    ∃ (T : _root_.SmoothManifolds.CornerData.CornerManifold n
        (_root_.SmoothManifolds.CornerData.ResolvedFaceSpace S))
      (b : _root_.SmoothManifolds.CornerOrientationData.CornerOrientation T),
      _root_.SmoothManifolds.CornerOrientationData.IsResolvedOrientation o b ∧
      _root_.SmoothManifolds.CornerData.CornerMapContDiff (⊤ : ℕ∞) T S
        (_root_.SmoothManifolds.CornerData.faceProjection S) ∧
      IsProperMap (_root_.SmoothManifolds.CornerData.faceProjection S) ∧
      ∀ {F : M → Type v} [∀ p, Zero (F p)] (s : ∀ p, F p),
        IsCompact (_root_.SmoothManifolds.ModelData.sectionSupport s) →
        IsCompact (_root_.SmoothManifolds.ModelData.sectionSupport
          (fun q : _root_.SmoothManifolds.CornerData.ResolvedFaceSpace S =>
            s (_root_.SmoothManifolds.CornerData.faceProjection S q)))

/-- The original ordinary orientations induce the ordered corner product on the
actual Cartesian product, with smooth projections and inclusions. One orientation
works in every allowed ambient product coordinate family. -/
def ordinary_oriented_boundary_productType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M)
    (T : AtlasData.SmoothManifold m b N)
    (s : Orientation S) (t : Orientation T),
    ∃ (E : ModelOrthantCoordinates n a) (F : ModelOrthantCoordinates m b)
      (R : CornerManifold n M) (Q : CornerManifold m N)
      (C : ProductCoordinateFamily n m) (P : CornerManifold (n+m) (M × N))
      (hRsub : ordinaryCornerAtlas E S.smoothStructure.val ⊆ R.atlas)
      (hQsub : ordinaryCornerAtlas F T.smoothStructure.val ⊆ Q.atlas)
      (oR : CornerOrientation R) (oQ : CornerOrientation Q) (oP : CornerOrientation P),
      R.atlas = cornerMaximalExtension (ordinaryCornerAtlas E S.smoothStructure.val) ∧
      Q.atlas = cornerMaximalExtension (ordinaryCornerAtlas F T.smoothStructure.val) ∧
      P.atlas = cornerMaximalExtension (productAtlas C R.atlas Q.atlas) ∧
      IsOrdinaryOrientation S E R hRsub oR s ∧
      IsOrdinaryOrientation T F Q hQsub oQ t ∧
      IsCornerProductOrientation C oR oQ oP ∧
      (∀ D : ProductCoordinateFamily n m,
        productAtlas D R.atlas Q.atlas ⊆ P.atlas ∧
        IsCornerProductOrientation D oR oQ oP) ∧
      CornerMapContDiff (⊤ : ℕ∞) P R Prod.fst ∧
      CornerMapContDiff (⊤ : ℕ∞) P Q Prod.snd ∧
      (∀ q : N, CornerMapContDiff (⊤ : ℕ∞) R P (fun p => (p,q))) ∧
      (∀ p : M, CornerMapContDiff (⊤ : ℕ∞) Q P (fun q => (p,q))) ∧
      (∀ p : M, Nat.card (LocalFaceGerm R p) =
        if p ∈ BoundaryData.intrinsicBoundary S then 1 else 0) ∧
      (∀ q : N, Nat.card (LocalFaceGerm Q q) =
        if q ∈ BoundaryData.intrinsicBoundary T then 1 else 0)

/-- The full parent obligation: geometry, products, and outward-first face orientations. -/
def structure_and_facesType : Prop :=
  local_geometryType.{u, v} ∧ corner_productsType.{u, v} ∧ face_orientationsType.{u, v} ∧
    resolved_oriented_facesType.{u, v} ∧ ordinary_oriented_boundary_productType.{u}

end Specs.SmoothManifolds.Corners.StructureAndFaces
