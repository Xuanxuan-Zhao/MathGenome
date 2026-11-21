import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedCalculus
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.EmbeddedAtlas
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.EmbeddedBoundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.EmbeddedDerivative

/-! Assembly of the accepted atlas, geometric boundary, and C¹ calculus
comparisons. All shared definitions and component proofs are reused from their
own modules. The distinct namespace avoids redeclaring the original local
comparison lemmas already exported by the atlas prerequisite. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace SmoothManifolds.EmbeddedCompatibilityResults
universe u v

theorem tangent_identification :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.tangent_identificationType :=
  EmbeddedCalculusResults.tangent_identification

theorem form_evaluation :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.form_evaluationType.{u,v} :=
  EmbeddedCalculusResults.form_evaluation

theorem form_bijective :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.form_bijectiveType.{u,v} :=
  EmbeddedCalculusResults.form_bijective

theorem restriction_transport :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.restriction_transportType.{u,v} :=
  EmbeddedCalculusResults.restriction_transport

theorem coefficient_evaluation :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.coefficient_evaluationType.{u} :=
  EmbeddedCalculusResults.coefficient_evaluation

theorem support_identification :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.support_identificationType :=
  EmbeddedCalculusResults.support_identification

theorem chart_pullback :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.chart_pullbackType :=
  EmbeddedCalculusResults.chart_pullback

theorem induced_structure_exists :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.induced_structure_existsType :=
  EmbeddedAtlasResults.induced_structure_exists

theorem induced_euclidean_structure_exists :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.induced_euclidean_structure_existsType :=
  EmbeddedAtlasResults.induced_euclidean_structure_exists

theorem induced_tangent_identification :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.induced_tangent_identificationType :=
  EmbeddedAtlasResults.induced_tangent_identification

theorem matching_chart_pullback :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.matching_chart_pullbackType :=
  EmbeddedAtlasResults.matching_chart_pullback

theorem transportField_bijective :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.transportField_bijectiveType :=
  EmbeddedAtlasResults.transportField_bijective

theorem boundary_set :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.boundary_setType :=
  EmbeddedBoundaryResults.boundary_set

theorem boundary_base :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.boundary_baseType :=
  EmbeddedBoundaryResults.boundary_base

theorem boundary_zero :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.boundary_zeroType :=
  EmbeddedBoundaryResults.boundary_zero

theorem boundary_geometry :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.boundary_geometryType :=
  EmbeddedBoundaryResults.boundary_geometry

theorem boundary_tangent_hyperplane :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.boundary_tangent_hyperplaneType :=
  EmbeddedBoundaryResults.boundary_tangent_hyperplane

theorem boundary_outward_rays :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.boundary_outward_raysType :=
  EmbeddedBoundaryResults.boundary_outward_rays

theorem boundary_restriction :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.boundary_restrictionType :=
  EmbeddedBoundaryResults.boundary_restriction

theorem orientation_transport :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.orientation_transportType :=
  EmbeddedBoundaryResults.orientation_transport

theorem zero_orientation_transport :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.zero_orientation_transportType :=
  EmbeddedBoundaryResults.zero_orientation_transport

theorem boundary_orientation :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.boundary_orientationType :=
  EmbeddedBoundaryResults.boundary_orientation

theorem boundary_point_comparison :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.boundary_point_comparisonType :=
  EmbeddedBoundaryResults.boundary_point_comparison

theorem interval_comparison :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.interval_comparisonType :=
  EmbeddedBoundaryResults.interval_comparison

theorem interval_positive :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.interval_positiveType :=
  EmbeddedBoundaryResults.interval_positive

theorem regularity_transport :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.regularity_transportType :=
  EmbeddedDerivativeResults.regularity_transport

theorem continuous_transport :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.continuous_transportType :=
  EmbeddedDerivativeResults.continuous_transport

theorem hasDerivative_transport :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.hasDerivative_transportType :=
  EmbeddedDerivativeResults.hasDerivative_transport

theorem intrinsicExteriorDerivative_transport :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.intrinsicExteriorDerivative_transportType :=
  EmbeddedDerivativeResults.intrinsicExteriorDerivative_transport

open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.ExteriorDerivativeData
  _root_.SmoothManifolds.EmbeddedCalculusData _root_.SmoothManifolds.EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model

/-- The component conclusions hold for the same uniquely determined family. -/
theorem common_domain :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.common_domainType := by
  intro n N a M hM S hS
  obtain ⟨I, hI, huniq⟩ := induced_tangent_identification hM S hS
  refine ⟨I, ⟨hI, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact transportField_bijective S I
  · exact support_identification S I
  · exact regularity_transport hM S hS I hI
  · exact continuous_transport hM S hS I hI
  · exact hasDerivative_transport hM S hS I hI
  · exact intrinsicExteriorDerivative_transport hM S hS I hI
  · intro J hJ
    exact huniq J hJ.1

/-- Raw local extension assumptions are discharged by the induced atlas. -/
theorem every_chart_pullback :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.every_chart_pullbackType := by
  intro n N a M S hS I hI C e he
  have hraw : IsRawEmbeddedChart e := by
    have he' := he
    rw [hS] at he'
    exact he'
  obtain ⟨c, hm, hcover⟩ := EmbeddedDerivativeResults.embeddedChart_of_raw e hraw
  refine ⟨c, hm, ?_⟩
  intro u hu p
  exact ⟨hcover u hu, matching_chart_pullback S hS I hI C e he c hm u hu (hcover u hu)⟩

/-- The smooth derivative is constructed, then its coordinate characterization
and C¹ uniqueness identify it with the D04 selector. -/
theorem smooth_operator_comparison :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.smooth_operator_comparisonType := by
  intro n N a M hM S hS I hI C B
  obtain ⟨D, hD, huniq⟩ := ExteriorDerivativeResults.smooth_family_exists C B
  refine ⟨D, hD, huniq, ?_⟩
  intro k ξ hξ
  have hr := ExteriorDerivativeResults.smooth_regular C k (B k) ξ 1 hξ
  have hd := ExteriorDerivativeResults.global_coordinates C B D hD k ξ hξ
  obtain ⟨η, hη, _⟩ := intrinsicExteriorDerivative_transport hM S hS I hI C k ξ hr
  have heq := ExteriorDerivativeResults.derivative_unique C k ξ (D k ξ) η hd hη.2.1
  rw [heq]
  exact hη.2.2

theorem degree_zero_transport :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.degree_zero_transportType.{u,v} := by
  intro V W _ _ _ _ I r w
  let z : Fin 0 → Module.Dual ℝ V := fun j => Fin.elim0 j
  have hr : (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)).symm r =
      r • exteriorPower.ιMulti ℝ 0 z := by
    apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)).injective
    simp
  rw [hr]
  change evaluate V 0 (r • exteriorPower.ιMulti ℝ 0 z) (fun j => I.symm (w j)) = r
  rw [map_smul, smul_apply,
    ExteriorAlgebraResults.determinant_normalization]
  simp

theorem zero_dimension_comparison :
    Specs.SmoothManifolds.Integration.EmbeddedCalculus.zero_dimension_comparisonType := by
  intro N a M hM S hS I hI C
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  refine ⟨?_, ?_, ?_⟩
  · intro p
    have hz := D04.tangentSpace_zero hM₂ p.val p.property
    refine ⟨hz, ?_⟩
    intro v
    apply (I p).injective
    rw [map_zero]
    apply Subtype.ext
    exact (Submodule.eq_bot_iff _).mp hz _ (I p v).property
  · intro k ξ
    have hr := EmbeddedDerivativeResults.zero_dimension_regular C 1 k ξ
    have hd := ExteriorDerivativeResults.zero_dim_derivative C k ξ
    obtain ⟨η, hη, _⟩ := intrinsicExteriorDerivative_transport hM S hS I hI C k ξ hr
    have hz := ExteriorDerivativeResults.derivative_unique C k ξ η 0 hη.2.1 hd
    refine ⟨hr, hd, ?_⟩
    rw [hz] at hη
    rw [← hη.2.2]
    funext p
    simp [transportField, transportCovector]
  · intro k hk ξ
    funext p
    exact ExteriorAlgebraResults.fields_above_dimension C k hk ξ p

end SmoothManifolds.EmbeddedCompatibilityResults
