import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricFoundation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthLaws

/-! Assembly of the smooth metric, intrinsic curve calculus and length laws.
All public definitions are aliases of the single shared objects. -/
set_option autoImplicit false
namespace P202.Geometry.MetricFoundation
universe u

abbrev Metric := @P202.MetricData.RiemannianMetric
abbrev metricPairing := @P202.MetricData.pairing
noncomputable abbrev metricNorm := @P202.MetricData.tangentNorm
abbrev Immersion := @P202.MetricData.SmoothImmersion
abbrev metricPullbackForm := @P202.MetricData.pullbackForm
abbrev MetricPreserving := @P202.MetricData.IsMetricPreserving
abbrev IsometricImmersion := @P202.MetricData.IsIsometricImmersion
abbrev LocalIsometry := @P202.MetricData.IsLocalIsometry

theorem exists_metric : P202Specs.Geometry.MetricFoundation.exists_metricType.{u} :=
  P202.Geometry.SmoothMetrics.exists_metric

theorem pullback_metric : P202Specs.Geometry.MetricFoundation.pullback_metricType.{u} :=
  P202.Geometry.SmoothMetrics.pullback_metric

theorem smoothImmersion_iff : P202Specs.Geometry.MetricFoundation.smoothImmersion_iffType.{u} :=
  P202.Geometry.SmoothMetrics.smoothImmersion_iff

theorem pullback_metric_original : P202Specs.Geometry.MetricFoundation.pullback_metric_originalType.{u} :=
  P202.Geometry.SmoothMetrics.pullback_metric_original

abbrev CoordinateC1On := @P202.CurveData.CoordinateC1On
abbrev Curve := @P202.CurveData.PiecewiseC1Curve
abbrev CompactCurve := @P202.CurveData.CompactPiecewiseC1Curve
noncomputable abbrev breakpoints := @P202.CurveData.breakpoints
abbrev compactCurve := @P202.CurveData.compactCurve
abbrev HasVelocityAt := @P202.CurveData.HasVelocityAt
noncomputable abbrev velocity := @P202.CurveData.velocity
noncomputable abbrev speed := @P202.CurveData.speed
noncomputable abbrev length := @P202.CurveData.length
noncomputable abbrev energy := @P202.CurveData.energy
abbrev IncreasingParameter := @P202.CurveData.PiecewiseRegularIncreasing
abbrev RegularRealC1On := @P202.CurveData.RegularRealC1On
noncomputable abbrev parameterToFun := @P202.CurveData.PiecewiseRegularIncreasing.toFun

theorem tangentNorm_nonneg : P202Specs.Geometry.MetricFoundation.tangentNorm_nonnegType.{u} :=
  @P202.Geometry.SmoothMetrics.tangentNorm_nonneg

theorem tangentNorm_zero : P202Specs.Geometry.MetricFoundation.tangentNorm_zeroType.{u} :=
  @P202.Geometry.SmoothMetrics.tangentNorm_zero

theorem tangentNorm_sq : P202Specs.Geometry.MetricFoundation.tangentNorm_sqType.{u} :=
  @P202.Geometry.SmoothMetrics.tangentNorm_sq

theorem tangentNorm_eq_zero_iff : P202Specs.Geometry.MetricFoundation.tangentNorm_eq_zero_iffType.{u} :=
  @P202.Geometry.SmoothMetrics.tangentNorm_eq_zero_iff

theorem tangentNorm_neg : P202Specs.Geometry.MetricFoundation.tangentNorm_negType.{u} :=
  @P202.Geometry.SmoothMetrics.tangentNorm_neg

theorem tangentNorm_smul : P202Specs.Geometry.MetricFoundation.tangentNorm_smulType.{u} :=
  @P202.Geometry.SmoothMetrics.tangentNorm_smul

theorem metricPreserving_norm : P202Specs.Geometry.MetricFoundation.metricPreserving_normType.{u} :=
  @P202.Geometry.SmoothMetrics.metricPreserving_norm

theorem localIsometry_isIsometricImmersion : P202Specs.Geometry.MetricFoundation.localIsometry_isIsometricImmersionType.{u} :=
  @P202.Geometry.SmoothMetrics.localIsometry_isIsometricImmersion

theorem hasVelocityAt_coordinates : P202Specs.Geometry.MetricFoundation.hasVelocityAt_coordinatesType.{u} :=
  @P202.Geometry.PiecewiseCurves.hasVelocityAt_coordinates

theorem hasVelocityAt_unique : P202Specs.Geometry.MetricFoundation.hasVelocityAt_uniqueType.{u} :=
  @P202.Geometry.PiecewiseCurves.hasVelocityAt_unique

theorem hasVelocityAt_off_breakpoints : P202Specs.Geometry.MetricFoundation.hasVelocityAt_off_breakpointsType.{u} :=
  @P202.Geometry.PiecewiseCurves.hasVelocityAt_off_breakpoints

theorem velocity_eq_coordinateExtension : P202Specs.Geometry.MetricFoundation.velocity_eq_coordinateExtensionType.{u} :=
  @P202.Geometry.PiecewiseCurves.velocity_eq_coordinateExtension

theorem coordinateExtension_independent : P202Specs.Geometry.MetricFoundation.coordinateExtension_independentType.{u} :=
  @P202.Geometry.PiecewiseCurves.coordinateExtension_independent

theorem speed_integrable : P202Specs.Geometry.MetricFoundation.speed_integrableType.{u} :=
  @P202.Geometry.PiecewiseCurves.speed_integrable

theorem squared_speed_integrable : P202Specs.Geometry.MetricFoundation.squared_speed_integrableType.{u} :=
  @P202.Geometry.PiecewiseCurves.squared_speed_integrable

theorem length_eq_of_eqOn : P202Specs.Geometry.MetricFoundation.length_eq_of_eqOnType.{u} :=
  @P202.Geometry.PiecewiseCurves.length_eq_of_eqOn

theorem energy_eq_of_eqOn : P202Specs.Geometry.MetricFoundation.energy_eq_of_eqOnType.{u} :=
  @P202.Geometry.PiecewiseCurves.energy_eq_of_eqOn

theorem integral_norm_eq_of_velocity_eqOn_off_finite : P202Specs.Geometry.MetricFoundation.integral_norm_eq_of_velocity_eqOn_off_finiteType.{u} :=
  @P202.Geometry.PiecewiseCurves.integral_norm_eq_of_velocity_eqOn_off_finite

theorem integral_sq_norm_eq_of_velocity_eqOn_off_finite : P202Specs.Geometry.MetricFoundation.integral_sq_norm_eq_of_velocity_eqOn_off_finiteType.{u} :=
  @P202.Geometry.PiecewiseCurves.integral_sq_norm_eq_of_velocity_eqOn_off_finite

theorem length_degenerate : P202Specs.Geometry.MetricFoundation.length_degenerateType.{u} :=
  @P202.Geometry.PiecewiseCurves.length_degenerate

theorem energy_degenerate : P202Specs.Geometry.MetricFoundation.energy_degenerateType.{u} :=
  @P202.Geometry.PiecewiseCurves.energy_degenerate

theorem stationary_exists : P202Specs.Geometry.MetricFoundation.stationary_existsType.{u} :=
  @P202.Geometry.PiecewiseCurves.stationary_exists

theorem compact_representation : P202Specs.Geometry.MetricFoundation.compact_representationType.{u} :=
  @P202.Geometry.PiecewiseCurves.compact_representation

theorem restriction_exists : P202Specs.Geometry.MetricFoundation.restriction_existsType.{u} :=
  @P202.Geometry.PiecewiseCurves.restriction_exists

theorem postcomposition_exists : P202Specs.Geometry.MetricFoundation.postcomposition_existsType.{u} :=
  @P202.Geometry.PiecewiseCurves.postcomposition_exists

theorem concatenation_exists : P202Specs.Geometry.MetricFoundation.concatenation_existsType.{u} :=
  @P202.Geometry.PiecewiseCurves.concatenation_exists

theorem reversal_exists : P202Specs.Geometry.MetricFoundation.reversal_existsType.{u} :=
  @P202.Geometry.PiecewiseCurves.reversal_exists

theorem reparametrization_exists : P202Specs.Geometry.MetricFoundation.reparametrization_existsType.{u} :=
  @P202.Geometry.PiecewiseCurves.reparametrization_exists

theorem isometricImmersion_length : P202Specs.Geometry.MetricFoundation.isometricImmersion_lengthType.{u} :=
  @P202.Geometry.LengthLaws.isometricImmersion_length

theorem localIsometry_length : P202Specs.Geometry.MetricFoundation.localIsometry_lengthType.{u} :=
  @P202.Geometry.LengthLaws.localIsometry_length

theorem localIsometry_length_exists : P202Specs.Geometry.MetricFoundation.localIsometry_length_existsType.{u} :=
  @P202.Geometry.LengthLaws.localIsometry_length_exists

theorem subdivision_length : P202Specs.Geometry.MetricFoundation.subdivision_lengthType.{u} :=
  @P202.Geometry.LengthLaws.subdivision_length

theorem subdivision_length_exists : P202Specs.Geometry.MetricFoundation.subdivision_length_existsType.{u} :=
  @P202.Geometry.LengthLaws.subdivision_length_exists

theorem finiteConcatenation_length : P202Specs.Geometry.MetricFoundation.finiteConcatenation_lengthType.{u} :=
  @P202.Geometry.LengthLaws.finiteConcatenation_length

theorem concatenation_length : P202Specs.Geometry.MetricFoundation.concatenation_lengthType.{u} :=
  @P202.Geometry.LengthLaws.concatenation_length

theorem reversal_length : P202Specs.Geometry.MetricFoundation.reversal_lengthType.{u} :=
  @P202.Geometry.LengthLaws.reversal_length

theorem reversal_length_exists : P202Specs.Geometry.MetricFoundation.reversal_length_existsType.{u} :=
  @P202.Geometry.LengthLaws.reversal_length_exists

theorem reparametrization_length : P202Specs.Geometry.MetricFoundation.reparametrization_lengthType.{u} :=
  @P202.Geometry.LengthLaws.reparametrization_length

theorem reparametrization_length_exists : P202Specs.Geometry.MetricFoundation.reparametrization_length_existsType.{u} :=
  @P202.Geometry.LengthLaws.reparametrization_length_exists

theorem length_formula : P202Specs.Geometry.MetricFoundation.length_formulaType.{u} := by
  unfold P202Specs.Geometry.MetricFoundation.length_formulaType
  intros
  rfl

theorem energy_formula : P202Specs.Geometry.MetricFoundation.energy_formulaType.{u} := by
  unfold P202Specs.Geometry.MetricFoundation.energy_formulaType
  intros
  rfl

end P202.Geometry.MetricFoundation
