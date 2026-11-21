import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolarVolumeIntegration
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CutLocusNull
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConstantCurvaturePolar
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.HyperboloidModel
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PolarVolumeDensity
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ModelPolarDomains
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Order.AtTopBotIxx

/-! Polar integration for actual Riemannian metric balls, including the
Euclidean, spherical and hyperbolic model formulas. The polar density and
model-domain identities are supplied by the proved upstream results. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped ENNReal Topology

namespace P202.Geometry.PolarVolumeIntegration
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CompletenessData P202.CurvatureData
  P202.ExponentialData P202.ExponentialJacobiData P202.CompleteExponentialData P202.CutTimeData
  P202.CutPolarData P202.PolarVolumeData P202.PolarIntegrationData
open Set Filter MeasureTheory
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The canonical measure's defining compact-density representation. -/
theorem volume_properties (g : RiemannianMetric S) :
    letI : MeasurableSpace M := borel M
    (P202.CutNullData.volume g).Regular ∧
      (∀ K : Set M, IsCompact K → P202.CutNullData.volume g K < ⊤) ∧
      ∀ f : CompactlySupportedContinuousMap M ℝ,
        (∫ x, f x ∂P202.CutNullData.volume g) = P202.VolumeData.integral g f :=
  (RiemannianVolume.measure_representation_exists g).choose_spec.1

/-- Positive-dimensional Riemannian volume has no atoms, without completeness. -/
theorem volume_singleton (g : RiemannianMetric S) (hn : 0 < n) (p : M) :
    P202.CutNullData.volume g {p} = 0 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply CutLocusNull.coordinate_null g
  intro c hc
  have hsource : ({p} ∩ c.source).Subsingleton := by
    intro x hx y hy
    exact (mem_singleton_iff.mp hx.1).trans (mem_singleton_iff.mp hy.1).symm
  have hsub := hsource.image (fun q => (c q).val)
  exact hsub.measure_zero volume

/-- The polar parametrization is continuous on the full product on a complete
manifold. Its density has support only in the open polar domain. -/
theorem polarMap_continuous [ConnectedSpace M] (g : RiemannianMetric S)
    (hcomplete : LengthMetricComplete g) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) : Continuous (polarMap g F p) := by
  let E := selectedCoordinates S p
  have hfull : FullExponentialAt F p := HopfRinow.full_exponential_of_geodesicallyComplete C
    ((HopfRinow.hopf_rinow S g C hC).1.mp hcomplete) F hF p
  have hc : Continuous (fun v : UnitDirection g p => E v.val) := continuous_induced_dom
  have hv : Continuous (fun tv : ℝ × UnitDirection g p => tv.1 • E tv.2.val) :=
    continuous_fst.smul (hc.comp continuous_snd)
  convert (CompleteExponentialMinimizers.exponential_coordinates_continuous
    C F hF p hfull E).comp hv using 1
  funext tv
  simp [polarMap, E]

/-- Metric balls use the original topology, not an auxiliary ambient distance. -/
theorem metricBall_open [ConnectedSpace M] (g : RiemannianMetric S)
    (p : M) (r : ℝ) : IsOpen (metricBall g p r) :=
  isOpen_lt ((CompleteExponentialMinimizers.lengthDistance_continuous g).comp
    (continuous_const.prodMk continuous_id)) continuous_const

/-- The omitted locus is null for the genuine volume. -/
theorem volume_regularDomain [ConnectedSpace M] (g : RiemannianMetric S)
    (hn : 0 < n) (hcomplete : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M) :
    letI : MeasurableSpace M := borel M
    (P202.CutNullData.volume g).restrict (regularDomain g F p) =
      P202.CutNullData.volume g := by
  letI : MeasurableSpace M := borel M
  apply Measure.restrict_eq_self_of_ae_mem
  apply (ae_iff).mpr
  have heq : {a : M | a ∉ regularDomain g F p} = {p} ∪ cutLocus g F p := by
    ext a
    simp only [mem_ofPred_eq, regularDomain, mem_compl_iff, not_not]
  rw [heq]
  exact measure_union_null (volume_singleton g hn p)
    (CutLocusNull.cut_locus_null S g hn hcomplete C hC F hF p)

/-- On the support of j_* the radial coordinate is the intrinsic distance. -/
theorem polar_distance [ConnectedSpace M] (g : RiemannianMetric S)
    (hn : 0 < n) (hcomplete : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (tv : ℝ × UnitDirection g p) (htv : tv ∈ polarDomain g F p) :
    lengthDistance g p (polarMap g F p tv) = tv.1 := by
  have h := CutPolarDomain.distance_exponential_eq_norm g hn hcomplete C hC F hF p
    (tv.1 • tv.2.val) ⟨tv, htv, rfl⟩
  simpa only [polarMap, SmoothMetrics.tangentNorm_smul, abs_of_pos htv.1,
    tv.2.property, mul_one] using h

/-- Compactness of closed metric balls supplies finite volume. -/
theorem ball_volume_finite :
    P202Specs.Geometry.PolarVolumeIntegration.ball_volume_finiteType.{u} := by
  intro n M _ _ S g hcomplete p r
  obtain ⟨C, F, hC, hF, hfull⟩ := CutTime.complete_exponential_exists S g hcomplete
  have hcompact := (CompleteExponentialMinimizers.complete_exponential_minimizers
    S g C hC F hF p (hfull p)).2.1 (max r 0) (le_max_right _ _)
  apply lt_of_le_of_lt (measure_mono (t := {q | lengthDistance g p q ≤ max r 0}) ?_)
    ((volume_properties g).2.1 _ hcompact.2)
  exact fun q hq => (show lengthDistance g p q < r from hq).le.trans (le_max_left _ _)

/-- The endpoint value follows by continuity of a measure from below. -/
theorem ball_volume_left_limit :
    P202Specs.Geometry.PolarVolumeIntegration.ball_volume_left_limitType.{u} := by
  intro n M _ _ S g p r hr
  letI : MeasurableSpace M := borel M
  have hmono : Monotone (fun a : Iio r => metricBall g p a.val) := by
    intro a b hab q hq
    exact (show lengthDistance g p q < a.val from hq).trans_le hab
  have hunion : (⋃ a : Iio r, metricBall g p a.val) = metricBall g p r := by
    ext q
    constructor
    · intro hq
      obtain ⟨a, ha⟩ := mem_iUnion.mp hq
      exact (show lengthDistance g p q < a.val from ha).trans a.property
    · intro hq
      obtain ⟨a, ha, har⟩ := exists_between (show lengthDistance g p q < r from hq)
      exact mem_iUnion.mpr ⟨⟨a, har⟩, ha⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := P202.CutNullData.volume g) hmono
  rw [hunion] at hlim
  exact (tendsto_comp_coe_Iio_atTop (a := r)).mp hlim

theorem fiberVolume_orthonormal (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hE : IsOrthonormalCoordinates g p E) : fiberVolume g p E = 1 := by
  classical
  unfold fiberVolume SmoothManifolds.DensityIntegrationData.tupleEvaluation
    P202.VolumeData.density
  rw [SmoothManifolds.MetricVolumeResults.metricDensity_apply]
  unfold SmoothManifolds.MetricVolumeData.determinantNorm
    SmoothManifolds.MetricVolumeData.determinantMetric
  simp only [LinearMap.BilinForm.exteriorPower, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  have hmatrix : (Matrix.of fun i j =>
      SmoothManifolds.MetricVolumeData.metricForm (P202.VolumeData.libraryMetric g) p
        (fiberBasis p E j) (fiberBasis p E i)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.of_apply, fiberBasis, Module.Basis.coe_map, Function.comp_apply, Pi.basisFun_apply]
    change pairing g p (E.symm (Pi.single j 1)) (E.symm (Pi.single i 1)) = _
    rw [hE]
    simp only [Matrix.one_apply, eq_comm]
  simp only [Function.comp_apply]
  rw [hmatrix, Matrix.det_one, Real.sqrt_one]

theorem unitCone_univ (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    unitCone g p E univ = {x | tangentNorm g p (E.symm x) < 1} \ {0} := by
  ext x
  constructor
  · rintro ⟨r, hr, v, _, rfl⟩
    have hnorm : tangentNorm g p (E.symm (r • E v.val)) = r := by
      simp only [map_smul, E.symm_apply_apply, SmoothMetrics.tangentNorm_smul,
        abs_of_pos hr.1, v.property, mul_one]
    refine ⟨by simpa only [mem_ofPred_eq, hnorm] using hr.2, ?_⟩
    intro hz
    have hzero : r • E v.val = 0 := mem_singleton_iff.mp hz
    rw [hzero, map_zero, SmoothMetrics.tangentNorm_zero] at hnorm
    linarith [hr.1]
  · rintro ⟨hx, hx0⟩
    have hxne : x ≠ 0 := hx0
    have hvne : E.symm x ≠ 0 := fun h => hxne (by simpa using congrArg E h)
    have hpos : 0 < tangentNorm g p (E.symm x) :=
      lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g p _)
        (fun h => hvne ((SmoothMetrics.tangentNorm_eq_zero_iff g p _).mp h.symm))
    let v : UnitDirection g p :=
      ⟨(tangentNorm g p (E.symm x))⁻¹ • E.symm x, by
        rw [SmoothMetrics.tangentNorm_smul, abs_of_pos (inv_pos.mpr hpos),
          inv_mul_cancel₀ hpos.ne']⟩
    refine ⟨tangentNorm g p (E.symm x), ⟨hpos, hx⟩, v, mem_univ _, ?_⟩
    simp only [v, map_smul, E.apply_symm_apply, smul_smul,
      mul_inv_cancel₀ hpos.ne', one_smul]

theorem sphereMeasure_univ
    (hsphere : P202Specs.Geometry.PolarVolumeDensity.sphere_measureType.{u})
    (g : RiemannianMetric S) (hn : 2 ≤ n) (p : M) :
    sphereMeasure g p univ = omega n := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨E, hE⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist g p
  rw [(hsphere S g hn p).2.2 E univ MeasurableSet.univ,
    fiberVolume_orthonormal g p E hE, mul_one, unitCone_univ,
    measure_sdiff_null (measure_singleton (0 : Euclidean n))]
  unfold omega
  rw [Measure.toSphere_apply_univ]
  have hvol : volume {x : Euclidean n | tangentNorm g p (E.symm x) < 1} =
      volume (Metric.ball (0 : P202.SpaceFormData.E n) 1) := by
    rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage (measurableSet_ball.nullMeasurableSet)]
    congr 1
    ext x
    simp only [ExponentialNormalCoordinates.orthonormal_norm_formula g p E hE,
      mem_ofPred_eq, mem_preimage, Metric.mem_ball, dist_zero_right,
      EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  rw [hvol]
  simp

/-- A radial segment minimizing to r puts every smaller positive radius in
the open polar domain, including when r is a finite model endpoint. -/
theorem mem_polar_of_minimizing_radius (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (v : UnitDirection g p)
    (r t : ℝ) (ht : 0 < t) (htr : t < r)
    (hd : lengthDistance g p (fiberExponential F p (r • v.val)) = r) :
    (t,v) ∈ polarDomain g F p := by
  have hr : 0 < r := ht.trans htr
  exact ⟨ht, lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hr).mpr htr)
    (le_sSup ⟨r, ⟨hr.le, hd⟩, rfl⟩)⟩

open P202.JacobiMatrixData P202.ConstantCurvaturePolarData

/-- Constant sectional curvature makes every normal system the scalar model
operator in its parallel frame. -/
theorem model_jacobi_operator (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (k : ℝ) (hk : ConstantSectional g R k)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (hunit : ∀ t ∈ I.carrier, pairing g (q t).1 (q t).2 (q t).2 = 1)
    (D : JacobiSystem S C R I q (n-1)) (hD : IsOrthonormalNormalFrame g D)
    (t : ℝ) (ht : t ∈ I.carrier) : D.A t = s k t • (1 : Operator (n-1)) := by
  have hcurv (t : ℝ) (ht : t ∈ I.carrier) : D.curvature t = k • (1 : Operator (n-1)) := by
    apply ContinuousLinearMap.ext
    intro x
    apply D.frame_injective t ht
    rw [D.curvature_eq t ht]
    have hnormal : pairing g (q t).1 (D.frame t x) (q t).2 = 0 :=
      (hD.2 t ht _).mp ⟨x, rfl⟩
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul] using
      ConstantCurvaturePolar.radial_curvature g C hC R hR k hk _ _ _ (hunit t ht) hnormal
  let L : ℝ → Operator (n-1) →L[ℝ] Operator (n-1) :=
    fun t => ContinuousLinearMap.mul ℝ (Operator (n-1)) (D.curvature t)
  have hL : ContinuousOn L I.carrier :=
    (ContinuousLinearMap.mul ℝ (Operator (n-1))).continuous.comp_continuousOn
      D.curvature_continuous
  obtain ⟨A, B, hA, hB, hd, hu⟩ := JacobiIVP.second_order_linear_ivp I L hL 0 h0 0 1
  have hDAB : D.A t = A t := (hu D.A D.B D.initial_A D.initial_B (by
    simpa only [L, ContinuousLinearMap.mul_apply'] using D.derivatives) t ht).1
  have hmodel : s k t • (1 : Operator (n-1)) = A t := by
    apply (hu (fun t => s k t • (1 : Operator (n-1)))
      (fun t => c k t • (1 : Operator (n-1))) (by simp [ConstantCurvaturePolar.s_zero])
      (by simp [ConstantCurvaturePolar.c_zero]) ?_ t ht).1
    intro a ha
    constructor
    · simpa using! (ConstantCurvaturePolar.s_derivative k a).smul_const (1 : Operator (n-1))
    · convert (ConstantCurvaturePolar.c_derivative k a).smul_const
        (1 : Operator (n-1)) using 1
      simp only [L, ContinuousLinearMap.mul_apply', hcurv a ha,
        smul_mul_smul_comm, one_mul, neg_smul, neg_mul]
  exact hDAB.trans hmodel.symm

/-- The model density is obtained from the actual normal Jacobi systems. -/
theorem constant_curvature_density
    (hframes : P202Specs.Geometry.PolarVolumeDensity.normal_frame_existsType.{u})
    (hjacobi : P202Specs.Geometry.PolarVolumeDensity.jacobi_densityType.{u})
    [ConnectedSpace M] (g : RiemannianMetric S) (hn : 2 ≤ n)
    (hcomplete : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (k : ℝ) (hk : ConstantSectional g R k)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : UnitDirection g p) (t : ℝ)
    (htv : (t,v) ∈ polarDomain g F p) :
    radialDensity g F p (t,v) = s k t ^ (n-1) ∧ 0 < s k t ^ (n-1) := by
  obtain ⟨D, hD⟩ := hframes S g hn hcomplete C hC R hR F hF p v
  have h0 := (hF ⟨p, v.val⟩).1
  have hq := (hF ⟨p, v.val⟩).2.2.1
  have hfull : FullExponentialAt F p := HopfRinow.full_exponential_of_geodesicallyComplete C
    ((HopfRinow.hopf_rinow S g C hC).1.mp hcomplete) F hF p
  have htime : t ∈ (F.interval ⟨p, v.val⟩).carrier := by
    rw [CompleteExponentialMinimizers.full_interval C F hF p hfull v.val]
    trivial
  have hunit (a : ℝ) (ha : a ∈ (F.interval ⟨p, v.val⟩).carrier) :
      pairing g (F.curve ⟨p,v.val⟩ a).1 (F.curve ⟨p,v.val⟩ a).2
        (F.curve ⟨p,v.val⟩ a).2 = 1 := by
    rw [← SmoothMetrics.tangentNorm_sq]
    have hs := GeodesicIVP.constant_speed S g C hC _ _ hq a ha 0 h0
    rw [hs, (hF ⟨p,v.val⟩).2.1, v.property, one_pow]
  have hA := model_jacobi_operator g C hC R hR k hk _ _ hq h0 hunit D hD t htime
  have hdet : LinearMap.det (D.A t).toLinearMap = s k t ^ (n-1) := by
    rw [hA]
    change LinearMap.det (s k t • (1 : Euclidean (n-1) →ₗ[ℝ] Euclidean (n-1))) = _
    rw [LinearMap.det_smul, map_one, mul_one]
    simp
  have hj := hjacobi S g hn hcomplete C hC R hR F hF p v D hD t htv.1 htv.2
  exact ⟨hj.1.trans hdet, hdet ▸ hj.1 ▸ hj.2⟩

/-- Once the prescribed model radius minimizes in every direction, the
constant-curvature metric gives its actual ball volume. This lemma has no
Ricci hypothesis and permits a finite endpoint r. -/
theorem constant_curvature_ball
    (hball : P202Specs.Geometry.PolarVolumeIntegration.ball_integralType.{u})
    (hframes : P202Specs.Geometry.PolarVolumeDensity.normal_frame_existsType.{u})
    (hjacobi : P202Specs.Geometry.PolarVolumeDensity.jacobi_densityType.{u})
    (hsphere : P202Specs.Geometry.PolarVolumeDensity.sphere_measureType.{u})
    [ConnectedSpace M] (g : RiemannianMetric S) (hn : 2 ≤ n)
    (hcomplete : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (k : ℝ) (hk : ConstantSectional g R k)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (r : ℝ) (hr : 0 < r)
    (hmin : ∀ v : UnitDirection g p,
      lengthDistance g p (fiberExponential F p (r • v.val)) = r) :
    modelVolume g p r = omega n *
      ENNReal.ofReal (∫ t in (0 : ℝ)..r, s k t ^ (n-1)) := by
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) r) (v : UnitDirection g p) :
      truncatedDensity g F p (t,v) = s k t ^ (n-1) ∧ 0 < s k t ^ (n-1) := by
    have hp := mem_polar_of_minimizing_radius g F p v r t ht.1 ht.2 (hmin v)
    have h := constant_curvature_density hframes hjacobi g hn hcomplete C hC R hR
      k hk F hF p v t hp
    refine ⟨?_, h.2⟩
    change (polarDomain g F p).indicator (radialDensity g F p) (t,v) = _
    rw [indicator_of_mem hp, h.1]
  obtain ⟨v, _⟩ := nonempty_of_measure_ne_zero (hsphere S g hn p).2.1
  have hcont : Continuous (fun t => s k t ^ (n-1)) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (ConstantCurvaturePolar.s_derivative k t).continuousAt).pow _
  have hint : IntegrableOn (fun t => s k t ^ (n-1)) (Ioo (0 : ℝ) r) :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)] (fun t => s k t ^ (n-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hd t ht v).2.le
  have hscalar : ENNReal.ofReal (∫ t in (0 : ℝ)..r, s k t ^ (n-1)) =
      ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (s k t ^ (n-1)) := by
    rw [intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo]
    exact ofReal_integral_eq_lintegral_ofReal hint hnonneg
  change ballVolume g p r = _
  rw [hball S g hn hcomplete C hC R hR F hF p r hr, hscalar,
    ← lintegral_const_mul _ hcont.measurable.ennreal_ofReal]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  simp_rw [(hd t ht _).1]
  simp only [lintegral_const, sphereMeasure_univ hsphere g hn p]
  exact mul_comm _ _


open P202.SpaceFormData P202.ModelPolarData

/-- Specialization to actual Euclidean realizations; the volume remains the
measure of an intrinsic metric ball. -/
theorem euclidean_volume_of_density
    (hball : P202Specs.Geometry.PolarVolumeIntegration.ball_integralType.{0})
    (hframes : P202Specs.Geometry.PolarVolumeDensity.normal_frame_existsType.{0})
    (hjacobi : P202Specs.Geometry.PolarVolumeDensity.jacobi_densityType.{0})
    (hsphere : P202Specs.Geometry.PolarVolumeDensity.sphere_measureType.{0})
    (hmodel : P202Specs.Geometry.ModelPolarDomains.euclideanType) :
    P202Specs.Geometry.PolarVolumeIntegration.euclidean_volumeType := by
  intro n hn G hG p r hr
  letI : ConnectedSpace (E n) := hG.1
  obtain ⟨R, hR, hk⟩ := hG.2.2.2.1
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists G.manifold G.connection
  obtain ⟨E, c, hE, hc, hsource, htarget, hp, hvectors, hpolar, hradii⟩ :=
    (hmodel n hn G hG).1 F hF p
  apply constant_curvature_ball hball hframes hjacobi hsphere G.metric hn hG.2.2.1
    G.connection G.leviCivita R hR 0 hk F hF p r hr
  intro v
  simpa only [SmoothMetrics.tangentNorm_smul, abs_of_pos hr, v.property, mul_one]
    using (hvectors (r • v.val)).2.2

/-- The spherical normal-domain theorem supplies the minimizing boundary
radius as well, so this proof includes r = πa directly. -/
theorem spherical_volume_of_density
    (hball : P202Specs.Geometry.PolarVolumeIntegration.ball_integralType.{0})
    (hframes : P202Specs.Geometry.PolarVolumeDensity.normal_frame_existsType.{0})
    (hjacobi : P202Specs.Geometry.PolarVolumeDensity.jacobi_densityType.{0})
    (hsphere : P202Specs.Geometry.PolarVolumeDensity.sphere_measureType.{0})
    (hmodel : P202Specs.Geometry.ModelPolarDomains.sphericalType) :
    P202Specs.Geometry.PolarVolumeIntegration.spherical_volumeType := by
  intro n hn a ha A B hB p r hr hra
  letI : ConnectedSpace (Sphere n a) := hB.1
  obtain ⟨R, hR, hk⟩ := hB.2.2.2.1
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists B.manifold B.connection
  obtain ⟨E, c, hE, hnormal, hsource, hformula, hdist, hantipode,
      hcos, hdistanti, hpolar, hradii⟩ := (hmodel n hn a ha A B hB).1 F hF p
  apply constant_curvature_ball hball hframes hjacobi hsphere B.metric hn hB.2.2.1
    B.connection B.leviCivita R hR ((a^2)⁻¹) hk F hF p r hr
  intro v
  have hnorm : tangentNorm B.metric p (r • v.val) = r := by
    rw [SmoothMetrics.tangentNorm_smul, abs_of_pos hr, v.property, mul_one]
  have hbnd : tangentNorm B.metric p (r • v.val) ≤ Real.pi * a := by
    rw [hnorm]
    exact hra
  simpa only [hnorm] using hdist (r • v.val) hbnd

/-- Every positive curvature is represented by the original radius-a sphere,
and its normal radius is precisely the manuscript's rho_k. -/
theorem positive_curvature_radius (k : ℝ) (hk : 0 < k) :
    let a := (Real.sqrt k)⁻¹
    0 < a ∧ (a ^ 2)⁻¹ = k ∧ Real.pi * a = Real.pi / Real.sqrt k := by
  dsimp
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  refine ⟨inv_pos.mpr hs, ?_, by rw [div_eq_mul_inv]⟩
  rw [inv_pow, inv_inv, Real.sq_sqrt hk.le]

/-- The same parameter bridge covers every negative curvature. -/
theorem negative_curvature_radius (k : ℝ) (hk : k < 0) :
    let a := (Real.sqrt (-k))⁻¹
    0 < a ∧ -(a ^ 2)⁻¹ = k := by
  dsimp
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr (neg_pos.mpr hk)), ?_⟩
  rw [inv_pow, inv_inv, Real.sq_sqrt (neg_nonneg.mpr hk.le), neg_neg]


/-- The accepted Lorentz curvature calculation is on smooth fields; extension
of tangent vectors gives the exact intrinsic sectional-curvature interface. -/
theorem hyperbolic_constant_sectional {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (P202.HyperboloidData.Hyperboloid n a))
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hproj : HasProjectionChart S) (hg : P202.HyperboloidData.IsInduced g)
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R) :
    ConstantSectional g R (-(a^2)⁻¹) := by
  obtain ⟨c, hc, hsource, htarget, hprojection⟩ := hproj
  intro p x y hi
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p x
  obtain ⟨Y, hY⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p y
  have hden := ne_of_gt (SectionalRecovery.gram_pos (pairing g p)
    (g.symmetric p) (g.positive p) x y hi)
  have hf := HyperboloidModel.constant_sectional_curvature ha S c hc hsource hprojection
    g hg C hC X Y p (by simpa only [hX, hY] using hden)
  have ht : R.val p x y y = (P202.HyperboloidData.curvatureField C X Y Y).val p := by
    simpa only [hX, hY, P202.CurvatureData.curvature,
      P202.HyperboloidData.curvatureField] using! hR X Y Y p
  change pairing g p (R.val p x y y) x / _ = _
  rw [ht]
  simpa only [hX, hY] using hf

/-- Actual complete hyperboloid balls at every positive radius. -/
theorem hyperbolic_volume_of_density
    (hball : P202Specs.Geometry.PolarVolumeIntegration.ball_integralType.{0})
    (hframes : P202Specs.Geometry.PolarVolumeDensity.normal_frame_existsType.{0})
    (hjacobi : P202Specs.Geometry.PolarVolumeDensity.jacobi_densityType.{0})
    (hsphere : P202Specs.Geometry.PolarVolumeDensity.sphere_measureType.{0})
    (hmodel : P202Specs.Geometry.ModelPolarDomains.hyperbolicType) :
    P202Specs.Geometry.PolarVolumeIntegration.hyperbolic_volumeType := by
  intro n hn a ha S g C hproj hg hC hcomplete p r hr
  letI : ConnectedSpace (P202.HyperboloidData.Hyperboloid n a) :=
    (HyperboloidModel.topology n a ha).1
  obtain ⟨R, hR, _⟩ := CurvatureAlgebra.tensor_exists_unique C
  have hk := hyperbolic_constant_sectional ha S g C hproj hg hC R hR
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  obtain ⟨E, c, hE, hc, hsource, htarget, hp, hvectors, hpolar, hradii⟩ :=
    (hmodel n hn a ha S g C hproj hg hC).1 F hF p
  apply constant_curvature_ball hball hframes hjacobi hsphere g hn hcomplete
    C hC R hR (-(a^2)⁻¹) hk F hF p r hr
  intro v
  simpa only [SmoothMetrics.tangentNorm_smul, abs_of_pos hr, v.property, mul_one]
    using (hvectors (r • v.val)).2.2

/-- Assemble the three actual model-ball identities from the polar density
and the intrinsic model-domain results. -/
theorem model_volume_of_density
    (hball : P202Specs.Geometry.PolarVolumeIntegration.ball_integralType.{0})
    (hframes : P202Specs.Geometry.PolarVolumeDensity.normal_frame_existsType.{0})
    (hjacobi : P202Specs.Geometry.PolarVolumeDensity.jacobi_densityType.{0})
    (hsphere : P202Specs.Geometry.PolarVolumeDensity.sphere_measureType.{0})
    (he : P202Specs.Geometry.ModelPolarDomains.euclideanType)
    (hs : P202Specs.Geometry.ModelPolarDomains.sphericalType)
    (hh : P202Specs.Geometry.ModelPolarDomains.hyperbolicType) :
    P202Specs.Geometry.PolarVolumeIntegration.model_volumeType :=
  ⟨euclidean_volume_of_density hball hframes hjacobi hsphere he,
    spherical_volume_of_density hball hframes hjacobi hsphere hs,
    hyperbolic_volume_of_density hball hframes hjacobi hsphere hh⟩


/-- Integrating the polar measure identity on the intrinsic metric ball,
then removing the null pole and cut locus, gives the full ball formula. -/
theorem ball_integral :
    P202Specs.Geometry.PolarVolumeIntegration.ball_integralType.{u} := by
  intro n M _ _ S g hn hcomplete C hC R hR F hF p r hr
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  letI : SecondCountableTopology M := S.topologicalManifold.secondCountable
  let μ := P202.CutNullData.volume g
  have hμ := volume_properties g
  have hmap := PolarVolumeDensity.polar_measure S g hn hcomplete C hC R hR F hF p μ hμ.2.2 hμ.1 hμ.2.1
  rw [volume_regularDomain g (by omega) hcomplete C hC F hF p] at hmap
  have hreg := PolarVolumeDensity.regularity S g hn hcomplete C hC R hR F hF p
  letI : IsFiniteMeasure (sphereMeasure g p) := (PolarVolumeDensity.sphere_measure S g hn p).1
  have hm : Measurable (fun tv => ENNReal.ofReal (truncatedDensity g F p tv)) :=
    hreg.2.2.1.ennreal_ofReal
  have hball : MeasurableSet (metricBall g p r) := (metricBall_open g p r).measurableSet
  have hpolar : Measurable (polarMap g F p) :=
    (polarMap_continuous g hcomplete C hC F hF p).measurable
  have heq :
      (fun tv => (polarMap g F p ⁻¹' metricBall g p r).indicator
        (fun tv => ENNReal.ofReal (truncatedDensity g F p tv)) tv) =
      (Ioo (0 : ℝ) r ×ˢ (univ : Set (UnitDirection g p))).indicator
        (fun tv => ENNReal.ofReal (truncatedDensity g F p tv)) := by
    funext tv
    by_cases ht : tv ∈ polarDomain g F p
    · have hd := polar_distance g (by omega) hcomplete C hC F hF p tv ht
      have hiff : tv ∈ polarMap g F p ⁻¹' metricBall g p r ↔
          tv ∈ Ioo (0 : ℝ) r ×ˢ (univ : Set (UnitDirection g p)) := by
        simp only [mem_preimage, metricBall, mem_ofPred_eq, hd, mem_prod,
          mem_Ioo, mem_univ, and_true]
        exact ⟨fun h => ⟨ht.1, h⟩, fun h => h.2⟩
      simp only [indicator, hiff]
    · have hz : truncatedDensity g F p tv = 0 := indicator_of_notMem ht _
      simp only [indicator_apply]
      split_ifs <;> simp [hz]
  calc
    ballVolume g p r =
        Measure.map (polarMap g F p)
          ((volume.prod (sphereMeasure g p)).withDensity
            (fun tv => ENNReal.ofReal (truncatedDensity g F p tv))) (metricBall g p r) := by
      rw [hmap]
      rfl
    _ = ∫⁻ tv in polarMap g F p ⁻¹' metricBall g p r,
        ENNReal.ofReal (truncatedDensity g F p tv) ∂volume.prod (sphereMeasure g p) := by
      rw [Measure.map_apply hpolar hball, withDensity_apply _ (hball.preimage hpolar)]
    _ = ∫⁻ tv in Ioo (0 : ℝ) r ×ˢ (univ : Set (UnitDirection g p)),
        ENNReal.ofReal (truncatedDensity g F p tv) ∂volume.prod (sphereMeasure g p) := by
      rw [← lintegral_indicator (hball.preimage hpolar),
        ← lintegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ), heq]
    _ = ∫⁻ t in Ioo (0 : ℝ) r, ∫⁻ v,
        ENNReal.ofReal (truncatedDensity g F p (t,v)) ∂sphereMeasure g p := by
      rw [setLIntegral_prod _ hm.aemeasurable.restrict]
      simp

/-- Actual model-ball volumes, with the same Euclidean sphere normalization
in all three cases. The spherical formula includes its finite endpoint. -/
theorem model_volume : P202Specs.Geometry.PolarVolumeIntegration.model_volumeType :=
  model_volume_of_density ball_integral.{0}
    PolarVolumeDensity.normal_frame_exists.{0} PolarVolumeDensity.jacobi_density.{0}
    PolarVolumeDensity.sphere_measure.{0} ModelPolarDomains.euclidean_geometry
    ModelPolarDomains.spherical_geometry ModelPolarDomains.hyperbolic_geometry

end P202.Geometry.PolarVolumeIntegration
