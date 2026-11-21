import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CutCriterion
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CutTime
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialJacobi
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.NoInteriorConjugate

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace P202.Geometry.CutCriterion
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData SmoothManifolds.MapData
  P202.MetricData P202.CurveData P202.ConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.ExponentialData P202.CompletenessData
  P202.CompleteExponentialData P202.CutTimeData P202.CutCriterionData
  P202.CurvatureData P202.ExponentialJacobiData P202.MinimizingIndexData
  P202.CurveConnectionData P202.FirstVariationData P202.SecondVariationData P202.JacobiData
open Set Filter
open scoped Topology ENNReal
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

abbrev MinimizingInitialVector := @P202.CutCriterionData.MinimizingInitialVector
abbrev IsExponentialInverseAt := @P202.CutCriterionData.IsExponentialInverseAt

/-- Equality of the norm and distance makes the actual radial segment
minimizing against every piecewise C¹ competitor. -/
theorem minimizing_initial_vector_segment
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p)
    (q : M) (w : TangentSpace S p) (hw : MinimizingInitialVector g F p q w) :
    ∃ γ : PiecewiseC1Curve S 0 1,
      γ 0 = p ∧ γ 1 = q ∧
      EqOn γ (fun t => fiberExponential F p (t • w)) (Icc 0 1) ∧
      IsLengthMinimizing g γ := by
  obtain ⟨γ,h0,h1,_,hrad,_,hL⟩ :=
    CompleteExponentialMinimizers.radial_segment g C hC F hF p hfull w
  refine ⟨γ,h0,h1.trans hw.1,hrad,?_⟩
  intro a b η hη0 hη1
  have hd := CompleteExponentialMinimizers.lengthDistance_le_length g η
  rw [hη0,hη1,h0,h1,hw.1] at hd
  rw [hL,hw.2]
  exact hd

/-- Completeness supplies a minimizing initial vector for every endpoint. -/
theorem minimizing_initial_vector_exists [ConnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (hc : LengthMetricComplete g)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p q : M) :
    ∃ w, MinimizingInitialVector g F p q w := by
  obtain ⟨w,γ,_,_,hw,_,_,_,hL,hD,_⟩ :=
    (HopfRinow.hopf_rinow S g C hC).2.2.1 hc F hF p q
  exact ⟨w,hw,hL.symm.trans hD⟩

/-- An equality time supplies its minimizing initial vector on [0,1]. -/
theorem radial_minimizing_initial_vector
    (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) {t : ℝ}
    (ht : t ∈ minimizingTimes g F p v) :
    MinimizingInitialVector g F p (fiberExponential F p (t • v.val)) (t • v.val) := by
  refine ⟨rfl,?_⟩
  rw [SmoothMetrics.tangentNorm_smul,v.property,mul_one,abs_of_nonneg ht.1,ht.2]

/-- Strictly before the supremum there is a larger minimizing time. -/
theorem exists_later_minimizing_time
    (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) {t : ℝ}
    (htc : ENNReal.ofReal t < cutTime g F p v) :
    ∃ s, s ∈ minimizingTimes g F p v ∧ t < s := by
  obtain ⟨r,⟨s,hs,rfl⟩,hrs⟩ := lt_sSup_iff.mp htc
  exact ⟨s,hs,(ENNReal.ofReal_lt_ofReal_iff'.mp hrs).1⟩

/-- The no-corner theorem followed by backward geodesic uniqueness proves
uniqueness at every positive time that admits a larger minimizing time. -/
theorem minimizing_initial_vector_unique_of_later [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p)
    (v : UnitDirection g p) {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hs : s ∈ minimizingTimes g F p v)
    (z : TangentSpace S p)
    (hz : MinimizingInitialVector g F p (fiberExponential F p (t • v.val)) z) :
    z = t • v.val := by
  have htmem := CutTime.minimizingTimes_downward g C hC F hF p hfull v hs ht.le hts.le
  have hnz : tangentNorm g p z = t := hz.2.trans htmem.2
  let u : TangentSpace S p := t⁻¹ • z
  have hunit : tangentNorm g p u = 1 := by
    rw [SmoothMetrics.tangentNorm_smul,hnz,abs_of_pos (inv_pos.mpr ht)]
    exact inv_mul_cancel₀ (ne_of_gt ht)
  have htu : t • u = z := by
    dsimp [u]
    rw [smul_smul,mul_inv_cancel₀ (ne_of_gt ht),one_smul]
  have hIu := CompleteExponentialMinimizers.full_interval C F hF p hfull u
  have hIv := CompleteExponentialMinimizers.full_interval C F hF p hfull v.val
  let I := F.interval ⟨p,u⟩
  let J := F.interval ⟨p,v.val⟩
  let q := F.curve ⟨p,u⟩
  let r := F.curve ⟨p,v.val⟩
  have hqu : IsGeodesicOn S C I.carrier q := (hF ⟨p,u⟩).2.2.1
  have hrv : IsGeodesicOn S C J.carrier r := (hF ⟨p,v.val⟩).2.2.1
  have hdu : Icc 0 t ⊆ I.carrier := by rw [hIu]; exact subset_univ _
  have hdv : Icc t (t+(s-t)) ⊆ J.carrier := by rw [hIv]; exact subset_univ _
  have hqt : t ∈ I.carrier := by rw [hIu]; trivial
  have hrt : t ∈ J.carrier := by rw [hIv]; trivial
  have hrs : s ∈ J.carrier := by rw [hIv]; trivial
  have hposu : (q t).1 = fiberExponential F p z := by
    rw [← htu]
    exact (ExponentialNormalCoordinates.radial_identity_at C F hF p u t hqt).2.symm
  have hposv : (r t).1 = fiberExponential F p (t • v.val) :=
    (ExponentialNormalCoordinates.radial_identity_at C F hF p v.val t hrt).2.symm
  have hunitq : tangentNorm g (q t).1 (q t).2 = 1 := by
    rw [GeodesicIVP.constant_speed S g C hC I q hqu t hqt 0 (hF ⟨p,u⟩).1]
    change tangentNorm g (F.curve ⟨p,u⟩ 0).1 (F.curve ⟨p,u⟩ 0).2 = 1
    rw [(hF ⟨p,u⟩).2.1]
    exact hunit
  have hunitr : tangentNorm g (r t).1 (r t).2 = 1 := by
    rw [GeodesicIVP.constant_speed S g C hC J r hrv t hrt 0 (hF ⟨p,v.val⟩).1]
    change tangentNorm g (F.curve ⟨p,v.val⟩ 0).1 (F.curve ⟨p,v.val⟩ 0).2 = 1
    rw [(hF ⟨p,v.val⟩).2.1]
    exact v.property
  have hq0 : (q 0).1 = p := congrArg Sigma.fst (hF ⟨p,u⟩).2.1
  have hd0 : lengthDistance g (q 0).1 (q t).1 = t := by
    rw [hq0,hposu,hz.1]
    exact htmem.2
  have hd1 : lengthDistance g (q 0).1 (r (t+(s-t))).1 = t+(s-t) := by
    rw [hq0,show t+(s-t)=s by ring,
      ← (ExponentialNormalCoordinates.radial_identity_at C F hF p v.val s hrs).2]
    exact hs.2
  have hphase := CompleteExponentialMinimizers.minimizing_two_geodesics_phase_match
    g C hC I J q r hqu hrv ht (sub_pos.mpr hts) hdu hdv
    ((hposu.trans hz.1).trans hposv.symm) hunitq hunitr hd0 hd1
  have heq := GeodesicIVP.overlap_unique S C I J q r hqu hrv t ⟨hqt,hrt⟩ hphase
    ⟨(hF ⟨p,u⟩).1,(hF ⟨p,v.val⟩).1⟩
  change F.curve ⟨p,u⟩ 0 = F.curve ⟨p,v.val⟩ 0 at heq
  rw [(hF ⟨p,u⟩).2.1,(hF ⟨p,v.val⟩).2.1] at heq
  have hu : u = v.val := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  rw [← htu,hu]

/-- The uniqueness conclusion before cut time, retaining exactly the original
complete connected positive-dimensional hypotheses. -/
theorem interior_unique [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : UnitDirection g p) {t : ℝ} (ht : 0 < t)
    (htc : ENNReal.ofReal t < cutTime g F p v) :
    MinimizingInitialVector g F p (fiberExponential F p (t • v.val)) (t • v.val) ∧
    ∀ z, MinimizingInitialVector g F p (fiberExponential F p (t • v.val)) z →
      z = t • v.val := by
  have hi := CutTime.cut_time_interval S g hn hc C hC F hF p v
  obtain ⟨s,hs,hts⟩ := exists_later_minimizing_time g F p v htc
  exact ⟨radial_minimizing_initial_vector g F p v ((hi.2.2.2.1 t).mpr ⟨ht.le,htc.le⟩),
    minimizing_initial_vector_unique_of_later g C hC F hF p hi.1 v ht hts hs⟩

/-- Restriction of a genuine phase geodesic is an affine closed segment,
with the original one-sided tangent convention. -/
theorem affine_segment_of_geodesic
    (C : Connection (tangentBundle S)) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a < b) (hdom : Icc a b ⊆ I.carrier) :
    IsAffineGeodesicSegment C (fun t => (q t).1) a b := by
  have hsm : SmoothVariationOn S (fun z : ℝ × ℝ => (q z.2).1) 1 a b :=
    GeodesicCriticalityCorners.smooth_curve_constant_variation
      (GeodesicCriticalityCorners.geodesic_position_smoothCurveOn C I q hq hdom) Subset.rfl
  have hT (t : ℝ) (ht : t ∈ Icc a b) :
      segmentTangent S (fun r => (q r).1) a b t = (q t).2 := by
    exact CurveCovariantDerivative.velocity_unique ht (uniqueDiffOn_Icc hab t ht)
      (FirstVariation.segmentVelocity_spec hsm (by norm_num) ht)
      (ParallelTransport.hasVelocityWithinAt_mono (hq t (hdom ht)).1 (subset_univ _))
  refine ⟨hsm,?_⟩
  intro t ht
  exact SecondVariation.hasCovariantDerivativeWithinAt_congr_field C ht
    (SecondVariation.hasCovariantDerivativeWithinAt_mono C (hq t (hdom ht)).2 (subset_univ _)) hT

/-- A nonzero Jacobi section on the actual maximal interval cannot vanish
identically on a nondegenerate subsegment. -/
theorem jacobi_section_nonzero_on_segment
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) {a b : ℝ} (hab : a < b)
    (hdom : Icc a b ⊆ I.carrier)
    (J : RestrictedField S I q) (hJ : IsJacobiSection S C R I q J) (hne : J ≠ 0) :
    ∃ t : ℝ, ∃ ht : t ∈ Icc a b, J ⟨t,hdom ht⟩ ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨K,hK,hKJ⟩ := hJ
  let m : ℝ := (a+b)/2
  have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith,by dsimp [m]; linarith⟩
  have hmI : m ∈ I.carrier := hdom (Ioo_subset_Icc_self hm)
  have hzero (t : ℝ) (ht : t ∈ Icc a b) : K t = 0 :=
    (hKJ ⟨t,hdom ht⟩).trans (hn t ht)
  obtain ⟨D,hD⟩ := hK
  have hder0 : HasCovariantDerivativeAt C (fun t => (q t).1) (fun _ => 0) m 0 := by
    simpa only [zero_smul] using CurveCovariantDerivative.derivative_const_smul C (hD m hmI).1 (0:ℝ)
  have hderK : HasCovariantDerivativeAt C (fun t => (q t).1) K m 0 := by
    apply JacobiVariation.covariantDerivative_congr_field C hder0
    filter_upwards [isOpen_Ioo.mem_nhds hm] with t ht
    exact (hzero t (Ioo_subset_Icc_self ht)).symm
  have hzeroJac : IsJacobiField C R I.carrier q (fun _ => 0) :=
    ExponentialJacobi.zero_jacobi C R I.carrier q hq
  obtain ⟨L,_,_,_,huniq⟩ := JacobiIVP.exists_unique S g C hC R hR I q hq m hmI 0 0
  have hKL := huniq K ⟨D,hD⟩ (hzero m (Ioo_subset_Icc_self hm)) hderK
  have h0L := huniq (fun _ => 0) hzeroJac rfl hder0
  apply hne
  funext t
  exact (hKJ t).symm.trans ((hKL t.val t.property).trans (h0L t.val t.property).symm)

/-- Interior nonconjugacy on the full radial interval follows from the
closed-segment no-interior-conjugate theorem, with a nonzero restriction
proved rather than assumed. -/
theorem radial_nonconjugate_of_later [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p) (v : UnitDirection g p)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) (hs : s ∈ minimizingTimes g F p v)
    (htI : t ∈ (F.interval ⟨p,v.val⟩).carrier) :
    ¬ ConjugateAlong S C R (F.interval ⟨p,v.val⟩) (F.curve ⟨p,v.val⟩)
      ⟨0,(hF ⟨p,v.val⟩).1⟩ ⟨t,htI⟩ := by
  let I := F.interval ⟨p,v.val⟩
  let q := F.curve ⟨p,v.val⟩
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p,v.val⟩).2.2.1
  have hI : I.carrier = univ := CompleteExponentialMinimizers.full_interval C F hF p hfull v.val
  have hdom : Icc 0 s ⊆ I.carrier := by rw [hI]; exact subset_univ _
  have hdomt : Icc 0 t ⊆ I.carrier := by rw [hI]; exact subset_univ _
  have hspos : 0 < s := ht.trans hts
  let γ := CompleteExponentialMinimizers.geodesicRepresentative C I q hq hspos.le hdom
  have hγ : IsAffineGeodesicSegment C γ 0 s := affine_segment_of_geodesic C I q hq hspos hdom
  have hL : length g γ = s := by
    change (∫ r in 0..s, speed g γ r) = s
    rw [GeodesicCriticalityCorners.geodesic_piece_length_of_eqOn g C hC I q hq
      hspos hdom γ (fun _ _ => rfl)]
    change tangentNorm g (F.curve ⟨p,v.val⟩ 0).1 (F.curve ⟨p,v.val⟩ 0).2 * (s-0) = s
    rw [(hF ⟨p,v.val⟩).2.1,v.property]
    ring
  have hγ0 : γ 0 = p := congrArg Sigma.fst (hF ⟨p,v.val⟩).2.1
  have hγs : γ s = fiberExponential F p (s • v.val) :=
    (ExponentialNormalCoordinates.radial_identity_at C F hF p v.val s
      (hdom ⟨hspos.le,le_rfl⟩)).2.symm
  have hmin : IsLengthMinimizing g γ := by
    intro a b η ha hb
    have hd := CompleteExponentialMinimizers.lengthDistance_le_length g η
    rw [ha,hb,hγ0,hγs,hs.2] at hd
    rwa [hL]
  rintro ⟨J,⟨hJ,hJ0,hJt⟩,hne⟩
  obtain ⟨K,hK,hKJ⟩ := hJ
  have hnonzero := jacobi_section_nonzero_on_segment g C hC R hR I q hq ht hdomt J
    ⟨K,hK,hKJ⟩ hne
  have hseg := NoInteriorConjugate.segment_jacobi_of_open C R hq ht hdomt hK
  apply NoInteriorConjugate.no_interior_conjugate g C hC R hR γ hspos hγ hmin t ht hts
  refine ⟨K,hseg,?_,?_,?_⟩
  · exact (hKJ ⟨0,(hF ⟨p,v.val⟩).1⟩).trans hJ0
  · exact (hKJ ⟨t,htI⟩).trans hJt
  · obtain ⟨r,hr,hne⟩ := hnonzero
    exact ⟨r,hr,fun h => hne ((hKJ ⟨r,hdomt hr⟩).symm.trans h)⟩

/-- Unique and nonconjugate minimizing segments at every positive pre-cut time. -/
theorem interior_unique_nonconjugate :
    P202Specs.Geometry.CutCriterion.interior_unique_nonconjugateType.{u} := by
  intro n M _ _ S g hn hc C hC R hR F hF p v t ht htc
  obtain ⟨hmin,huniq⟩ := interior_unique g hn hc C hC F hF p v ht htc
  have hfull := (CutTime.cut_time_interval S g hn hc C hC F hF p v).1
  obtain ⟨s,hs,hts⟩ := exists_later_minimizing_time g F p v htc
  have htI : t ∈ (F.interval ⟨p,v.val⟩).carrier := by
    rw [CompleteExponentialMinimizers.full_interval C F hF p hfull v.val]
    trivial
  exact ⟨hmin,huniq,htI,radial_nonconjugate_of_later g C hC R hR F hF p hfull v ht hts hs htI⟩

/-- Metric balls in any linear coordinates of the actual tangent fiber
are compact; the coordinate norm is continuous. -/
theorem fiber_norm_compact_coordinates (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Continuous (fun x : Euclidean n => tangentNorm g p (E.symm x)) ∧
      ∀ R : ℝ, IsCompact {x : Euclidean n | tangentNorm g p (E.symm x) ≤ R} := by
  obtain ⟨B,hB⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist g p
  let A := (E.symm.trans B).toContinuousLinearEquiv
  have hnorm : Continuous (fun x : Euclidean n => tangentNorm g p (B.symm x)) :=
    ExponentialNormalCoordinates.orthonormal_norm_continuous g p B hB
  have hA (x : Euclidean n) : B.symm (A x) = E.symm x := B.symm_apply_apply _
  refine ⟨by simpa only [Function.comp_def,hA] using hnorm.comp A.continuous,?_⟩
  intro R
  have hK : IsCompact {x : Euclidean n | tangentNorm g p (B.symm x) ≤ R} := by
    apply (isCompact_closedBall (0 : Euclidean n) R).of_isClosed_subset
      (isClosed_le hnorm continuous_const)
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (ExponentialNormalCoordinates.coordinate_norm_le_metric_norm g p B hB x).trans hx
  have heq : {x : Euclidean n | tangentNorm g p (E.symm x) ≤ R} =
      A.symm '' {x : Euclidean n | tangentNorm g p (B.symm x) ≤ R} := by
    ext x
    constructor
    · intro hx
      refine ⟨A x,?_,A.symm_apply_apply x⟩
      change tangentNorm g p (E.symm x) ≤ R at hx
      change tangentNorm g p (B.symm (A x)) ≤ R
      rw [hA]
      exact hx
    · rintro ⟨y,hy,rfl⟩
      have h := hA (A.symm y)
      rw [A.apply_symm_apply] at h
      change tangentNorm g p (E.symm (A.symm y)) ≤ R
      rw [← h]
      exact hy
  rw [heq]
  exact hK.image A.symm.continuous

/-- Compactness of bounded minimizing vectors gives uniform trapping near a
unique minimizer. This is the compactness step of the source stability proof,
expressed without choosing a sequence of minimizers. -/
theorem minimizing_vectors_trapped [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p) (q : M)
    (w : TangentSpace S p) (huniq : ∀ z, MinimizingInitialVector g F p q z → z = w)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (V : Set (Euclidean n)) (hV : IsOpen V) (hwV : E w ∈ V) :
    ∃ U : Set M, IsOpen U ∧ q ∈ U ∧
      ∀ y ∈ U, ∀ z, MinimizingInitialVector g F p y z → E z ∈ V := by
  let : T2Space M := S.topologicalManifold.hausdorff
  let f : Euclidean n → M := fun x => fiberExponential F p (E.symm x)
  let N : Euclidean n → ℝ := fun x => tangentNorm g p (E.symm x)
  let d : M → ℝ := fun y => lengthDistance g p y
  have hfc : Continuous f := CompleteExponentialMinimizers.exponential_coordinates_continuous C F hF p hfull E
  have hdc : Continuous d :=
    CompleteExponentialMinimizers.lengthDistance_continuous g |>.comp (continuous_const.prodMk continuous_id)
  obtain ⟨hNc,hcompact⟩ := fiber_norm_compact_coordinates g p E
  let B : Set (Euclidean n) := {x | N x ≤ d q + 1} ∩ (Vᶜ ∩ {x | N x = d (f x)})
  have hB : IsCompact B := (hcompact (d q + 1)).inter_right
    (hV.isClosed_compl.inter (isClosed_eq hNc (hdc.comp hfc)))
  have hbad : IsClosed (f '' B) := (hB.image hfc).isClosed
  have hq : q ∉ f '' B := by
    rintro ⟨x,hx,hxq⟩
    have hm : MinimizingInitialVector g F p q (E.symm x) :=
      ⟨hxq,by change N x = d q; rw [← hxq]; exact hx.2.2⟩
    have hxw : x = E w := by simpa only [LinearEquiv.apply_symm_apply] using congrArg E (huniq _ hm)
    exact hx.2.1 (hxw.symm ▸ hwV)
  let U : Set M := (f '' B)ᶜ ∩ {y | d y < d q + 1}
  refine ⟨U,hbad.isOpen_compl.inter (isOpen_lt hdc continuous_const),⟨hq,by dsimp [d]; linarith⟩,?_⟩
  intro y hy z hz
  by_contra hzV
  have hx : E z ∈ B := by
    refine ⟨?_,hzV,?_⟩
    · change tangentNorm g p (E.symm (E z)) ≤ d q + 1
      rw [E.symm_apply_apply,hz.2]
      exact hy.2.le
    · change tangentNorm g p (E.symm (E z)) = d (fiberExponential F p (E.symm (E z)))
      rw [E.symm_apply_apply,hz.1]
      exact hz.2
  exact hy.1 ⟨E z,hx,by simpa only [f,E.symm_apply_apply] using hz.1⟩

/-- The inverse function theorem at an arbitrary nonsingular exponential
vector, expressed as a chart of the original smooth structure. -/
theorem exponential_inverse_of_nonsingular
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p)
    (w : TangentSpace S p) (hbij : Function.Bijective (fiberDifferential S F p w)) :
    ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (c : ModelChart n .euclidean M),
      IsExponentialInverseAt F p w E c := by
  let E := selectedCoordinates S p
  let e := (selectedChart S (fiberExponential F p w)).val
  have he := (selectedChart S (fiberExponential F p w)).property.1
  have hqe := (selectedChart S (fiberExponential F p w)).property.2
  let D := selectedCoordinates S (fiberExponential F p w)
  let f : Euclidean n → M := fun x => fiberExponential F p (E.symm x)
  let k : Euclidean n → Euclidean n := fun x => (e (f x)).val
  let U : Set (Euclidean n) := f ⁻¹' e.source
  have hfc : Continuous f := CompleteExponentialMinimizers.exponential_coordinates_continuous C F hF p hfull E
  have hU : IsOpen U := e.open_source.preimage hfc
  have hwU : E w ∈ U := by
    change fiberExponential F p (E.symm (E w)) ∈ e.source
    rw [E.symm_apply_apply]
    exact hqe
  have hk : ContDiffOn ℝ (⊤ : ℕ∞) k U := by
    intro x hx
    exact (ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis C F hF p E e he x
      (hfull _) hx).contDiffWithinAt
  let L := fderiv ℝ k (E w)
  have hL : HasFDerivAt k L (E w) :=
    ((hk.contDiffAt (hU.mem_nhds hwU)).differentiableAt (by simp)).hasFDerivAt
  have hcoord (x : Euclidean n) : L x = D (fiberDifferential S F p w (E.symm x)) := by
    change L x = D (D.symm (L (E (E.symm x))))
    simp only [E.apply_symm_apply,D.apply_symm_apply]
  have hLb : Function.Bijective L := by
    have hh := D.bijective.comp (hbij.comp E.symm.bijective)
    simpa only [Function.comp_def,← hcoord] using hh
  obtain ⟨j,hwj,hjk,hjs⟩ := SmoothManifolds.InteriorInverse.euclidean_inverse
    (⊤ : ℕ∞) (by simp) k U hU hk (E w) hwU L hL hLb
  let b := SmoothManifolds.InteriorInverse.ambientChart e
  have hfb (x : Euclidean n) (hx : x ∈ U) : f x ∈ b.source := by
    refine ⟨hx,?_⟩
    change (e (f x)).val ∈ interior (modelSet n .euclidean)
    simp [modelSet]
  let h := (j.restrOpen U hU).trans b.symm
  have hsource (x : Euclidean n) (hx : x ∈ h.source) : x ∈ U := hx.1.2
  have heq : EqOn h f h.source := by
    intro x hx
    change b.symm (j x) = f x
    have hjx : j x = b (f x) := congrFun hjk x
    rw [hjx,b.left_inv (hfb x (hsource x hx))]
  have hwh : E w ∈ h.source := by
    refine ⟨⟨hwj,hwU⟩,?_⟩
    change j (E w) ∈ b.target
    rw [show j (E w) = b (f (E w)) from congrFun hjk _]
    exact b.map_source (hfb _ hwU)
  have hfw : f (E w) = fiberExponential F p w := by simp only [f,E.symm_apply_apply]
  have hwhq : h (E w) = fiberExponential F p w := (heq hwh).trans hfw
  have hforward : ∀ x ∈ h.source, ∀ d ∈ S.smoothStructure.val, h x ∈ d.source →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (d (h y)).val) x := by
    intro x hx d hd hxd
    have hfd : f x ∈ d.source := by rwa [← heq hx]
    apply (ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis C F hF p E d hd x
      (hfull _) hfd).congr_of_eventuallyEq
    filter_upwards [h.open_source.mem_nhds hx] with y hy
    exact congrArg (fun z => (d z).val) (heq hy)
  have hback : ∀ y ∈ h.target, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
      S.smoothStructure.val h.symm y := by
    intro y hy
    have hye : y ∈ e.source := hy.1.1
    have hyj : (e y).val ∈ j.target := hy.2.1
    refine ⟨h.symm.continuousAt hy,?_⟩
    intro d hd hyd
    have ht := SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 d hd e he) hyd hye
    have hi : LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (e z).val) h.symm y :=
      ⟨j.target,j.open_target,hyj,j.symm,hjs,Eventually.of_forall (fun _ => rfl)⟩
    exact SmoothManifolds.LocalCoordinateExtension.comp hi ht
  let c := ExponentialNormalCoordinates.parametrizationChart h
  have hcs : c.source = h.target := ExponentialNormalCoordinates.parametrizationChart_source h
  have hct : c.target = {x | x.val ∈ h.source} := ExponentialNormalCoordinates.parametrizationChart_target h
  refine ⟨E,c,ExponentialNormalCoordinates.parametrizationChart_mem h hforward hback,?_,?_,?_⟩
  · rw [hcs,← hwhq]
    exact h.map_source hwh
  · change h.symm (fiberExponential F p w) = E w
    rw [← hwhq,h.left_inv hwh]
  · intro x hx
    rw [hct] at hx
    exact (heq hx).symm

/-- Stability of a unique nonsingular minimizing initial vector. -/
theorem minimizing_stability : P202Specs.Geometry.CutCriterion.minimizing_stabilityType.{u} := by
  intro n M _ _ S g _hn hc C hC F hF p q w _hqp hw huniq hbij
  have hfull : FullExponentialAt F p := HopfRinow.full_exponential_of_geodesicallyComplete C
    ((HopfRinow.hopf_rinow S g C hC).1.mp hc) F hF p
  obtain ⟨E,c,hcInv⟩ := exponential_inverse_of_nonsingular C F hF p hfull w hbij
  let j : Euclidean n → ModelSpace n .euclidean := fun x => ⟨x,mem_univ _⟩
  let V : Set (Euclidean n) := j ⁻¹' c.target
  have hj : Continuous j := continuous_id.subtype_mk _
  have hV : IsOpen V := c.open_target.preimage hj
  have hwV : E w ∈ V := by
    have hct := c.map_source hcInv.2.1
    have hcval := hcInv.2.2.1
    change j (E w) ∈ c.target
    have heq : j (E w) = c (fiberExponential F p w) := Subtype.ext hcval.symm
    rwa [heq]
  obtain ⟨U,hU,hqU,htrap⟩ := minimizing_vectors_trapped g C F hF p hfull q w huniq E V hV hwV
  refine ⟨E,c,U ∩ c.source,hcInv,hU.inter c.open_source,⟨hqU,hw.1 ▸ hcInv.2.1⟩,
    inter_subset_right,?_⟩
  intro y hy z
  have hexp : ∀ z : TangentSpace S p, E z ∈ V →
      fiberExponential F p z = c.symm (j (E z)) := by
    intro z hz
    simpa only [j,E.symm_apply_apply] using hcInv.2.2.2 (j (E z)) hz
  have hcoord : ∀ z : TangentSpace S p, MinimizingInitialVector g F p y z →
      z = E.symm (c y).val := by
    intro z hz
    have hzin := htrap y hy.1 z hz
    have hcZ : c.symm (j (E z)) = y := (hexp z hzin).symm.trans hz.1
    have hh := c.symm.injOn hzin (c.map_source hy.2) (hcZ.trans (c.left_inv hy.2).symm)
    have he : E z = (c y).val := congrArg Subtype.val hh
    exact E.injective (by simpa only [E.apply_symm_apply] using he)
  constructor
  · exact hcoord z
  · intro hz
    obtain ⟨z₀,hz₀⟩ := minimizing_initial_vector_exists g C hC hc F hF p y
    have heq := (hcoord z₀ hz₀).trans hz.symm
    exact heq ▸ hz₀

/-- A finite cut endpoint is conjugate along its own radial segment, or
has a second minimizing initial vector, or both. -/
theorem finite_cut_criterion : P202Specs.Geometry.CutCriterion.finite_cut_criterionType.{u} := by
  intro n M _ _ S g hn hc C hC R hR F hF p v hfin
  classical
  dsimp only
  let t := (cutTime g F p v).toReal
  have hi := CutTime.cut_time_interval S g hn hc C hC F hF p v
  have ht : 0 < t := (hi.2.2.2.2.1 hfin).2.1
  have htmem : t ∈ minimizingTimes g F p v := by
    rw [(hi.2.2.2.2.1 hfin).1]
    exact ⟨ht.le,le_rfl⟩
  have hmin := radial_minimizing_initial_vector g F p v htmem
  refine ⟨hmin,?_⟩
  have htI : t ∈ (F.interval ⟨p,v.val⟩).carrier := by
    rw [CompleteExponentialMinimizers.full_interval C F hF p hi.1 v.val]
    trivial
  by_cases hconj : ∃ htI : t ∈ (F.interval ⟨p,v.val⟩).carrier,
      ConjugateAlong S C R (F.interval ⟨p,v.val⟩) (F.curve ⟨p,v.val⟩)
        ⟨0,(hF ⟨p,v.val⟩).1⟩ ⟨t,htI⟩
  · exact Or.inl hconj
  by_cases huniq : ∀ z, MinimizingInitialVector g F p (fiberExponential F p (t • v.val)) z →
      z = t • v.val
  · exfalso
    have hbij : Function.Bijective (fiberDifferential S F p (t • v.val)) := by
      by_contra hsing
      exact hconj ⟨htI,(ExponentialJacobi.conjugacy_singularity S g C hC R hR F hF p v.val t ht htI).mpr hsing⟩
    have hqp : fiberExponential F p (t • v.val) ≠ p := by
      intro heq
      have hd := htmem.2
      rw [heq,CompleteExponentialMinimizers.lengthDistance_self] at hd
      linarith
    obtain ⟨E,c,U,hcInv,hU,hqU,hUc,hstable⟩ :=
      minimizing_stability S g hn hc C hC F hF p _ (t • v.val) hqp hmin huniq hbij
    let j : Euclidean n → ModelSpace n .euclidean := fun x => ⟨x,mem_univ _⟩
    let x : ℝ → ModelSpace n .euclidean := fun r => j (r • E v.val)
    let f : ℝ → M := fun r => fiberExponential F p (r • v.val)
    have hxc : Continuous x := (continuous_id.smul continuous_const).subtype_mk _
    have hfc : Continuous f := CompleteExponentialMinimizers.radial_position_continuous C F hF p hi.1 v.val
    have hxt : x t ∈ c.target := by
      have hcval := hcInv.2.2.1
      have heq : x t = c (f t) := by
        apply Subtype.ext
        exact (E.map_smul t v.val).symm.trans hcval.symm
      rw [heq]
      exact c.map_source hcInv.2.1
    have hnear : f ⁻¹' U ∩ x ⁻¹' c.target ∈ 𝓝 t :=
      ((hU.preimage hfc).inter (c.open_target.preimage hxc)).mem_nhds ⟨hqU,hxt⟩
    obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
    let s := (t+b)/2
    have hts : t < s := by dsimp [s]; linarith [hab.2]
    have hsab : s ∈ Ioo a b := ⟨hab.1.trans hts,by dsimp [s]; linarith [hab.2]⟩
    obtain ⟨hsU,hsT⟩ := hsub hsab
    have hinv : E.symm (c (f s)).val = s • v.val := by
      have hxval : E.symm (x s).val = s • v.val := by simp only [x,j,map_smul,E.symm_apply_apply]
      have hfx : f s = c.symm (x s) := by
        simpa only [hxval] using hcInv.2.2.2 (x s) hsT
      rw [hfx,c.right_inv hsT,hxval]
    have hsmin : MinimizingInitialVector g F p (f s) (s • v.val) :=
      (hstable (f s) hsU (s • v.val)).mpr hinv.symm
    have hss : s ∈ minimizingTimes g F p v := by
      refine ⟨(ht.trans hts).le,?_⟩
      have he := hsmin.2.symm
      simpa only [SmoothMetrics.tangentNorm_smul,v.property,mul_one,
        abs_of_pos (ht.trans hts)] using he
    have hle : s ≤ t :=
      (ENNReal.ofReal_le_iff_le_toReal hfin).mp ((hi.2.2.2.1 s).mp hss).2
    exact (not_lt_of_ge hle) hts
  · push Not at huniq
    obtain ⟨z,hz,hne⟩ := huniq
    exact Or.inr ⟨z,hne,hz⟩

end P202.Geometry.CutCriterion
