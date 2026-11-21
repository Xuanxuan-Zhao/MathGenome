import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CartanHadamard
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialPullbackComplete
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CompleteLocalIsometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CoveringMetricCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.HopfRinow
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace P202.Geometry.CartanHadamard
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.CurvatureData P202.NonpositiveJacobiData P202.CompletenessData
  P202.ExponentialData P202.ExponentialPullbackData P202.CompleteExponentialData
  P202.CoveringMetricData
open Set Filter
open scoped _root_.Topology
universe u

/-- The topology of an affine model is the ordinary vector-space topology,
so its entire intrinsic fiber is simply connected, including in rank zero. -/
theorem affine_simplyConnected {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {p : M} (A : AffineFiberModel S p) :
    letI := A.topology
    SimplyConnectedSpace (TangentSpace S p) := by
  letI := A.topology
  exact (ExponentialPullbackComplete.affine_homeomorph A).toHomotopyEquiv.simplyConnectedSpace

/-- Completeness and the nonsingular pullback metric make the actual
exponential a surjective smooth covering. -/
theorem exponential_covering :
    P202Specs.Geometry.CartanHadamard.exponential_coveringType.{u} := by
  intro n M _ _ S g C hC R hR hK hc F hF p A
  letI := A.topology
  letI := affine_simplyConnected A
  obtain ⟨h, _, hi, _, _, hh⟩ :=
    ExponentialPullbackComplete.pullback_complete S g C hC R hR hK hc F hF p A
  have hcov := (CompleteLocalIsometry.complete_local_isometry
    A.manifold S h g (fiberExponential F p) hi hh).1
  exact ⟨fun v => (NonpositiveJacobiGrowth.nonsingular S g C hC R hR hK hc F hF p v).1,
    hcov, hi.1⟩

section Covering
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A connected covering of a simply connected locally path connected space
has a global continuous inverse. The section comes from lifting the identity;
uniqueness of lifts makes it a left inverse as well. -/
theorem covering_bijective [ConnectedSpace X] [SimplyConnectedSpace Y]
    [LocallyPathConnectedSpace Y] (f : X → Y)
    (hf : P202Specs.Topology.Covering f) : Function.Bijective f := by
  have hcov := P202.Topology.covering_to_library hf
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨s, hs, _⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id Y) (f x) x rfl
  have hsf : s ∘ f = id := by
    apply hcov.eq_of_comp_eq (s.continuous.comp hcov.continuous) continuous_id
      (funext fun z => congrFun hs.2 (f z)) x hs.1
  exact ⟨fun a b hab => by
    have heq := congrArg s hab
    simpa only [show ∀ z, s (f z) = z from fun z => congrFun hsf z] using heq,
    hf.1⟩

/-- A bijective local diffeomorphism has a smooth global inverse. -/
theorem diffeomorphism_of_bijective {n m : ℕ}
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold m .euclidean Y)
    (f : X → Y) (hf : SmoothManifolds.TensorData.IsLocalDiffeomorphism S T f)
    (hb : Function.Bijective f) :
    ∃ D : Diffeomorph S.smoothStructure.val T.smoothStructure.val,
      ∀ x, D.toEquiv x = f x := by
  let e := Equiv.ofBijective f hb
  have hinv : ManifoldSmooth T.smoothStructure.val S.smoothStructure.val e.symm := by
    intro y
    obtain ⟨g, hg, _, _, hfg⟩ := hf.2 (e.symm y)
    have hey : f (e.symm y) = y := e.apply_symm_apply y
    rw [hey] at hg hfg
    apply SmoothManifolds.manifoldContDiffAt_congr hg
    filter_upwards [hfg] with z hz
    exact hb.1 (hz.trans (e.apply_symm_apply z).symm)
  exact ⟨⟨e, hf.1, hinv⟩, fun _ => rfl⟩
end Covering

/-- Simple connectedness of the base removes all additional sheets. -/
theorem exponential_diffeomorphism :
    P202Specs.Geometry.CartanHadamard.exponential_diffeomorphismType.{u} := by
  intro n M _ _ _ S g C hC R hR hK hc F hF p A
  letI := A.topology
  letI := affine_simplyConnected A
  letI := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  have hcov := (exponential_covering S g C hC R hR hK hc F hF p A).2
  exact diffeomorphism_of_bijective A.manifold S _ hcov.2
    (covering_bijective _ hcov.1)

section Geodesics
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
  {S : SmoothManifold n .euclidean M}

/-- On a complete manifold every geodesic segment agrees, in both position
and velocity, with the global maximal trajectory having its initial phase. -/
theorem segment_agrees_family (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (hc : LengthMetricComplete g) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p q : M)
    (I : D13Unified.OpenTimeInterval) (γ : ℝ → Phase S)
    (hI : Icc 0 1 ⊆ I.carrier) (hγ : IsGeodesicOn S C I.carrier γ)
    (hp : (γ 0).1 = p) (hq : (γ 1).1 = q) :
    ∃ v : TangentSpace S p, fiberExponential F p v = q ∧
      EqOn γ (F.curve ⟨p, v⟩) I.carrier := by
  obtain ⟨v, hv⟩ : ∃ v : TangentSpace S p, γ 0 = ⟨p, v⟩ := by
    subst p
    exact ⟨(γ 0).2, rfl⟩
  have hwhole := MetricGeodesicCompleteness.metric_complete_geodesically_complete
    S g C hC hc ⟨p, v⟩ (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩) (hF ⟨p, v⟩)
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hagr := GeodesicIVP.overlap_unique S C I (F.interval ⟨p, v⟩)
    γ (F.curve ⟨p, v⟩) hγ (hF ⟨p, v⟩).2.2.1 0
    ⟨hI hzero, (hF ⟨p, v⟩).1⟩ (hv.trans (hF ⟨p, v⟩).2.1.symm)
  have hagr' : EqOn γ (F.curve ⟨p, v⟩) I.carrier :=
    fun t ht => hagr ⟨ht, hwhole ▸ mem_univ t⟩
  exact ⟨v, (congrArg Sigma.fst (hagr' (hI hone))).symm.trans hq, hagr'⟩

/-- Hopf–Rinow supplies minimizers. Injectivity of the exponential and
geodesic IVP uniqueness identify every normalized geodesic with that minimizer. -/
theorem unique_normalized_geodesics :
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R → LengthMetricComplete g →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ p : M, MinimizingGeodesicsFrom g C F p ∧
      ∀ (q : M) (I J : D13Unified.OpenTimeInterval) (γ η : ℝ → Phase S),
        Icc 0 1 ⊆ I.carrier → Icc 0 1 ⊆ J.carrier →
        IsGeodesicOn S C I.carrier γ → IsGeodesicOn S C J.carrier η →
        (γ 0).1 = p → (η 0).1 = p → (γ 1).1 = q → (η 1).1 = q →
        EqOn γ η (Icc 0 1) := by
  intro n M _ _ _ S g C hC R hR hK hc F hF p
  obtain ⟨A⟩ := ExponentialPullbackComplete.affine_model_exists S p
  letI := A.topology
  obtain ⟨D, hD⟩ := exponential_diffeomorphism S g C hC R hR hK hc F hF p A
  have hinj : Function.Injective (fiberExponential F p) := by
    intro v w hvw
    apply D.toEquiv.injective
    simpa only [hD] using hvw
  refine ⟨(HopfRinow.complete_conclusions g C hC hc F hF p).1, ?_⟩
  intro q I J γ η hI hJ hγ hη hp hηp hq hηq
  obtain ⟨v, hv, hγv⟩ := segment_agrees_family g C hC hc F hF p q I γ hI hγ hp hq
  obtain ⟨w, hw, hηw⟩ := segment_agrees_family g C hC hc F hF p q J η hJ hη hηp hηq
  have hvw : v = w := hinj (hv.trans hw.symm)
  subst w
  exact fun t ht => (hγv (hI ht)).trans (hηw (hJ ht)).symm
/-- Affine normalization handles arbitrary nondegenerate parameter intervals.
The comparison is in position; velocities transform with the expected factors. -/
theorem unique_minimizers :
    P202Specs.Geometry.CartanHadamard.unique_minimizersType.{u} := by
  intro n M _ _ _ S g C hC R hR hK hc F hF p
  have hu := unique_normalized_geodesics S g C hC R hR hK hc F hF p
  refine ⟨hu.1, ?_⟩
  intro q a b c d hab hcd I J γ η hI hJ hγ hη hp hηp hq hηq
  let I' := GeodesicIVP.affineInterval I (b - a) a (ne_of_gt (sub_pos.mpr hab))
  let J' := GeodesicIVP.affineInterval J (d - c) c (ne_of_gt (sub_pos.mpr hcd))
  have hI' : Icc (0 : ℝ) 1 ⊆ I'.carrier := by
    intro t ht
    apply hI
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) ht.1]
    · nlinarith [mul_le_of_le_one_right (sub_nonneg.mpr hab.le) ht.2]
  have hJ' : Icc (0 : ℝ) 1 ⊆ J'.carrier := by
    intro t ht
    apply hJ
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hcd.le) ht.1]
    · nlinarith [mul_le_of_le_one_right (sub_nonneg.mpr hcd.le) ht.2]
  have heq := hu.2 q I' J'
    (affineCurve S γ (b - a) a) (affineCurve S η (d - c) c) hI' hJ'
    (GeodesicIVP.affine_geodesic S C _ γ _ _ hγ)
    (GeodesicIVP.affine_geodesic S C _ η _ _ hη)
    (by simpa only [affineCurve, mul_zero, zero_add] using hp)
    (by simpa only [affineCurve, mul_zero, zero_add] using hηp)
    (by simpa only [affineCurve, mul_one, sub_add_cancel] using hq)
    (by simpa only [affineCurve, mul_one, sub_add_cancel] using hηq)
  intro t ht
  have hpos := congrArg (fun z : Phase S => z.1) (heq ht)
  exact hpos
end Geodesics

section Universal
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace B] [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
  [LocallyPathConnectedSpace X] [LocallyPathConnectedSpace Y]

/-- The lift criterion and uniqueness of lifts identify any two simply
connected smooth coverings of the same base by a diffeomorphism over the base. -/
theorem simplyConnected_cover_diffeomorphism {n : ℕ}
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean Y)
    (U : SmoothManifold n .euclidean B) (f : X → B) (g : Y → B)
    (hf : SmoothCovering S U f) (hg : SmoothCovering T U g)
    (x : X) (y : Y) (hxy : g y = f x) :
    ∃ D : Diffeomorph S.smoothStructure.val T.smoothStructure.val,
      ∀ z, g (D.toEquiv z) = f z := by
  have hfc := P202.Topology.covering_to_library hf.1
  have hgc := P202.Topology.covering_to_library hg.1
  obtain ⟨L, hL, _⟩ := hgc.existsUnique_continuousMap_lifts ⟨f, hfc.continuous⟩ x y hxy
  obtain ⟨K, hK, _⟩ := hfc.existsUnique_continuousMap_lifts ⟨g, hgc.continuous⟩ y x hxy.symm
  have hKL : K ∘ L = id := by
    apply hfc.eq_of_comp_eq (K.continuous.comp L.continuous) continuous_id
      (funext fun z => (congrFun hK.2 (L z)).trans (congrFun hL.2 z)) x
    exact (congrArg K hL.1).trans hK.1
  have hLK : L ∘ K = id := by
    apply hgc.eq_of_comp_eq (L.continuous.comp K.continuous) continuous_id
      (funext fun z => (congrFun hL.2 (K z)).trans (congrFun hK.2 z)) y
    exact (congrArg L hK.1).trans hL.1
  have hLs := SmoothManifolds.CoveringStructure.smooth_lift T U S g
    ((CoveringMetricCompleteness.smoothCovering_iff_branches T U g).mp hg).2
    f L hf.2.1 L.continuous hL.2
  have hKs := SmoothManifolds.CoveringStructure.smooth_lift S U T f
    ((CoveringMetricCompleteness.smoothCovering_iff_branches S U f).mp hf).2
    g K hg.2.1 K.continuous hK.2
  exact ⟨⟨⟨L, K, fun z => congrFun hKL z, fun z => congrFun hLK z⟩, hLs, hKs⟩,
    fun z => congrFun hL.2 z⟩
end Universal

/-- A global smooth chart gives an actual diffeomorphism to ordinary R^n,
whose identity coordinate chart suffices to test its usual smoothness. -/
theorem diffeomorphism_of_global_chart {n : ℕ} {E : Type u} [TopologicalSpace E]
    (T : SmoothManifold n .euclidean E) (c : ModelChart n .euclidean E)
    (hc : c ∈ T.smoothStructure.val) (hs : c.source = univ) (ht : c.target = univ) :
    ∃ D : Diffeomorph T.smoothStructure.val {P202.CartanHadamardData.euclideanChart n},
      ∀ x, D.toEquiv x = (c x).val := by
  let e : E ≃ₜ Euclidean n :=
    (c.toHomeomorphOfSourceEqUnivTargetEqUniv hs ht).trans (Homeomorph.Set.univ _)
  have hf : ManifoldSmooth T.smoothStructure.val
      {P202.CartanHadamardData.euclideanChart n} e := by
    intro x
    refine ⟨e.continuous.continuousAt, ?_⟩
    rintro b hb d hd hx hy
    have hdd := Set.mem_singleton_iff.mp hd
    subst d
    exact SmoothManifolds.chartContDiffAt_of_compatible
      (T.smoothStructure.property.1.2 b hb c hc) hx (hs ▸ mem_univ x)
  have hg : ManifoldSmooth {P202.CartanHadamardData.euclideanChart n}
      T.smoothStructure.val e.symm := by
    intro y
    refine ⟨e.symm.continuous.continuousAt, ?_⟩
    rintro d hd b hb hy hx
    have hdd := Set.mem_singleton_iff.mp hd
    subst d
    have hh := SmoothManifolds.chartContDiffAt_of_compatible
      (T.smoothStructure.property.1.2 c hc b hb) (hs ▸ mem_univ (e.symm y)) hx
    have hh' := SmoothManifolds.LocalCoordinateExtension.precomp hh
      e.symm.continuous.continuousAt rfl
    exact SmoothManifolds.CoveringStructure.extension_congr hh'
      (Eventually.of_forall fun z => e.apply_symm_apply z)
      (Eventually.of_forall fun _ => rfl)
  exact ⟨⟨e.toEquiv, hf, hg⟩, fun _ => rfl⟩

/-- The exponential is already a simply connected covering. Comparing it
with any universal covering gives a global smooth chart on that covering.
Completeness of its canonical pullback metric follows from the complete-base
covering theorem, independently of this comparison. -/
theorem universal_cover : P202Specs.Geometry.CartanHadamard.universal_coverType.{u} := by
  intro n M _ _ S g C hC R hR hK hc F hF E _ _ π hπ
  obtain ⟨_, _, T, hT, hTp, _, _⟩ := CoveringMetricCompleteness.canonical_geometry S g π hπ
  obtain ⟨h, hi, hpair, hhc⟩ := CoveringMetricCompleteness.covering_complete_connectedBase
    T S π hTp g hc
  have hh := (CoveringMetricCompleteness.connected_complete_iff h).mp hhc
  refine ⟨T, hT, hTp, ⟨h, hi, hpair, hh⟩, ?_⟩
  obtain ⟨p⟩ := (inferInstance : Nonempty M)
  obtain ⟨A⟩ := ExponentialPullbackComplete.affine_model_exists S p
  letI := A.topology
  letI := affine_simplyConnected A
  letI := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace A.manifold.topologicalManifold
  letI := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace T.topologicalManifold
  have hcov := (exponential_covering S g C hC R hR hK hc F hF p A).2
  obtain ⟨y, hy⟩ := hπ.1 (fiberExponential F p 0)
  obtain ⟨D, _⟩ := simplyConnected_cover_diffeomorphism A.manifold T S
    (fiberExponential F p) π hcov hTp 0 y hy
  let c : ModelChart n .euclidean E := D.toHomeomorph.symm.toOpenPartialHomeomorph.trans A.chart
  have hmem : c ∈ T.smoothStructure.val :=
    SmoothManifolds.transportAtlas_subset_of_maps T.smoothStructure.property
      D.toHomeomorph D.contDiff_toFun D.contDiff_invFun ⟨A.chart, A.chart_mem, rfl⟩
  have hs : c.source = univ := by
    ext z
    change (z ∈ univ ∧ D.toHomeomorph.symm z ∈ A.chart.source) ↔ z ∈ univ
    simp only [A.chart_source, mem_univ, and_self]
  have ht : c.target = univ := by
    have hAt := ExponentialPullbackComplete.affine_chart_target A
    ext z
    change (z ∈ A.chart.target ∧ A.chart.symm z ∈ univ) ↔ z ∈ univ
    simp only [hAt, mem_univ, and_self]
  obtain ⟨Q, _⟩ := diffeomorphism_of_global_chart T c hmem hs ht
  exact ⟨⟨c, hmem, hs, ht⟩, ⟨Q⟩⟩

end P202.Geometry.CartanHadamard
