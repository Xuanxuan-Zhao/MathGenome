import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricGeodesicCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GeodesicIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthDistance
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace P202.Geometry.MetricGeodesicCompleteness
open SmoothManifolds.AtlasData P202.ConnectionData P202.MetricData
  P202.LeviCivitaData P202.GeodesicData P202.CompletenessData
open Set Filter
open scoped Topology NNReal
universe u

abbrev LengthMetricComplete := @P202.CompletenessData.LengthMetricComplete

/-- The openness of the actual flow domain supplies a common short lifespan
for initial states near a phase cluster state. At a time sufficiently close
to b, that short lifespan reaches b. The exact lifespan translation law and
uniqueness identify this with the original maximal interval. -/
theorem time_mem_of_phase_cluster :
    P202Specs.Geometry.MetricGeodesicCompleteness.time_mem_of_phase_clusterType.{u} := by
  intro n M _ S C w I q hq b z hz
  obtain ⟨G, _hG, hbridge⟩ := GeodesicIVP.spray_exists S C
  obtain ⟨F, hF⟩ := SmoothManifolds.MaximalFlow.maximal_family_exists
    (phaseManifold S) (P202.MetricData.tangentStructure (phaseManifold S)) G
  have hqi := (GeodesicIVP.maximal_iff_integral C G hbridge w I q).mp hq
  have hsame := SmoothManifolds.IntegralCurves.maximal_unique
    (phaseManifold S) (P202.MetricData.tangentStructure (phaseManifold S))
    G w I (F.interval w) q (F.curve w) hqi (hF w)
  have hopen := (SmoothManifolds.MaximalFlow.domain_open_smooth
    (phaseManifold S) (P202.MetricData.tangentStructure (phaseManifold S))
    G F hF).1
  have hzero : (0, z) ∈ SmoothManifolds.MaximalFlowData.flowDomain F := (hF z).1
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (hopen.mem_nhds hzero)
  have htime : Tendsto (fun t : ℝ => b - t) (𝓝[I.carrier] b) (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := b)).sub (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ => t) (𝓝[I.carrier] b) (𝓝 b)))
  obtain ⟨t, htV, htU, htI⟩ :=
    ((hz.frequently hV).and_eventually ((htime.eventually hU).and self_mem_nhdsWithin)).exists
  have htD := hUV (show (b - t, q t) ∈ U ×ˢ V from ⟨htU, htV⟩)
  have htF : t ∈ (F.interval w).carrier := hsame.1 ▸ htI
  have hqt : q t = F.curve w t := hsame.2 htI
  have hlaw := (SmoothManifolds.MaximalFlow.lifespan_flow_law
    (phaseManifold S) (P202.MetricData.tangentStructure (phaseManifold S))
    G F hF w t htF).1
  have hbF : b ∈ (F.interval w).carrier := by
    change b - t ∈ (F.interval (q t)).carrier at htD
    rw [hqt, hlaw] at htD
    simpa using htD
  rwa [hsame.1]

/-- Closedness of the domain follows by excluding every finite boundary time.
Connectedness here is connectedness of the time axis, not an extra assumption
on the manifold. Upper and lower endpoints are treated simultaneously. -/
theorem global_of_phase_clusters :
    P202Specs.Geometry.MetricGeodesicCompleteness.global_of_phase_clustersType.{u} := by
  intro n M _ S C w I q hq hcluster
  have hclosed : IsClosed I.carrier := by
    apply isClosed_of_closure_subset
    intro b hb
    obtain ⟨z, hz⟩ := hcluster b hb
    exact time_mem_of_phase_cluster S C w I q hq b z hz
  exact (show IsClopen I.carrier from ⟨hclosed, I.isOpen⟩).eq_univ I.nonempty

/-- Arbitrary dimension and the zero initial vector are preserved. -/
theorem zero_velocity_global :
    P202Specs.Geometry.MetricGeodesicCompleteness.zero_velocity_globalType.{u} := by
  intro n M _ S C p I q hq
  have hu := GeodesicIVP.maximal_unique S C ⟨p, 0⟩ I
    D13Unified.OpenTimeInterval.whole q (constantCurve S p) hq
    (GeodesicIVP.zero_maximal S C p)
  exact hu

section MetricEstimates
open P202.CurveData P202.CurveConnectionData
open SmoothManifolds.ModelData SmoothManifolds.TangentData
open SmoothManifolds.BundleOperationsData
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The intrinsic velocity predicate used for connections agrees with the
one used for length when the parameter germ is an interior germ. -/
theorem geodesic_hasVelocityAt (C : Connection (tangentBundle S))
    {I : Set ℝ} {q : ℝ → Phase S} (hq : IsGeodesicOn S C I q)
    {t : ℝ} (ht : t ∈ I) :
    HasVelocityAt S (fun s => (q s).1) t (q t).2 := by
  obtain ⟨hc, e, he, hp, hd⟩ := (hq t ht).1
  exact ⟨(by simpa only [ContinuousWithinAt, ContinuousAt, nhdsWithin_univ] using hc), e, he, hp, hasDerivWithinAt_univ.mp hd⟩

/-- The geodesic equation gives C¹ coordinate germs on any closed subinterval
of the open solution interval, including the endpoints of that subinterval. -/
theorem geodesic_coordinateC1 (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) :
    CoordinateC1On S (fun s => (q s).1) I.carrier := by
  have hc : ContinuousOn (fun s => (q s).1) I.carrier :=
    fun t ht => (geodesic_hasVelocityAt C hq ht).1.continuousWithinAt
  intro t ht
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (q t).1
  let c : TangentIndex S := ⟨e, he⟩
  let J : Set ℝ := I.carrier ∩ (fun s => (q s).1) ⁻¹' e.source
  have hJ : IsOpen J := hc.isOpen_inter_preimage I.isOpen e.open_source
  have hd (s : ℝ) (hs : s ∈ J) :
      HasDerivAt (fun r => (e (q r).1).val) (chartVelocity S c q s) s ∧
      DifferentiableAt ℝ (chartVelocity S c q) s := by
    have hps : (q s).1 ∈ (tangentBundle S).baseSet c := by
      rw [(tangentRealization S).baseSet]; exact hs.2
    have h := GeodesicIVP.geodesic_coordinate_equation C hq hs.1 c hps
    exact ⟨h.1, h.2.differentiableAt⟩
  have hC1 : ContDiffOn ℝ 1 (fun s => (e (q s).1).val) J := by
    rw [contDiffOn_one_iff_derivWithin hJ.uniqueDiffOn]
    refine ⟨fun s hs => (hd s hs).1.differentiableAt.differentiableWithinAt, ?_⟩
    apply ContinuousOn.congr (fun s hs => (hd s hs).2.continuousAt.continuousWithinAt)
    intro s hs
    exact (hd s hs).1.hasDerivWithinAt.derivWithin (hJ.uniqueDiffOn s hs)
  exact ⟨e, he, hp, (fun s => (e (q s).1).val),
    hC1.contDiffAt (hJ.mem_nhds ⟨ht, hp⟩), rfl, Filter.EventuallyEq.rfl⟩

/-- A compact subarc is an admissible curve for the original length infimum.
It has exactly constant speed, with no normalization or division by that speed. -/
theorem geodesic_segment_length (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a ≤ b) (ha : a ∈ I.carrier) (hb : b ∈ I.carrier) :
    ∃ c : PiecewiseC1Curve S a b, (∀ t, c t = (q t).1) ∧
      length g c = (b - a) * tangentNorm g (q a).1 (q a).2 := by
  have hsub : Icc a b ⊆ I.carrier := I.ordConnected.out ha hb
  let c : PiecewiseC1Curve S a b := {
    ordered := hab
    toFun := fun t => (q t).1
    continuousOn := fun t ht =>
      (geodesic_hasVelocityAt C hq (hsub ht)).1.continuousWithinAt
    pieces := 1
    node := ![a, b]
    monotone_node := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    first_node := rfl
    last_node := rfl
    regular := by
      intro i
      fin_cases i
      intro t ht
      have htt : t ∈ Icc a b := by simpa using ht
      obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := geodesic_coordinateC1 C I q hq t (hsub htt)
      refine ⟨e, he, hp, x, hx, hxt, ?_⟩
      apply heq.filter_mono
      apply nhdsWithin_mono
      simpa using hsub }
  refine ⟨c, fun _ => rfl, ?_⟩
  change (∫ t in a..b, speed g (fun s => (q s).1) t) = _
  have heq : EqOn (speed g (fun s => (q s).1))
      (fun _ => tangentNorm g (q a).1 (q a).2) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro t ht
    rw [speed, PiecewiseCurves.velocity_eq (geodesic_hasVelocityAt C hq (hsub ht))]
    exact GeodesicIVP.constant_speed S g C hC I q hq t (hsub ht) a ha
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const, smul_eq_mul]

/-- Distance along a geodesic is bounded by its speed times elapsed time. -/
theorem geodesic_dist_le {d : MetricSpace M}
    (g : RiemannianMetric S)
    (hd : ∀ p r : M, @dist M d.toDist p r = sInf (P202.DistanceData.pathLengths g p r))
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (hzero : 0 ∈ I.carrier)
    {a b : ℝ} (ha : a ∈ I.carrier) (hb : b ∈ I.carrier) :
    @dist M d.toDist (q a).1 (q b).1 ≤
      tangentNorm g (q 0).1 (q 0).2 * |b - a| := by
  have forward {a b : ℝ} (ha : a ∈ I.carrier) (hb : b ∈ I.carrier) (hab : a ≤ b) :
      @dist M d.toDist (q a).1 (q b).1 ≤
        tangentNorm g (q 0).1 (q 0).2 * (b - a) := by
    obtain ⟨c, hc, hlen⟩ := geodesic_segment_length g C hC I q hq hab ha hb
    rw [hd]
    have hle := csInf_le (LengthDistance.pathLengths_bddBelow g (q a).1 (q b).1)
      (show length g c ∈ P202.DistanceData.pathLengths g (q a).1 (q b).1 from
        ⟨a, b, c, hc a, hc b, rfl⟩)
    rw [hlen, GeodesicIVP.constant_speed S g C hC I q hq a ha 0 hzero] at hle
    simpa only [mul_comm] using hle
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using forward ha hb hab
  · rw [@dist_comm M d.toPseudoMetricSpace (q a).1 (q b).1, abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact forward hb ha hba

end MetricEstimates

section ClusterEstimates
open SmoothManifolds.ModelData SmoothManifolds.TangentData
open SmoothManifolds.BundleOperationsData

/-- A convergent coordinate and a clustering coordinate cluster jointly, even
when they are evaluated along the same filter. -/
theorem cluster_prod_of_tendsto {A B T : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {l : Filter T} {f : T → A} {h : T → B} {a : A} {b : B}
    (hf : Tendsto f l (𝓝 a)) (hh : MapClusterPt b l h) :
    MapClusterPt (a, b) l (fun t => (f t, h t)) := by
  rw [mapClusterPt_iff_frequently]
  intro W hW
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hW
  exact ((hh.frequently hV).and_eventually (hf.eventually hU)).mono
    (fun t ht => hUV ⟨ht.2, ht.1⟩)

/-- A Lipschitz curve into a complete metric space has a position limit at
any finite closure time of its domain. -/
theorem position_limit_of_lipschitz {X : Type*} [MetricSpace X] [CompleteSpace X]
    {f : ℝ → X} {J : Set ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f J)
    {b : ℝ} (hb : b ∈ closure J) : ∃ p : X, Tendsto f (𝓝[J] b) (𝓝 p) := by
  letI : NeBot (𝓝[J] b) := mem_closure_iff_nhdsWithin_neBot.mp hb
  have hc : Cauchy (𝓝[J] b) := cauchy_nhds.mono nhdsWithin_le_nhds
  exact cauchy_map_iff_exists_tendsto.mp
    (hc.map_of_le hf.uniformContinuousOn (by exact inf_le_right))

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- A position limit and bounded intrinsic velocity give a cluster state in
the actual tangent bundle. Only a finite-dimensional coordinate ball in the
fiber is compact; neither M nor its whole tangent bundle is assumed compact. -/
theorem phase_cluster_of_position_limit (g : RiemannianMetric S)
    {l : Filter ℝ} [NeBot l] {q : ℝ → Phase S} {p : M}
    (hp : Tendsto (fun t => (q t).1) l (𝓝 p))
    {K : ℝ} (hK : ∀ᶠ t in l, tangentNorm g (q t).1 (q t).2 ≤ K) :
    ∃ z : Phase S, MapClusterPt z l q := by
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  let c : TangentIndex S := ⟨e, he⟩
  obtain ⟨B, hB, V, hV, hpV, hVe, hbound⟩ :=
    LocalCurveTrapping.local_coordinate_bound g c p hpe
  have hstay : ∀ᶠ t in l, (q t).1 ∈ V := hp.eventually (hV.mem_nhds hpV)
  have hvel : ∀ᶠ t in l, chartVelocity S c q t ∈ Metric.closedBall 0 (B * K) := by
    filter_upwards [hstay, hK] with t ht hKt
    rw [Metric.mem_closedBall, dist_zero_right, GeodesicIVP.chartVelocity_eq c q t (hVe ht)]
    exact (hbound (q t).1 (hVe ht) (q t).2 ht).trans (mul_le_mul_of_nonneg_left hKt hB.le)
  obtain ⟨v, _hv, hv⟩ := (isCompact_closedBall (0 : Euclidean n) (B * K)).exists_mapClusterPt
    (Filter.tendsto_principal.mpr hvel)
  have hx : Tendsto (fun t => (e (q t).1).val) l (𝓝 (e p).val) :=
    ((continuous_subtype_val.continuousAt.comp (e.continuousAt hpe)).tendsto).comp hp
  have hpair := cluster_prod_of_tendsto hx hv
  let T := tangentStructure S
  let E := T.chart e he
  let H : Euclidean n × Euclidean n → ModelSpace (n + n) .euclidean :=
    fun w => T.productCoordinates.homeomorph
      (⟨w.1, by trivial⟩, ⟨w.2, by trivial⟩)
  have hH : Continuous H := T.productCoordinates.homeomorph.continuous.comp
    ((continuous_fst.subtype_mk _).prodMk (continuous_snd.subtype_mk _))
  have htarget : H ((e p).val, v) ∈ E.target := by
    rw [T.chart_target]
    exact ⟨(e p, ⟨v, by trivial⟩), ⟨e.map_source hpe, mem_univ _⟩, rfl⟩
  have hcluster := hpair.continuousAt_comp
    ((E.continuousAt_symm htarget).comp hH.continuousAt)
  refine ⟨E.symm (H ((e p).val, v)), ?_⟩
  apply hcluster.congrFun
  filter_upwards [hstay] with t ht
  change E.symm (H ((e (q t).1).val, chartVelocity S c q t)) = q t
  have hsource : q t ∈ E.source := by
    rw [T.chart_source]
    exact hVe ht
  have hchart : H ((e (q t).1).val, chartVelocity S c q t) = E (q t) := by
    apply Subtype.ext
    rw [T.chart_apply e he (q t) (hVe ht), GeodesicIVP.chartVelocity_eq c q t (hVe ht)]
    rfl
  rw [hchart, E.left_inv hsource]

end ClusterEstimates

/-- Metric completeness gives a position limit at every finite closure time;
finite-dimensional compactness supplies a phase cluster state; the actual
geodesic flow then rules out all finite boundary times. -/
theorem metric_complete_geodesically_complete :
    P202Specs.Geometry.MetricGeodesicCompleteness.metric_complete_geodesically_completeType.{u} := by
  intro n M inst _ S g C hC hcomplete w I q hq
  obtain ⟨d, htop, hd, hcomp⟩ := hcomplete
  let d' : MetricSpace M := d.replaceTopology htop.symm
  letI : MetricSpace M := d'
  letI : CompleteSpace M := by
    change @CompleteSpace M d'.toUniformSpace
    rw [show d' = d from MetricSpace.replaceTopology_eq d htop.symm]
    exact hcomp
  have hd' : ∀ p r : M, dist p r = sInf (P202.DistanceData.pathLengths g p r) := hd
  let K : ℝ≥0 := ⟨tangentNorm g (q 0).1 (q 0).2,
    SmoothMetrics.tangentNorm_nonneg g (q 0).1 (q 0).2⟩
  have hLip : LipschitzOnWith K (fun t => (q t).1) I.carrier := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have h := geodesic_dist_le (d := d') g hd' C hC I q hq.2.2.1 hq.1 ha hb
    change dist (q a).1 (q b).1 ≤ tangentNorm g (q 0).1 (q 0).2 * dist a b
    simpa only [Real.dist_eq, abs_sub_comm] using h
  apply global_of_phase_clusters S C w I q hq
  intro b hb
  obtain ⟨p, hp⟩ := position_limit_of_lipschitz hLip hb
  letI : NeBot (𝓝[I.carrier] b) := mem_closure_iff_nhdsWithin_neBot.mp hb
  apply phase_cluster_of_position_limit g hp (K := (K : ℝ))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (GeodesicIVP.constant_speed S g C hC I q hq.2.2.1 t ht 0 hq.1).le

/-- After continuation, the complete position and velocity have a limit in
TM at every real time, with its canonical topology. This states the full
state conclusion, without any completeness assumption on a tangent norm. -/
theorem metric_complete_phase_limit
    {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (hcomplete : LengthMetricComplete g)
    (w : Phase S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsMaximalThrough S C w I q) (b : ℝ) :
    Tendsto q (𝓝[I.carrier] b) (𝓝 (q b)) := by
  have hglobal := metric_complete_geodesically_complete S g C hC hcomplete w I q hq
  obtain ⟨G, _hG, hbridge⟩ := GeodesicIVP.spray_exists S C
  have hc := ((hbridge I q).mpr hq.2.2.1).1
  exact hc b (hglobal ▸ mem_univ b)

end P202.Geometry.MetricGeodesicCompleteness
