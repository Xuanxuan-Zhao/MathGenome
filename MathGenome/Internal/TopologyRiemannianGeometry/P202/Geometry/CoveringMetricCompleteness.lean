import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CoveringMetricCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MetricFoundation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CoveringLifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.MetricSpace.Isometry
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.CoveringStructure

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace P202.Geometry.CoveringMetricCompleteness
open SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.CoveringData P202.MetricData P202.CoveringMetricData
open Set Filter
open scoped _root_.Topology
universe u

abbrev SmoothCovering := @P202.CoveringMetricData.SmoothCovering
abbrev ComponentwiseComplete := @P202.CoveringMetricData.ComponentwiseComplete

/-- Transport a complete metric through a homeomorphism while retaining the
specified topology and the exact distance function. -/
private theorem transport_complete_metric {X Y : Type u}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (e : X ≃ₜ Y) (d : MetricSpace Y)
    (htop : d.toUniformSpace.toTopologicalSpace = tY)
    (hc : @CompleteSpace Y d.toUniformSpace) :
    ∃ dX : MetricSpace X, dX.toUniformSpace.toTopologicalSpace = tX ∧
      (∀ x y, @dist X dX.toDist x y = @dist Y d.toDist (e x) (e y)) ∧
      @CompleteSpace X dX.toUniformSpace := by
  let dY := d.replaceTopology htop.symm
  have hdY : dY = d := MetricSpace.replaceTopology_eq d htop.symm
  letI : MetricSpace Y := dY
  have hcy : @CompleteSpace Y dY.toUniformSpace := by rw [hdY]; exact hc
  letI : CompleteSpace Y := hcy
  let dX : MetricSpace X := e.isEmbedding.comapMetricSpace e
  letI : MetricSpace X := dX
  have hi : Isometry e := Isometry.of_dist_eq fun _ _ => rfl
  exact ⟨dX, rfl, fun _ _ => rfl,
    (hi.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance⟩

/-- A connected component is the whole space when the space is connected. -/
private def componentHomeomorph {M : Type u} [TopologicalSpace M]
    [ConnectedSpace M] (o : M) : connectedComponent o ≃ₜ M where
  toFun := Subtype.val
  invFun := fun p => ⟨p, by rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

theorem connected_complete_iff :
    P202Specs.Geometry.CoveringMetricCompleteness.connected_complete_iffType.{u} := by
  intro n M _ _ S g
  constructor
  · intro h
    obtain ⟨o⟩ := (inferInstance : Nonempty M)
    obtain ⟨d, ht, hd, hc⟩ := h o
    let e := componentHomeomorph o
    obtain ⟨dM, htM, hdM, hcM⟩ := transport_complete_metric e.symm d ht hc
    refine ⟨dM, htM, ?_, hcM⟩
    intro p q
    exact (hdM p q).trans (hd (e.symm p) (e.symm q))
  · rintro ⟨d, ht, hd, hc⟩ o
    let e := componentHomeomorph o
    obtain ⟨dC, htC, hdC, hcC⟩ := transport_complete_metric e d ht hc
    exact ⟨dC, htC, fun p q => (hdC p q).trans (hd p.val q.val), hcC⟩

section Branches
variable {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  (T : SmoothManifold n .euclidean E) (S : SmoothManifold n .euclidean B)
  (p : E → B)

/-- Every smooth branch supplies an actual smooth inverse germ. -/
theorem localDiffeomorphism_of_smoothBranches (hp : IsSmoothCovering T S p) :
    SmoothManifolds.TensorData.IsLocalDiffeomorphism T S p := by
  refine ⟨hp.2.1, fun x => ?_⟩
  obtain ⟨q, hx, heq⟩ := hp.1.isLocalHomeomorph x
  have hq : EqOn q p q.source := fun z _ => congrFun heq.symm z
  have hpxt : p x ∈ q.target := by rw [heq]; exact q.map_source hx
  refine ⟨q.symm, hp.2.2 q hq (p x) hpxt, ?_, ?_, ?_⟩
  · rw [heq]; exact q.left_inv hx
  · filter_upwards [q.open_source.mem_nhds hx] with z hz
    change q.symm (p z) = z
    rw [heq]; exact q.left_inv hz
  · filter_upwards [q.open_target.mem_nhds hpxt] with z hz
    change p (q.symm z) = z
    rw [heq]; exact q.right_inv hz

/-- A local inverse germ agrees with any topological covering branch inverse
near its center, so every branch inverse is smooth on its entire target. -/
theorem smoothBranches_of_localDiffeomorphism
    (hc : IsCoveringMap p)
    (hp : SmoothManifolds.TensorData.IsLocalDiffeomorphism T S p) :
    IsSmoothCovering T S p := by
  refine ⟨hc, hp.1, ?_⟩
  intro q hq y hy
  have he : q.symm y ∈ q.source := q.map_target hy
  have hpy : p (q.symm y) = y := (hq he).symm.trans (q.right_inv hy)
  obtain ⟨f, hf, hfe, hfp, hpf⟩ := hp.2 (q.symm y)
  rw [hpy] at hf hfe hpf
  apply SmoothManifolds.manifoldContDiffAt_congr hf
  have hcont : ContinuousAt q.symm y := q.continuousAt_symm hy
  have hnear := hcont.preimage_mem_nhds hfp
  filter_upwards [hnear, q.open_target.mem_nhds hy] with z hz hzt
  change f (p (q.symm z)) = q.symm z at hz
  have hpz : p (q.symm z) = z :=
    (hq (q.map_target hzt)).symm.trans (q.right_inv hzt)
  simpa only [hpz] using hz

end Branches

theorem smoothCovering_iff_branches :
    P202Specs.Geometry.CoveringMetricCompleteness.smoothCovering_iff_branchesType.{u} := by
  intro n E B _ _ T S p
  constructor
  · rintro ⟨hc, hd⟩
    have hb := (P202.Topology.coveringBridge E B p).mp hc
    exact ⟨hb.2, smoothBranches_of_localDiffeomorphism T S p hb.1 hd⟩
  · rintro ⟨hs, hb⟩
    exact ⟨(P202.Topology.coveringBridge E B p).mpr ⟨hb.1, hs⟩,
      localDiffeomorphism_of_smoothBranches T S p hb⟩

theorem pullback_metric :
    P202Specs.Geometry.CoveringMetricCompleteness.pullback_metricType.{u} := by
  intro n E B _ _ T S p hp g
  let L := SmoothManifolds.differential T S p hp.2.1
  have hL := SmoothManifolds.differential_spec T S p hp.2.1
  let i : SmoothImmersion T S p :=
    ⟨hp.2.1, L, hL, fun x =>
      (SmoothManifolds.Tensors.differential_bijective_of_localDiffeomorphism
        T S p hp.2 x).1⟩
  obtain ⟨h, heq⟩ := P202.Geometry.MetricFoundation.pullback_metric T S p i g
  exact ⟨h, ⟨hp.2, L, hL, fun x v w => (heq x v w).symm⟩, heq⟩

theorem smooth_structure_agreement :
    P202Specs.Geometry.CoveringMetricCompleteness.smooth_structure_agreementType.{u} := by
  intro n E B _ _ T T' S p hp hp'
  exact SmoothManifolds.CoveringStructure.smooth_covering_unique T T' S p
    ((smoothCovering_iff_branches T S p).mp hp).2
    ((smoothCovering_iff_branches T' S p).mp hp').2

theorem covering_hausdorff :
    P202Specs.Geometry.CoveringMetricCompleteness.covering_hausdorffType.{u} := by
  intro n E B _ _ S p hp
  exact SmoothManifolds.CoveringTopology.hausdorff S.topologicalManifold p
    ((P202.Topology.coveringBridge E B p).mp hp).1

theorem canonical_geometry :
    P202Specs.Geometry.CoveringMetricCompleteness.canonical_geometryType.{u} := by
  intro n E B _ _ _ S g p hp
  have hc := (P202.Topology.coveringBridge E B p).mp hp
  obtain ⟨T, hA, hT, _, hu⟩ :=
    SmoothManifolds.CoveringStructure.exists_canonical_smooth_covering S p hc.1
      (Or.inr inferInstance)
  have hcover : SmoothCovering T S p :=
    (smoothCovering_iff_branches T S p).mpr ⟨hc.2, hT⟩
  obtain ⟨h, hh, _⟩ := pullback_metric T S p hcover g
  exact ⟨covering_hausdorff S p hp,
    SmoothManifolds.CoveringTopology.secondCountable_of_preconnected
      S.topologicalManifold p hc.1,
    T, hA, hcover, ⟨h, hh⟩,
    fun T' hT' => hu T' ((smoothCovering_iff_branches T' S p).mp hT').2⟩

/-- Use the simply connected real parameter line to avoid gluing an infinite
sequence of compact-interval lifts. -/
theorem real_path_lifting :
    P202Specs.Geometry.CoveringMetricCompleteness.real_path_liftingType.{u} := by
  intro E B _ _ p hp γ e he
  have hc := ((P202.Topology.coveringBridge E B p).mp hp).1
  obtain ⟨L, hL, hu⟩ := hc.existsUnique_continuousMap_lifts γ 0 e he
  refine ⟨L, ⟨hL.1, fun t => congrFun hL.2 t⟩, ?_⟩
  intro K hK
  exact hu K ⟨hK.1, funext hK.2⟩

section LengthCompleteness
open P202.CurveData P202.DistanceData
variable {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  {T : SmoothManifold n .euclidean E} {S : SmoothManifold n .euclidean B}

/-- Projection contracts the original component length distances. -/
theorem componentDistance_projection (h : RiemannianMetric T) (g : RiemannianMetric S)
    (p : E → B) (hi : IsLocalIsometry h g p) (o : E)
    (F : connectedComponent o → connectedComponent (p o))
    (hF : ∀ x, (F x).val = p x.val) (x y : connectedComponent o) :
    componentDistance g (p o) (F x) (F y) ≤ componentDistance h o x y := by
  apply le_csInf (LengthDistance.component_finite h o x y).1
  rintro L ⟨a, b, c, hx, hy, rfl⟩
  obtain ⟨d, hd, hlen⟩ := MetricFoundation.localIsometry_length_exists h g p hi c
  rw [← hlen]
  apply LengthDistance.componentDistance_le_length g (p o) (F x) (F y) d
  · rw [hd, hx, hF]
  · rw [hd, hy, hF]

/-- Every prefix has length bounded by the length of the whole curve. -/
theorem prefix_length_le {a b : ℝ} (c : PiecewiseC1Curve T a b)
    (h : RiemannianMetric T) {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ d : PiecewiseC1Curve T a t, (∀ s, d s = c s) ∧ length h d ≤ length h c := by
  obtain ⟨d, hd, _⟩ := MetricFoundation.restriction_exists c a t le_rfl ht.1 ht.2
  refine ⟨d, hd, ?_⟩
  have hf : (d : ℝ → E) = c := funext hd
  change (∫ s in a..t, speed h d s) ≤ ∫ s in a..b, speed h c s
  rw [hf]
  exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (.of_forall fun s => P202.Geometry.SmoothMetrics.tangentNorm_nonneg h (c s) _)
    (MetricFoundation.speed_integrable h c)

/-- A continuous curve whose projection remains in one branch target cannot
change sheets. This uses uniqueness of lifts on the connected parameter interval. -/
theorem curve_in_sheet (p : E → B) (hp : IsCoveringMap p)
    (q : OpenPartialHomeomorph E B) (hq : EqOn q p q.source)
    {a b : ℝ} (c : PiecewiseC1Curve T a b)
    (ha : c a ∈ q.source) (hc : ∀ t ∈ Icc a b, p (c t) ∈ q.target) :
    ∀ t ∈ Icc a b, c t = q.symm (p (c t)) := by
  have hproj : ∀ t ∈ Icc a b, p (q.symm (p (c t))) = p (c t) := by
    intro t ht
    exact (hq (q.map_target (hc t ht))).symm.trans (q.right_inv (hc t ht))
  have hcont : ContinuousOn (fun t => q.symm (p (c t))) (Icc a b) :=
    q.continuousOn_symm.comp (hp.continuous.comp_continuousOn c.continuousOn) hc
  exact hp.eqOn_of_comp_eqOn isPreconnected_Icc c.continuousOn hcont
    (fun t ht => (hproj t ht).symm) (left_mem_Icc.mpr c.ordered)
    (by rw [← hq ha]; exact (q.left_inv ha).symm)

/-- Completeness is transferred directly by Cauchy sequences. Short curves
between late terms cannot leave an evenly covered neighborhood of the base
limit; uniqueness of lifts then puts the entire tail in one fixed sheet. -/
theorem componentwiseComplete_of_covering
    (h : RiemannianMetric T) (g : RiemannianMetric S) (p : E → B)
    (hp : P202Specs.Topology.Covering p) (hi : IsLocalIsometry h g p)
    (hg : ComponentwiseComplete g) : ComponentwiseComplete h := by
  intro o
  obtain ⟨dE, htE, hdE⟩ := LengthDistance.component_metric h o
  obtain ⟨dB, htB, hdB, hcB⟩ := hg (p o)
  let mE := dE.replaceTopology htE.symm
  let mB := dB.replaceTopology htB.symm
  have hmB : mB = dB := MetricSpace.replaceTopology_eq dB htB.symm
  letI : MetricSpace (connectedComponent o) := mE
  letI : MetricSpace (connectedComponent (p o)) := mB
  have hdistE (x y : connectedComponent o) : dist x y = componentDistance h o x y := hdE x y
  have hdistB (x y : connectedComponent (p o)) :
      dist x y = componentDistance g (p o) x y := hdB x y
  letI : CompleteSpace (connectedComponent (p o)) := by
    change @CompleteSpace _ mB.toUniformSpace
    rw [hmB]
    exact hcB
  have hcover := ((P202.Topology.coveringBridge E B p).mp hp).1
  let F : connectedComponent o → connectedComponent (p o) :=
    fun x => ⟨p x.val, hcover.continuous.mapsTo_connectedComponent o x.property⟩
  have hF (x : connectedComponent o) : (F x).val = p x.val := rfl
  have hLip : LipschitzWith 1 F := LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [hdistE, hdistB, NNReal.coe_one, one_mul] using
      componentDistance_projection h g p hi o F hF x y
  refine ⟨mE, rfl, hdistE, Metric.complete_of_cauchySeq_tendsto ?_⟩
  intro u hu
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete (hLip.uniformContinuous.comp_cauchySeq hu)
  obtain ⟨U, hbU, hU, sheets, _hdisj, hsheets⟩ := hp.2 b.val
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((hU.preimage continuous_subtype_val).mem_nhds hbU)
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.mp hu (δ / 2) (half_pos hδ)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hb (δ / 2) (half_pos hδ)
  let N := max N₁ N₂
  have hNN₁ : N₁ ≤ N := le_max_left _ _
  have hNN₂ : N₂ ≤ N := le_max_right _ _
  have hNu : p (u N).val ∈ U :=
    hball (lt_trans (hN₂ N hNN₂) (half_lt_self hδ))
  have hmem : (u N).val ∈ ⋃ s ∈ sheets, s.chart.source := by
    rw [hsheets]
    exact hNu
  obtain ⟨s, _hs, hsN⟩ := mem_iUnion₂.mp hmem
  let q := s.chart
  have hq : EqOn q p q.source := fun x _ => congrFun s.projection x
  have htail : ∀ k ≥ N, (u k).val = q.symm (p (u k).val) := by
    intro k hk
    have hnear : componentDistance h o (u N) (u k) < δ / 2 := by
      rw [← hdistE]
      exact hN₁ N hNN₁ k (le_trans hNN₁ hk)
    obtain ⟨a, z, c, hca, hcz, hlen⟩ :=
      (LengthDistance.componentDistance_lt_iff h o (u N) (u k) (δ / 2)).mp hnear
    have hstay : ∀ t ∈ Icc a z, p (c t) ∈ q.target := by
      intro t ht
      obtain ⟨d, hd, hdlen⟩ := prefix_length_le c h ht
      have hct : c t ∈ connectedComponent o := by
        have hcpath : HasPiecewiseC1Path T (u N).val (c t) :=
          ⟨a, t, d, (hd a).trans hca, hd t⟩
        rw [connectedComponent_eq (u N).property]
        exact LengthDistance.path_mem_component hcpath
      let x : connectedComponent o := ⟨c t, hct⟩
      have hdx : dist (F (u N)) (F x) ≤ length h c := by
        rw [hdistB]
        apply le_trans (componentDistance_projection h g p hi o F hF (u N) x)
        exact (LengthDistance.componentDistance_le_length h o (u N) x d
          ((hd a).trans hca) (hd t)).trans hdlen
      have hxb : dist (F x) b < δ := by
        calc
          dist (F x) b ≤ dist (F x) (F (u N)) + dist (F (u N)) b := dist_triangle _ _ _
          _ = dist (F (u N)) (F x) + dist (F (u N)) b := by rw [dist_comm (F x)]
          _ < δ := by
            have hbase : dist (F (u N)) b < δ / 2 := hN₂ N hNN₂
            linarith
      have hxU : p (c t) ∈ U := hball hxb
      simpa only [q, s.target_eq] using hxU
    have hcN : c a ∈ q.source := hca ▸ hsN
    have heq := curve_in_sheet p hcover q hq c hcN hstay z ⟨c.ordered, le_rfl⟩
    simpa only [hcz] using heq
  have hpb : Tendsto (fun k => p (u k).val) atTop (𝓝 b.val) :=
    continuous_subtype_val.tendsto b |>.comp hb
  have hqb : b.val ∈ q.target := by simpa only [q, s.target_eq] using hbU
  have hlim : Tendsto (fun k => (u k).val) atTop (𝓝 (q.symm b.val)) := by
    apply (q.continuousAt_symm hqb |>.tendsto.comp hpb).congr'
    exact (eventually_ge_atTop N).mono fun k hk => (htail k hk).symm
  have hecomp : q.symm b.val ∈ connectedComponent o :=
    isClosed_connectedComponent.mem_of_tendsto hlim (.of_forall fun k => (u k).property)
  exact ⟨⟨q.symm b.val, hecomp⟩, tendsto_subtype_rng.mpr hlim⟩

end LengthCompleteness

/-- The pullback metric of a smooth covering of a componentwise complete base
is complete on every connected component of the total space. -/
theorem covering_complete :
    P202Specs.Geometry.CoveringMetricCompleteness.covering_completeType.{u} := by
  intro n E B _ _ T S p hp g hg
  obtain ⟨h, hi, hformula⟩ := pullback_metric T S p hp g
  exact ⟨h, hi, hformula, componentwiseComplete_of_covering h g p hp.1 hi hg⟩

/-- The usual connected-base version still allows disconnected total spaces. -/
theorem covering_complete_connectedBase :
    P202Specs.Geometry.CoveringMetricCompleteness.covering_complete_connectedBaseType.{u} := by
  intro n E B _ _ _ T S p hp g hg
  exact covering_complete T S p hp g ((connected_complete_iff g).mpr hg)

/-- The canonical smooth structure on a connected topological cover carries
the complete pullback metric on the original topology. -/
theorem canonical_complete_geometry :
    P202Specs.Geometry.CoveringMetricCompleteness.canonical_complete_geometryType.{u} := by
  intro n E B _ _ _ S g p hp hg
  obtain ⟨_, _, T, hA, hT, _, _⟩ := canonical_geometry S g p hp
  obtain ⟨h, hi, _, hh⟩ := covering_complete T S p hT g hg
  exact ⟨T, hA, hT, h, hi, hh⟩

end P202.Geometry.CoveringMetricCompleteness
