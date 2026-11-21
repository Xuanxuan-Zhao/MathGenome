import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialPullbackComplete
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.NonpositiveJacobiGrowth
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace P202.Geometry.ExponentialPullbackComplete
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.ExponentialData P202.ExponentialJacobiData P202.NonpositiveJacobiData
  P202.CompletenessData P202.ExponentialPullbackData
open Set Filter
open scoped Topology SmoothManifolds.BoundaryConeData
universe u

/-- Evaluate the arbitrary-speed Jacobi estimate at time one. This proves the
full differential estimate without a radial/angular decomposition and includes
the zero base vector and the zero-dimensional tangent fiber. -/
theorem differential_expands :
    P202Specs.Geometry.ExponentialPullbackComplete.differential_expandsType.{u} := by
  intro n M _ S g C hC R hR hK F hF p v hv w
  obtain ⟨J, hJ, hJ0, hJd, hformula, _⟩ :=
    ExponentialJacobi.radial_field S g C hC R hR F hF p v w
  have hgrowth := (NonpositiveJacobiGrowth.growth S g C hC R hR hK
    (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩) (hF ⟨p, v⟩).2.2.1
    (hF ⟨p, v⟩).1 J hJ hJ0 _ hJd).1 1 hv (by norm_num)
  have hinit : tangentNorm g (F.curve ⟨p, v⟩ 0).1
      (initialIdentification S C F hF p v w) = tangentNorm g p w := by
    have hbase : p = (F.curve ⟨p, v⟩ 0).1 :=
      (congrArg Sigma.fst (hF ⟨p, v⟩).2.1).symm
    change tangentNorm g _ (castTangent S hbase w) = _
    have hcast (a b : M) (hab : a = b) (x : TangentSpace S a) :
        tangentNorm g b (castTangent S hab x) = tangentNorm g a x := by
      cases hab
      rfl
    exact hcast p _ hbase w
  have hend : tangentNorm g (F.curve ⟨p, v⟩ 1).1 (J 1) =
      tangentNorm g (fiberExponential F p v) (fiberDifferential S F p v w) := by
    have heq := hformula 1 hv
    have hphase : (⟨(F.curve ⟨p, v⟩ 1).1, J 1⟩ : Phase S) =
        ⟨fiberExponential F p v, fiberDifferential S F p v w⟩ :=
      Sigma.ext rfl (by
        have hstep : HEq (J 1) (fiberDifferential S F p ((1 : ℝ) • v) w) := by
          simpa only [one_smul] using heq
        have hdiff (a b : TangentSpace S p) (hab : a = b) :
            HEq (fiberDifferential S F p a w) (fiberDifferential S F p b w) := by
          cases hab
          rfl
        exact hstep.trans (hdiff _ _ (one_smul ℝ v)))
    exact congrArg (fun z : Phase S => tangentNorm g z.1 z.2) hphase
  simpa only [one_mul, hinit, hend] using hgrowth

/-- Every intrinsic tangent fiber has its ordinary linear smooth structure.
The topology is induced by a genuine linear equivalence, hence is the usual
finite-dimensional topology; the chart is global even in dimension zero. -/
theorem affine_model_exists :
    P202Specs.Geometry.ExponentialPullbackComplete.affine_model_existsType.{u} := by
  intro n M _ S p
  let E := selectedCoordinates S p
  letI : TopologicalSpace (TangentSpace S p) := TopologicalSpace.induced E inferInstance
  let e : TangentSpace S p ≃ₜ Euclidean n :=
    E.toEquiv.toHomeomorphOfIsInducing (Topology.IsInducing.induced E)
  let c : ModelChart n .euclidean (TangentSpace S p) :=
    (e.trans (Homeomorph.Set.univ (Euclidean n)).symm).toOpenPartialHomeomorph
  have hc : IsContDiffAtlas (⊤ : ℕ∞) {c} := by
    refine ⟨fun v => ⟨c, rfl, mem_univ v⟩, ?_⟩
    rintro d rfl f rfl
    exact SmoothManifolds.LieBrackets.fullChart_compatible_self c
  let T : SmoothManifold n .euclidean (TangentSpace S p) := {
    topologicalManifold := {
      hausdorff := e.symm.t2Space
      secondCountable := e.secondCountableTopology
      atlas := {c}
      covers := hc.1 }
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) {c},
      SmoothManifolds.maximalExtension_isMaximal hc⟩ }
  exact ⟨{
    coordinates := E
    topology := inferInstance
    manifold := T
    chart := c
    chart_mem := SmoothManifolds.subset_maximalExtension hc rfl
    chart_source := rfl
    chart_value := fun _ => rfl }⟩

/-- A dominating metric with the same topology as a complete metric is complete.
Equality of topologies is essential; norm domination alone does not suffice. -/
theorem complete_of_dominates_same_topology {X : Type*}
    (d₀ d₁ : MetricSpace X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (htop : d₁.toUniformSpace.toTopologicalSpace = d₀.toUniformSpace.toTopologicalSpace)
    (hdom : ∀ x y, @dist X d₀.toDist x y ≤ @dist X d₁.toDist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  letI := d₁
  apply Metric.complete_of_cauchySeq_tendsto
  intro s hs
  have hs₀ : @CauchySeq X ℕ d₀.toUniformSpace _ s := by
    rw [@Metric.cauchySeq_iff X ℕ d₀.toPseudoMetricSpace _ _]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hs ε hε
    exact ⟨N, fun m hm n hn => lt_of_le_of_lt (hdom (s m) (s n)) (hN m hm n hn)⟩
  have hlimit : ∃ x, @Tendsto ℕ X s atTop
      (@nhds X d₀.toUniformSpace.toTopologicalSpace x) := by
    letI := d₀
    letI := hcomplete
    exact cauchySeq_tendsto_of_complete hs₀
  obtain ⟨x, hx⟩ := hlimit
  refine ⟨x, ?_⟩
  change Tendsto s atTop (@nhds X d₁.toUniformSpace.toTopologicalSpace x)
  rw [htop]
  exact hx

open SmoothManifolds.BundleOperationsData P202.CurveData P202.DistanceData

section Analytic
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {p : M}

/-- A global linear chart has full target as well as full source. -/
theorem affine_chart_target (A : AffineFiberModel S p) : A.chart.target = univ := by
  letI := A.topology
  apply eq_univ_of_forall
  intro x
  have hv : A.coordinates.symm x.val ∈ A.chart.source := by rw [A.chart_source]; trivial
  have heq : A.chart (A.coordinates.symm x.val) = x := by
    apply Subtype.ext
    rw [A.chart_value, LinearEquiv.apply_symm_apply]
  exact heq ▸ A.chart.map_source hv

/-- The affine model has exactly its ordinary finite-dimensional topology. -/
noncomputable def affine_homeomorph (A : AffineFiberModel S p) :
    letI := A.topology
    TangentSpace S p ≃ₜ Euclidean n := by
  letI := A.topology
  exact (A.chart.toHomeomorphOfSourceEqUnivTargetEqUniv
    A.chart_source (affine_chart_target A)).trans (Homeomorph.Set.univ _)

@[simp] theorem affine_homeomorph_apply (A : AffineFiberModel S p)
    (v : TangentSpace S p) : letI := A.topology;
    affine_homeomorph A v = A.coordinates v := A.chart_value v

@[simp] theorem affine_homeomorph_symm_apply (A : AffineFiberModel S p)
    (v : Euclidean n) : letI := A.topology;
    (affine_homeomorph A).symm v = A.coordinates.symm v := by
  letI := A.topology
  apply A.coordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  exact (affine_homeomorph_apply A _).symm.trans ((affine_homeomorph A).apply_symm_apply v)

/-- The fixed original metric controls any linear coordinates on the fiber. -/
theorem fiber_coordinate_bound (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    ∃ C : ℝ, 0 < C ∧ ∀ w, ‖E w‖ ≤ C * tangentNorm g p w := by
  let e := selectedChart S p
  let D := selectedCoordinates S p
  obtain ⟨C, hC, V, hV, hpV, hVs, hb⟩ :=
    LocalCurveTrapping.local_coordinate_bound g ⟨e.val, e.property.1⟩ p e.property.2
  let L := (D.symm.trans E).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨(‖L‖ + 1) * C, mul_pos (by positivity) hC, ?_⟩
  intro w
  have hD : ‖D w‖ ≤ C * tangentNorm g p w := hb p e.property.2 w hpV
  have hL : L (D w) = E w := by simp [L]
  calc
    ‖E w‖ = ‖L (D w)‖ := congrArg norm hL.symm
    _ ≤ ‖L‖ * ‖D w‖ := L.le_opNorm _
    _ ≤ (‖L‖ + 1) * ‖D w‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ (‖L‖ + 1) * (C * tangentNorm g p w) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ = ((‖L‖ + 1) * C) * tangentNorm g p w := (mul_assoc _ _ _).symm

/-- Continuity of the reference fiber norm requires no topology on its
intrinsic derivations: it is a finite Gram polynomial in any linear coordinates. -/
theorem fiber_norm_continuous (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Continuous (fun w : Euclidean n => tangentNorm g p (E.symm w)) := by
  let e := selectedChart S p
  let D := selectedCoordinates S p
  let L := (E.symm.trans D).toContinuousLinearEquiv
  have hc : Continuous (LocalCurveTrapping.chartNorm g ⟨e.val, e.property.1⟩ p) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (LocalCurveTrapping.chartNorm_continuousAt g ⟨e.val, e.property.1⟩
      p e.property.2 w).comp (continuousAt_const.prodMk continuousAt_id)
  have heq (w : Euclidean n) :
      LocalCurveTrapping.chartNorm g ⟨e.val, e.property.1⟩ p (L w) =
        tangentNorm g p (E.symm w) :=
    LocalCurveTrapping.chartNorm_coordinates g ⟨e.val, e.property.1⟩ p e.property.2 _
  exact (show (fun w => tangentNorm g p (E.symm w)) =
    (fun w => LocalCurveTrapping.chartNorm g ⟨e.val, e.property.1⟩ p (L w)) from
      funext (fun w => (heq w).symm)) ▸ hc.comp L.continuous

/-- Subtraction is preserved by linear coordinates on an intrinsic fiber. -/
theorem fiber_coordinates_sub (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (v w : TangentSpace S p) : E (v - w) = E v - E w := by
  have h : v - w = v + (-1 : ℝ) • w := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h, E.map_add, E.map_smul, neg_one_smul, sub_eq_add_neg]

/-- Every closed reference-metric ball is compact, including in rank zero. -/
theorem reference_ball_compact (g : RiemannianMetric S) (A : AffineFiberModel S p)
    (v : TangentSpace S p) (r : ℝ) (hr : 0 ≤ r) :
    letI := A.topology
    IsCompact {z : TangentSpace S p | tangentNorm g p (z - v) ≤ r} := by
  letI := A.topology
  let e := affine_homeomorph A
  let K : Set (Euclidean n) := {x | tangentNorm g p (A.coordinates.symm x - v) ≤ r}
  have hc : Continuous (fun x : Euclidean n => tangentNorm g p (A.coordinates.symm x - v)) := by
    have hh := (fiber_norm_continuous g p A.coordinates).comp
      (continuous_id.sub continuous_const : Continuous (fun x : Euclidean n => x - A.coordinates v))
    change Continuous (fun x => tangentNorm g p (A.coordinates.symm (x - A.coordinates v))) at hh
    have heq (x : Euclidean n) : A.coordinates.symm (x - A.coordinates v) =
        A.coordinates.symm x - v := by
      apply A.coordinates.injective
      rw [A.coordinates.apply_symm_apply, fiber_coordinates_sub,
        A.coordinates.apply_symm_apply]
    simpa only [heq] using hh
  have hclosed : IsClosed K := isClosed_le hc continuous_const
  obtain ⟨C, hC, hb⟩ := fiber_coordinate_bound g p A.coordinates
  have hsub : K ⊆ Metric.closedBall (A.coordinates v) (C * r) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hh := (hb (A.coordinates.symm x - v)).trans
      (mul_le_mul_of_nonneg_left hx hC.le)
    rw [fiber_coordinates_sub, A.coordinates.apply_symm_apply] at hh
    exact hh
  have hK : IsCompact K := (isCompact_closedBall _ _).of_isClosed_subset hclosed hsub
  have heq : e ⁻¹' K = {z | tangentNorm g p (z - v) ≤ r} := by
    ext z
    simp [K, e]
  exact heq ▸ e.isCompact_preimage.mpr hK

/-- Compactness of base points and the coordinate unit ball gives a uniform
upper bound. Using the closed unit ball also covers the zero-dimensional case. -/
theorem compact_chart_upper_bound {d : ℕ} {X : Type u} [TopologicalSpace X]
    {T : SmoothManifold d .euclidean X} (h : RiemannianMetric T)
    (i : TangentIndex T) (K : Set X) (hK : IsCompact K)
    (hsource : K ⊆ i.val.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ q ∈ K, ∀ w : Euclidean d,
      LocalCurveTrapping.chartNorm h i q w ≤ B * ‖w‖ := by
  have hc : ContinuousOn
      (fun z : X × Euclidean d => LocalCurveTrapping.chartNorm h i z.1 z.2)
      (K ×ˢ Metric.closedBall 0 1) := by
    intro z hz
    exact (LocalCurveTrapping.chartNorm_continuousAt h i z.1 (hsource hz.1) z.2).continuousWithinAt
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall (0 : Euclidean d) 1)).bddAbove_image hc
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro q hq w
  by_cases hw : w = 0
  · subst w
    simp [LocalCurveTrapping.chartNorm]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hu : ‖w‖⁻¹ • w ∈ Metric.closedBall (0 : Euclidean d) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, norm_smul, ne_of_gt hn]
  have hb := hB ⟨(q, ‖w‖⁻¹ • w), ⟨hq, hu⟩, rfl⟩
  change LocalCurveTrapping.chartNorm h i q (‖w‖⁻¹ • w) ≤ B at hb
  rw [LocalCurveTrapping.chartNorm_smul h i q (hsource hq),
    abs_of_pos (inv_pos.mpr hn)] at hb
  have hb' : LocalCurveTrapping.chartNorm h i q w ≤ B * ‖w‖ := by
    apply (div_le_iff₀ hn).mp
    simpa only [div_eq_inv_mul] using hb
  exact hb'.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self B]) hn.le)

/-- The explicit uniform upper estimate on a closed reference-metric ball.
No completeness or domination assumption on the smooth metric is needed. -/
theorem reference_ball_upper_bound (g : RiemannianMetric S) (A : AffineFiberModel S p)
    (h : letI := A.topology; RiemannianMetric A.manifold)
    (v : TangentSpace S p) (r : ℝ) (hr : 0 ≤ r) :
    letI := A.topology
    ∃ K : ℝ, 0 < K ∧ ∀ z : TangentSpace S p, tangentNorm g p (z - v) ≤ r →
      ∀ x : TangentSpace A.manifold z,
        tangentNorm h z x ≤ K * tangentNorm g p (A.identification z x) := by
  letI := A.topology
  obtain ⟨B, hB, hb⟩ := compact_chart_upper_bound h ⟨A.chart, A.chart_mem⟩
    {z | tangentNorm g p (z - v) ≤ r} (reference_ball_compact g A v r hr)
    (by intro z hz; rw [A.chart_source]; trivial)
  obtain ⟨C, hC, hc⟩ := fiber_coordinate_bound g p A.coordinates
  refine ⟨B * C, mul_pos hB hC, ?_⟩
  intro z hz x
  let E := (tangentStructure A.manifold).fiberCoordinates.equiv A.chart A.chart_mem z
    (A.chart_source ▸ mem_univ z)
  have hident : A.coordinates (A.identification z x) = E x := by
    change A.coordinates (A.coordinates.symm (E x)) = E x
    exact A.coordinates.apply_symm_apply _
  calc
    tangentNorm h z x = LocalCurveTrapping.chartNorm h ⟨A.chart, A.chart_mem⟩ z (E x) :=
      (LocalCurveTrapping.chartNorm_coordinates h ⟨A.chart, A.chart_mem⟩ z
        (A.chart_source ▸ mem_univ z) x).symm
    _ ≤ B * ‖E x‖ := hb z hz (E x)
    _ = B * ‖A.coordinates (A.identification z x)‖ := by rw [hident]
    _ ≤ B * (C * tangentNorm g p (A.identification z x)) :=
      mul_le_mul_of_nonneg_left (hc _) hB.le
    _ = (B * C) * tangentNorm g p (A.identification z x) := (mul_assoc _ _ _).symm

/-- Domination of tangent norms controls the Euclidean displacement of every
piecewise C¹ curve, including curves with corners and constant intervals. -/
theorem affine_displacement_le_length (g : RiemannianMetric S) (A : AffineFiberModel S p)
    (h : letI := A.topology; RiemannianMetric A.manifold)
    (hdom : letI := A.topology; ∀ v (x : TangentSpace A.manifold v),
      tangentNorm g p (A.identification v x) ≤ tangentNorm h v x) :
    letI := A.topology
    ∃ C : ℝ, 0 < C ∧ ∀ {a b : ℝ} (c : PiecewiseC1Curve A.manifold a b),
      ‖A.coordinates (c b) - A.coordinates (c a)‖ ≤ C * length h c := by
  letI := A.topology
  obtain ⟨C, hC, hb⟩ := fiber_coordinate_bound g p A.coordinates
  refine ⟨C, hC, ?_⟩
  intro a b c
  have hs : ∀ t ∈ Icc a b, c t ∈ A.chart.source := by
    intro t ht; rw [A.chart_source]; trivial
  have hh := LocalCurveTrapping.coordinate_displacement_le_length h
    ⟨A.chart, A.chart_mem⟩ hC.le c c.ordered le_rfl hs (by
      intro t ht x
      have heq : (tangentStructure A.manifold).fiberCoordinates.equiv
          A.chart A.chart_mem (c t) (hs t ht) x =
          A.coordinates (A.identification (c t) x) := by
        change _ = A.coordinates (A.coordinates.symm _)
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [heq]
      exact (hb _).trans (mul_le_mul_of_nonneg_left (hdom _ _) hC.le))
  simpa only [A.chart_value] using hh

/-- The component metric is a metric on the whole connected manifold.
The construction preserves the original topology definitionally. -/
theorem connected_length_metric {d : ℕ} {X : Type u} [TopologicalSpace X]
    [PreconnectedSpace X] (T : SmoothManifold d .euclidean X)
    (h : RiemannianMetric T) (o : X) :
    ∃ D : MetricSpace X,
      D.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X) ∧
      ∀ x y, @dist X D.toDist x y = sInf (pathLengths h x y) := by
  obtain ⟨D, htop, hdist⟩ := LengthDistance.component_metric h o
  let D' := D.replaceTopology htop.symm
  letI := D'
  let e : X ≃ₜ connectedComponent o := (Homeomorph.Set.univ X).symm.trans
    (Homeomorph.setCongr (PreconnectedSpace.connectedComponent_eq_univ o).symm)
  let DX := e.isEmbedding.comapMetricSpace e
  exact ⟨DX, rfl, fun x y => hdist (e x) (e y)⟩

/-- A smooth metric on an affine tangent fiber is complete when its norm
dominates the fixed original fiber norm. The Cauchy sequence first converges in
linear coordinates. The topology theorem for length distance, proved upstream
using local upper estimates and straight segments, then gives metric convergence. -/
theorem dominated_metric_complete (g : RiemannianMetric S) (A : AffineFiberModel S p)
    (h : letI := A.topology; RiemannianMetric A.manifold)
    (hdom : letI := A.topology; ∀ v (x : TangentSpace A.manifold v),
      tangentNorm g p (A.identification v x) ≤ tangentNorm h v x) :
    letI := A.topology
    LengthMetricComplete h := by
  letI := A.topology
  let e := affine_homeomorph A
  letI : ConnectedSpace (TangentSpace S p) :=
    e.symm.surjective.connectedSpace e.symm.continuous
  obtain ⟨D, htop, hdist⟩ := connected_length_metric A.manifold h (0 : TangentSpace S p)
  let D' := D.replaceTopology htop.symm
  letI := D'
  refine ⟨D', rfl, hdist, ?_⟩
  obtain ⟨C, hC, hb⟩ := affine_displacement_le_length g A h hdom
  have hdistbound (x y : TangentSpace S p) :
      dist (e x) (e y) ≤ C * dist x y := by
    have hne : (pathLengths h x y).Nonempty :=
      (LengthDistance.pathLengths_nonempty_iff h x y).mpr
        ((LengthDistance.path_exists A.manifold x y).mpr (by
          rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial))
    have hlower : dist (e x) (e y) / C ≤ sInf (pathLengths h x y) := by
      apply le_csInf hne
      rintro L ⟨a, b, c, hx, hy, rfl⟩
      apply (div_le_iff₀ hC).mpr
      have hh := hb c
      rw [hx, hy] at hh
      rw [dist_eq_norm]
      change ‖affine_homeomorph A x - affine_homeomorph A y‖ ≤ length h c * C
      rw [affine_homeomorph_apply, affine_homeomorph_apply]
      simpa only [norm_sub_rev, mul_comm] using hh
    rw [hdist]
    exact (div_le_iff₀ hC).mp hlower |>.trans_eq (mul_comm _ _)
  apply Metric.complete_of_cauchySeq_tendsto
  intro s hs
  have hseq : CauchySeq (fun k => e (s k)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hs (ε / C) (div_pos hε hC)
    refine ⟨N, ?_⟩
    intro m hm k hk
    exact (hdistbound (s m) (s k)).trans_lt
      ((mul_lt_mul_of_pos_left (hN m hm k hk) hC).trans_eq (mul_div_cancel₀ ε hC.ne'))
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hseq
  refine ⟨e.symm y, ?_⟩
  have he := e.symm.continuous.continuousAt.tendsto.comp hy
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using he

end Analytic

open SmoothManifolds.MapData SmoothManifolds.DifferentialData
  SmoothManifolds.FiniteRegularityData SmoothManifolds.BoundaryData

theorem localDiffeomorphism_of_bijective_differential
    {n m : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n .euclidean M) (T : SmoothManifold m .euclidean N)
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (hbij : ∀ p, Function.Bijective (L p)) :
    SmoothManifolds.TensorData.IsLocalDiffeomorphism S T f := by
  refine ⟨hf, ?_⟩
  intro p
  have hf1 := SmoothManifolds.manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf
  obtain ⟨F, G, K, hK⟩ := SmoothManifolds.MapClasses.exists_differential_model S T f hf1 p
  letI := F.group
  letI := F.module
  letI := G.group
  letI := G.module
  have hi := SmoothManifolds.MapClasses.smooth_tangent_invariants S T f hf p (L p) (hL p)
  have hc := SmoothManifolds.MapClasses.full_tangent_invariants S T f hf1 p F G K hK
  have hKb : Function.Bijective K :=
    ⟨hc.2.1.mp (hi.2.1.mpr (hbij p).1), hc.2.2.mp (hi.2.2.mpr (hbij p).2)⟩
  have hp : p ∈ manifoldInterior S := by
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    exact ⟨e, he, hp, by simp [SmoothManifolds.ModelData.modelSet]⟩
  have hfp : f p ∈ manifoldInterior T := by
    obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
    exact ⟨d, hd, hfp, by simp [SmoothManifolds.ModelData.modelSet]⟩
  obtain ⟨h, hph, _, _, heq, _, hback⟩ :=
    SmoothManifolds.InteriorInverse.interior_inverse (⊤ : ℕ∞) (by simp) S T f hf p hp hfp F G K hK hKb
  have hfph : f p ∈ h.target := by
    simpa only [heq hph] using h.map_source hph
  refine ⟨h.symm, hback (f p) hfph, ?_, ?_, ?_⟩
  · rw [← heq hph]
    exact h.left_inv hph
  · filter_upwards [h.open_source.mem_nhds hph] with x hx
    change h.symm (f x) = x
    rw [← heq hx]
    exact h.left_inv hx
  · filter_upwards [h.open_target.mem_nhds hfph] with y hy
    change f (h.symm y) = y
    rw [← heq (h.map_target hy)]
    exact h.right_inv hy

section Bridge
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}
  (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
  (hF : IsMaximalFamily S C F) (p : M) (A : AffineFiberModel S p)
  (hv : ∀ v : TangentSpace S p, (⟨p, v⟩ : Phase S) ∈ exponentialDomain F)

include C F hF hv in
theorem affine_exponential_smooth :
    letI := A.topology
    IsSmoothMap A.manifold S (fiberExponential F p) := by
  letI := A.topology
  have hcoord : Continuous (fun v => A.coordinates v) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hh := continuous_subtype_val.continuousAt.comp
      (A.chart.continuousAt (A.chart_source ▸ mem_univ v))
    change ContinuousAt (fun y => (A.chart y).val) v at hh
    simpa only [A.chart_value] using hh
  have hphase : Continuous (fun x : Euclidean n => (⟨p, A.coordinates.symm x⟩ : Phase S)) :=
    ExponentialNormalCoordinates.fiberInclusion_continuous_basis p A.coordinates
  have hcontE : Continuous (fun x : Euclidean n => fiberExponential F p (A.coordinates.symm x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ExponentialNormalCoordinates.exponential_smooth C F hF
      ⟨p, A.coordinates.symm x⟩ (hv (A.coordinates.symm x))).1.comp
      (f := fun y : Euclidean n => (⟨p, A.coordinates.symm y⟩ : Phase S)) hphase.continuousAt
  have hcont : Continuous (fiberExponential F p) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using hcontE.comp hcoord
  intro v
  obtain ⟨d, hd, hpd⟩ := S.smoothStructure.property.1.1 (fiberExponential F p v)
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞)
    A.manifold.smoothStructure.val S.smoothStructure.val
    A.manifold.smoothStructure.property.1 S.smoothStructure.property.1
    (fiberExponential F p) v).mpr
  refine ⟨hcont.continuousAt, A.chart, A.chart_mem, d, hd,
    A.chart_source ▸ mem_univ v, hpd, ?_⟩
  let U := (fun x : Euclidean n => fiberExponential F p (A.coordinates.symm x)) ⁻¹' d.source
  refine ⟨U, d.open_source.preimage hcontE, ?_,
    fun x : Euclidean n => (d (fiberExponential F p (A.coordinates.symm x))).val, ?_, ?_⟩
  · simpa only [U, mem_preimage, A.chart_value, LinearEquiv.symm_apply_apply] using hpd
  · intro x hx
    exact (ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis C F hF
      p A.coordinates d hd x (hv _) hx).contDiffWithinAt
  · exact Eventually.of_forall (fun y => by
      dsimp only
      rw [A.chart_value, LinearEquiv.symm_apply_apply])

include C F hF hv in
theorem affine_exponential_isDifferential (v : TangentSpace S p) :
    letI := A.topology
    IsDifferential A.manifold S (fiberExponential F p) v
      ((fiberDifferential S F p v).comp (A.identification v).toLinearMap) := by
  letI := A.topology
  let f := fiberExponential F p
  have hf := affine_exponential_smooth C F hF p A hv
  obtain ⟨L, hL, _⟩ := SmoothManifolds.differential_exists A.manifold S f hf v
  let E := selectedCoordinates S p
  let d := (selectedChart S (f v)).val
  have hd := (selectedChart S (f v)).property.1
  have hpd := (selectedChart S (f v)).property.2
  let D := selectedCoordinates S (f v)
  let T := (A.coordinates.symm.trans E).toContinuousLinearEquiv
  let H : Euclidean n → Euclidean n := fun x => (d (f (A.coordinates.symm x))).val
  let H₀ : Euclidean n → Euclidean n := fun x => (d (f (E.symm x))).val
  let Q := (tangentStructure A.manifold).fiberCoordinates.equiv A.chart A.chart_mem v
    (A.chart_source ▸ mem_univ v)
  have hQ := (tangentStructure A.manifold).fiberCoordinates.isCoordinates A.chart
    A.chart_mem v (A.chart_source ▸ mem_univ v)
  have hD := (tangentStructure S).fiberCoordinates.isCoordinates d hd (f v) hpd
  have hphase : Continuous (fun x : Euclidean n => (⟨p, A.coordinates.symm x⟩ : Phase S)) :=
    ExponentialNormalCoordinates.fiberInclusion_continuous_basis p A.coordinates
  have hcont : Continuous (fun x : Euclidean n => f (A.coordinates.symm x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ExponentialNormalCoordinates.exponential_smooth C F hF
      ⟨p, A.coordinates.symm x⟩ (hv (A.coordinates.symm x))).1.comp
      (f := fun y : Euclidean n => (⟨p, A.coordinates.symm y⟩ : Phase S)) hphase.continuousAt
  let U := (fun x : Euclidean n => f (A.coordinates.symm x)) ⁻¹' d.source
  have hU : IsOpen U := d.open_source.preimage hcont
  have hvU : (A.chart v).val ∈ U := by
    simpa only [U, mem_preimage, A.chart_value, LinearEquiv.symm_apply_apply] using hpd
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H U := by
    intro x hx
    exact (ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis C F hF
      p A.coordinates d hd x (hv _) hx).contDiffWithinAt
  have heH : (fun y => H (A.chart y).val) =ᶠ[𝓝 v] (fun y => (d (f y)).val) :=
    Eventually.of_forall (fun y => by dsimp only [H]; rw [A.chart_value, LinearEquiv.symm_apply_apply])
  have h₀ : DifferentiableAt ℝ H₀ (E v) := by
    apply (ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis C F hF
      p E d hd (E v) (by simpa only [LinearEquiv.symm_apply_apply] using hv v)
      (by simpa only [LinearEquiv.symm_apply_apply] using hpd)).differentiableAt
    simp
  have hT : T (A.coordinates v) = E v := by
    change E (A.coordinates.symm (A.coordinates v)) = E v
    rw [LinearEquiv.symm_apply_apply]
  have hfun : H = H₀ ∘ T := by
    funext x
    change (d (f (A.coordinates.symm x))).val =
      (d (f (E.symm (E (A.coordinates.symm x))))).val
    rw [LinearEquiv.symm_apply_apply]
  have hderiv : fderiv ℝ H (A.coordinates v) =
      (fderiv ℝ H₀ (E v)).comp T.toContinuousLinearMap := by
    rw [hfun]
    have h₀' : HasFDerivAt H₀ (fderiv ℝ H₀ (E v)) (T (A.coordinates v)) := by
      rw [hT]
      exact h₀.hasFDerivAt
    exact (h₀'.comp (A.coordinates v) T.hasFDerivAt).fderiv
  have heq : L = (fiberDifferential S F p v).comp (A.identification v).toLinearMap := by
    apply LinearMap.ext
    intro x
    apply D.injective
    have hj := SmoothManifolds.differential_jacobian A.manifold S f hf v L hL
      A.chart d A.chart_mem hd (A.chart_source ▸ mem_univ v) hpd Q D hQ hD
      U H hU hvU hH heH x
    rw [A.chart_value, hderiv] at hj
    change D (L x) = _ at hj
    rw [hj]
    change fderiv ℝ H₀ (E v) (T (Q x)) =
      D (D.symm (fderiv ℝ H₀ (E v) (E (A.identification v x))))
    rw [D.apply_symm_apply]
    rfl
  rw [← heq]
  exact hL
end Bridge

section Geometry
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Pull back the original metric by the everywhere nonsingular exponential.
The same fixed original fiber norm supplies both the domination and the local
compact-ball estimates used in the completeness argument. -/
theorem pullback_complete :
    P202Specs.Geometry.ExponentialPullbackComplete.pullback_completeType.{u} := by
  intro n M _ _ S g C hC R hR hK hcomplete F hF p A
  letI := A.topology
  have hfull (v : TangentSpace S p) :
      (⟨p, v⟩ : Phase S) ∈ exponentialDomain F :=
    (NonpositiveJacobiGrowth.nonsingular S g C hC R hR hK hcomplete F hF p v).1
  let L : (v : TangentSpace S p) → TangentSpace A.manifold v →ₗ[ℝ]
      TangentSpace S (fiberExponential F p v) :=
    fun v => (fiberDifferential S F p v).comp (A.identification v).toLinearMap
  have hsm := affine_exponential_smooth C F hF p A hfull
  have hd : ∀ v, SmoothManifolds.DifferentialData.IsDifferential A.manifold S
      (fiberExponential F p) v (L v) :=
    affine_exponential_isDifferential C F hF p A hfull
  have hbij (v : TangentSpace S p) : Function.Bijective (L v) :=
    (NonpositiveJacobiGrowth.nonsingular S g C hC R hR hK hcomplete F hF p v).2.comp
      (A.identification v).bijective
  have hlocal := localDiffeomorphism_of_bijective_differential
    A.manifold S (fiberExponential F p) hsm L hd hbij
  let i : SmoothImmersion A.manifold S (fiberExponential F p) :=
    ⟨hsm, L, hd, fun v => (hbij v).1⟩
  let h : RiemannianMetric A.manifold :=
    SmoothMetrics.pullbackMetric g (fiberExponential F p) i
  have hpair (v : TangentSpace S p) (x y : TangentSpace A.manifold v) :
      pairing h v x y = pairing g (fiberExponential F p v)
        (fiberDifferential S F p v (A.identification v x))
        (fiberDifferential S F p v (A.identification v y)) := rfl
  have hdom (v : TangentSpace S p) (x : TangentSpace A.manifold v) :
      tangentNorm g p (A.identification v x) ≤ tangentNorm h v x :=
    differential_expands S g C hC R hR hK F hF p v (hfull v) (A.identification v x)
  refine ⟨h, hpair, ⟨hlocal, L, hd, fun _ _ _ => rfl⟩, hdom, ?_,
    dominated_metric_complete g A h hdom⟩
  intro v
  obtain ⟨K, hK, hb⟩ := reference_ball_upper_bound g A h v 1 zero_le_one
  exact ⟨1, K, zero_lt_one, hK,
    reference_ball_compact g A v 1 zero_le_one, hb⟩

end Geometry

end P202.Geometry.ExponentialPullbackComplete
