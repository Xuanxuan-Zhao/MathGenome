import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CompleteExponentialMinimizers
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialNormalCoordinates
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GeodesicCriticalityCorners
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthDistance
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.NormalMinimality
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Order.Compact

/-! The single-center implication of Hopf–Rinow, using the canonical
normal-minimality, length-distance, and geodesic interfaces. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.Geometry.CompleteExponentialMinimizers
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.ConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.ExponentialData P202.DistanceData P202.CriticalityData P202.FirstVariationData
  P202.CompleteExponentialData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The length infimum used here is exactly the existing component distance. -/
theorem lengthDistance_eq_componentDistance (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o) :
    lengthDistance g p.val q.val = componentDistance g o p q := rfl

/-- The infimum in the no-corner interface ranges over exactly the same
curves as the source length metric; only the orientation of an equality differs. -/
theorem endpointDistance_eq_lengthDistance (g : RiemannianMetric S) (p q : M) :
    endpointDistance g p q = lengthDistance g p q := by
  change sInf (endpointLengths g p q) = sInf (pathLengths g p q)
  apply congrArg sInf
  ext L
  constructor
  · rintro ⟨a,b,γ,h0,h1,hL⟩
    exact ⟨a,b,γ,h0,h1,hL.symm⟩
  · rintro ⟨a,b,γ,h0,h1,hL⟩
    exact ⟨a,b,γ,h0,h1,hL.symm⟩

theorem lengthDistance_le_length (g : RiemannianMetric S)
    {a b : ℝ} (γ : PiecewiseC1Curve S a b) :
    lengthDistance g (γ a) (γ b) ≤ length g γ :=
  csInf_le (LengthDistance.pathLengths_bddBelow g _ _) ⟨a,b,γ,rfl,rfl,rfl⟩

theorem lengthDistance_self (g : RiemannianMetric S) (p : M) :
    lengthDistance g p p = 0 :=
  LengthDistance.componentDistance_self g p ⟨p,mem_connectedComponent⟩

/-- Having time one at every scaled initial velocity forces every real time
in the original maximal interval. No completeness of a metric is used. -/
theorem full_interval (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p) (v : TangentSpace S p) :
    (F.interval ⟨p,v⟩).carrier = univ := by
  apply Set.eq_univ_of_forall
  intro t
  by_cases ht : t = 0
  · subst t
    exact (hF ⟨p,v⟩).1
  obtain ⟨J,hJ,hmax⟩ := GeodesicIVP.maximal_affine S C ⟨p,v⟩
    (F.interval ⟨p,v⟩) (F.curve ⟨p,v⟩) (hF ⟨p,v⟩) t 0 ht (hF ⟨p,v⟩).1
  have hi : affineCurve S (F.curve ⟨p,v⟩) t 0 0 = (⟨p,t • v⟩ : Phase S) := by
    change (⟨(F.curve ⟨p,v⟩ (t * 0 + 0)).1,
      t • (F.curve ⟨p,v⟩ (t * 0 + 0)).2⟩ : Phase S) = _
    rw [mul_zero,add_zero,(hF ⟨p,v⟩).2.1]
  rw [hi] at hmax
  have hI := (GeodesicIVP.maximal_unique S C ⟨p,t • v⟩
    (F.interval ⟨p,t • v⟩) J (F.curve ⟨p,t • v⟩)
    (affineCurve S (F.curve ⟨p,v⟩) t 0) (hF ⟨p,t • v⟩) hmax).1
  have h1 : 1 ∈ (F.interval ⟨p,t • v⟩).carrier := hfull (t • v)
  rw [hI,hJ] at h1
  simpa only [affineDomain,mem_ofPred_eq,mul_one,add_zero] using h1

/-- A smooth intrinsic geodesic gives a curve in the original competitor
class on each compact interval of its actual domain. -/
noncomputable def geodesicRepresentative
    (C : Connection (tangentBundle S)) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a ≤ b) (hdom : Icc a b ⊆ I.carrier) :
    PiecewiseC1Curve S a b := by
  let node : Fin 2 → ℝ := fun i => if i = 0 then a else b
  have hnode : Monotone node := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [node]
  have hV := GeodesicCriticalityCorners.geodesic_velocity_smoothFieldAlongOn C I q hq hdom
  refine { ordered := hab
           toFun := fun t => (q t).1
           continuousOn := GeodesicCriticalityCorners.smooth_field_base_continuous hV
           pieces := 1
           node := node
           monotone_node := hnode
           first_node := by simp [node]
           last_node := by simp [node]
           regular := ?_ }
  intro i
  fin_cases i
  simpa [node] using GeodesicCriticalityCorners.smooth_field_base_c1 hV

/-- Every vector at the full center supplies a genuine radial geodesic
representative of length equal to its norm, also for the zero vector. -/
theorem radial_segment (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p)
    (v : TangentSpace S p) :
    ∃ γ : PiecewiseC1Curve S 0 1,
      γ 0 = p ∧ γ 1 = fiberExponential F p v ∧
      EqOn γ (fun t => (F.curve ⟨p,v⟩ t).1) (Icc 0 1) ∧
      EqOn γ (fun t => fiberExponential F p (t • v)) (Icc 0 1) ∧
      IsGeodesicOn S C (Icc 0 1) (F.curve ⟨p,v⟩) ∧
      length g γ = tangentNorm g p v := by
  have hdom : Icc (0 : ℝ) 1 ⊆ (F.interval ⟨p,v⟩).carrier := by
    rw [full_interval C F hF p hfull v]
    exact subset_univ _
  let γ := geodesicRepresentative C (F.interval ⟨p,v⟩) (F.curve ⟨p,v⟩)
    (hF ⟨p,v⟩).2.2.1 (a := 0) (b := 1) (by norm_num) hdom
  have htrace : ∀ t : ℝ, γ t = (F.curve ⟨p,v⟩ t).1 := fun _ => rfl
  refine ⟨γ,?_,rfl,fun _ _ => rfl,?_,?_,?_⟩
  · change (F.curve ⟨p,v⟩ 0).1 = p
    rw [(hF ⟨p,v⟩).2.1]
  · intro t ht
    exact (ExponentialNormalCoordinates.radial_identity_at C F hF p v t (hdom ht)).2.symm
  · intro t ht
    exact (hF ⟨p,v⟩).2.2.1 t (hdom ht)
  · have hL := GeodesicCriticalityCorners.geodesic_piece_length_of_eqOn g C hC
      (F.interval ⟨p,v⟩) (F.curve ⟨p,v⟩) (hF ⟨p,v⟩).2.2.1
      (a := 0) (b := 1) (by norm_num) hdom γ (fun _ _ => rfl)
    change (∫ t in (0 : ℝ)..1, speed g γ t) = _
    have hinit := congrArg (fun w : Phase S => tangentNorm g w.1 w.2) (hF ⟨p,v⟩).2.1
    calc
      _ = tangentNorm g (F.curve ⟨p,v⟩ 0).1 (F.curve ⟨p,v⟩ 0).2 * (1 - 0) := hL
      _ = tangentNorm g p v := by rw [hinit]; ring

/-- The easy inclusion in the eventual closed-ball image identity. -/
theorem distance_exponential_le_norm (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p) (v : TangentSpace S p) :
    lengthDistance g p (fiberExponential F p v) ≤ tangentNorm g p v := by
  obtain ⟨γ,h0,h1,_,_,_,hL⟩ := radial_segment g C hC F hF p hfull v
  have h := lengthDistance_le_length g γ
  rwa [h0,h1,hL] at h

/-- Fiber-coordinate continuity is established from the actual smooth flow,
without putting an arbitrary norm or topology on the intrinsic tangent fiber. -/
theorem exponential_coordinates_continuous
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Continuous (fun x : Euclidean n => fiberExponential F p (E.symm x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have he : ContinuousAt (exponential F) (⟨p,E.symm x⟩ : Phase S) :=
    (ExponentialNormalCoordinates.exponential_smooth C F hF _ (hfull (E.symm x))).1
  exact he.comp (f := fun y : Euclidean n => (⟨p,E.symm y⟩ : Phase S))
    (ExponentialNormalCoordinates.fiberInclusion_continuous_basis p E).continuousAt

/-- A closed fiber ball contained in the actual exponential domain has
compact exponential image. This applies at local centers without full domain. -/
theorem compact_exponential_image_of_domain (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (R : ℝ)
    (hball : ∀ v : TangentSpace S p, tangentNorm g p v ≤ R →
      (⟨p,v⟩ : Phase S) ∈ exponentialDomain F) :
    IsCompact (fiberExponential F p '' {v : TangentSpace S p | tangentNorm g p v ≤ R}) := by
  obtain ⟨E,hE⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist g p
  let K := {x : Euclidean n | tangentNorm g p (E.symm x) ≤ R}
  have hclosed : IsClosed K := isClosed_le
    (ExponentialNormalCoordinates.orthonormal_norm_continuous g p E hE) continuous_const
  have hK : IsCompact K := (isCompact_closedBall (0 : Euclidean n) R).of_isClosed_subset hclosed (by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (ExponentialNormalCoordinates.coordinate_norm_le_metric_norm g p E hE x).trans hx)
  have heq : (fun x : Euclidean n => fiberExponential F p (E.symm x)) '' K =
      fiberExponential F p '' {v : TangentSpace S p | tangentNorm g p v ≤ R} := by
    ext q
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨E.symm x,hx,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      refine ⟨E v,?_,?_⟩
      · simpa only [K,mem_ofPred_eq,LinearEquiv.symm_apply_apply] using hv
      · simp only [LinearEquiv.symm_apply_apply]
  rw [← heq]
  apply hK.image_of_continuousOn
  intro x hx
  have he : ContinuousAt (exponential F) (⟨p,E.symm x⟩ : Phase S) :=
    (ExponentialNormalCoordinates.exponential_smooth C F hF _ (hball (E.symm x) hx)).1
  exact (he.comp (f := fun y : Euclidean n => (⟨p,E.symm y⟩ : Phase S))
    (ExponentialNormalCoordinates.fiberInclusion_continuous_basis p E).continuousAt).continuousWithinAt

/-- Local centers need only their own normal-chart domain, not a global
exponential map. This is the compactness input for the second sphere argument. -/
theorem compact_normal_closed_ball (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r R : ℝ)
    (d : ModelChart n .euclidean M) (hrR : r < R)
    (hd : IsNormalChart g F p E R d) :
    IsCompact (fiberExponential F p '' {v : TangentSpace S p | tangentNorm g p v ≤ r}) := by
  apply compact_exponential_image_of_domain g C F hF p r
  intro v hv
  let x : ModelSpace n .euclidean := ⟨E v,mem_univ _⟩
  have hx : tangentNorm g p (E.symm x.val) < R := by
    simpa only [x,LinearEquiv.symm_apply_apply] using hv.trans_lt hrR
  have hdomain := (hd.2.2.2.2.2 x hx).1
  simpa only [x,LinearEquiv.symm_apply_apply] using hdomain

/-- Every closed fiber ball has compact exponential image at the full center.
Compactness is in the original topology on M, in every finite dimension. -/
theorem compact_exponential_image (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p)
    (R : ℝ) :
    IsCompact (fiberExponential F p '' {v : TangentSpace S p | tangentNorm g p v ≤ R}) :=
  compact_exponential_image_of_domain g C F hF p R (fun v _ => hfull v)

/-- The degenerate endpoint is already a genuine minimizing constant
geodesic; it needs no full exponential hypothesis. -/
theorem constant_minimizer (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) :
    ∃ γ : PiecewiseC1Curve S 0 1, (∀ t, γ t = p) ∧
      EqOn γ (fun t => (F.curve ⟨p,0⟩ t).1) (Icc 0 1) ∧
      IsGeodesicOn S C (Icc 0 1) (F.curve ⟨p,0⟩) ∧
      length g γ = lengthDistance g p p ∧
      ∀ {a b : ℝ} (η : PiecewiseC1Curve S a b), length g γ ≤ length g η := by
  obtain ⟨γ,hγ,hL⟩ := MetricFoundation.stationary_exists S 0 1 (by norm_num) p
  obtain ⟨hI,hzero⟩ := ExponentialNormalCoordinates.zero_family C F hF p
  refine ⟨γ,hγ,?_,?_,?_,?_⟩
  · intro t _
    change γ t = (F.curve ⟨p,0⟩ t).1
    exact (hγ t).trans (congrArg Sigma.fst (hzero t)).symm
  · intro t _
    exact (hF ⟨p,0⟩).2.2.1 t (by rw [hI]; trivial)
  · rw [(hL g).1,lengthDistance_self]
  · intro a b η
    rw [(hL g).1]
    exact LengthDistance.length_nonneg g η

/-- The hard geometric stage can be isolated as attainment by an exponential
vector of norm equal to the original distance. This helper does not assume
metric completeness and does not assert that attainment has been proved. -/
theorem minimizing_geodesics_of_vectors (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p)
    (hmin : ∀ q : M, ∃ v : TangentSpace S p,
      fiberExponential F p v = q ∧ tangentNorm g p v = lengthDistance g p q) :
    MinimizingGeodesicsFrom g C F p := by
  intro q
  obtain ⟨v,hv,hnorm⟩ := hmin q
  obtain ⟨γ,h0,h1,htrace,hrad,hgeo,hL⟩ := radial_segment g C hC F hF p hfull v
  refine ⟨v,γ,h0,h1.trans hv,hv,htrace,hrad,hgeo,hL,hL.trans hnorm,?_,?_⟩
  · intro a b η hη0 hη1
    have h := lengthDistance_le_length g η
    rw [hη0,hη1] at h
    exact (hL.trans hnorm).le.trans h
  · intro hq
    have hv0 : v = 0 := (SmoothMetrics.tangentNorm_eq_zero_iff g p v).mp (by
      rw [hnorm,hq,lengthDistance_self])
    refine ⟨hv0,?_⟩
    intro t ht
    calc
      γ t = (F.curve ⟨p,v⟩ t).1 := htrace ht
      _ = p := by rw [hv0,(ExponentialNormalCoordinates.zero_family C F hF p).2 t]

/-- Once the distance-attaining vectors are available, the exact image
identity follows from the radial length bound in the other direction. -/
theorem closed_ball_image_of_vectors (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p)
    (hmin : ∀ q : M, ∃ v : TangentSpace S p,
      fiberExponential F p v = q ∧ tangentNorm g p v = lengthDistance g p q)
    (R : ℝ) :
    {q : M | lengthDistance g p q ≤ R} =
      fiberExponential F p '' {v : TangentSpace S p | tangentNorm g p v ≤ R} := by
  ext q
  constructor
  · intro hq
    obtain ⟨v,hv,hnorm⟩ := hmin q
    exact ⟨v,by change tangentNorm g p v ≤ R; rw [hnorm]; exact hq,hv⟩
  · rintro ⟨v,hv,rfl⟩
    exact (distance_exponential_le_norm g C hC F hF p hfull v).trans hv

theorem compact_exponential_balls_of_vectors (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p)
    (hmin : ∀ q : M, ∃ v : TangentSpace S p,
      fiberExponential F p v = q ∧ tangentNorm g p v = lengthDistance g p q) :
    CompactExponentialBalls g F p := by
  intro R _
  have heq := closed_ball_image_of_vectors g C hC F hF p hfull hmin R
  refine ⟨heq,?_⟩
  rw [heq]
  exact compact_exponential_image g C F hF p hfull R

/-- Closed bounded subsets are closed subsets of a compact ball. Replacing
an arbitrary real bound by its maximum with zero includes the empty set. -/
theorem closed_bounded_compact_of_balls (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (hballs : CompactExponentialBalls g F p) :
    ClosedBoundedCompact g p := by
  intro K hclosed hbounded
  obtain ⟨R,hR⟩ := hbounded
  apply ((hballs (max R 0) (le_max_right _ _)).2).of_isClosed_subset hclosed
  intro q hq
  exact (hR q hq).trans (le_max_left _ _)

/-- A proved reduction, with attainment explicitly left as an additional
hypothesis. This is not the requested conditional target. -/
theorem conclusions_of_vectors (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p)
    (hmin : ∀ q : M, ∃ v : TangentSpace S p,
      fiberExponential F p v = q ∧ tangentNorm g p v = lengthDistance g p q) :
    MinimizingGeodesicsFrom g C F p ∧ CompactExponentialBalls g F p ∧
      ClosedBoundedCompact g p := by
  have hballs := compact_exponential_balls_of_vectors g C hC F hF p hfull hmin
  exact ⟨minimizing_geodesics_of_vectors g C hC F hF p hfull hmin,hballs,
    closed_bounded_compact_of_balls g F p hballs⟩

/-- Full coverage of the zero-dimensional boundary case: connectedness makes
the manifold a singleton, so the distance-attaining vector is zero. -/
theorem zero_dimension_conclusions {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold 0 .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p) :
    MinimizingGeodesicsFrom g C F p ∧ CompactExponentialBalls g F p ∧
      ClosedBoundedCompact g p := by
  apply conclusions_of_vectors g C hC F hF p hfull
  intro q
  have hq : q ∈ connectedComponent p := by simp
  rw [LengthDistance.zero_dimension S p] at hq
  have hqp : q = p := hq
  subst q
  refine ⟨0,(ExponentialNormalCoordinates.zero_section_at C F hF p).2,?_⟩
  rw [SmoothMetrics.tangentNorm_zero,lengthDistance_self]

/-- The maximal-time step in the distance-equality propagation argument. -/
theorem distance_equality_reaches_endpoint {f : ℝ → ℝ} {ε d : ℝ}
    (hε : ε ≤ d) (hf : Continuous f) (hstart : f ε = d - ε)
    (hstep : ∀ t ∈ Icc ε d, t < d → f t = d - t →
      ∃ s ∈ Ioc t d, f s = d - s) : f d = 0 := by
  let A := Icc ε d ∩ {t | f t = d - t}
  have hA : IsCompact A := isCompact_Icc.inter_right
    (isClosed_eq hf (continuous_const.sub continuous_id))
  have hne : A.Nonempty := ⟨ε,⟨⟨le_rfl,hε⟩,hstart⟩⟩
  obtain ⟨t,ht,hmax⟩ := hA.exists_isGreatest hne
  have htd : t = d := by
    by_contra hne
    have hlt : t < d := lt_of_le_of_ne ht.1.2 hne
    obtain ⟨s,hs,heq⟩ := hstep t ht.1 hlt ht.2
    have hmem : s ∈ A := ⟨⟨ht.1.1.trans hs.1.le,hs.2⟩,heq⟩
    exact (not_lt_of_ge (hmax hmem)) hs.1
  simpa only [mem_ofPred_eq,htd,sub_self] using ht.2

section Sphere
variable {X : Type*} [MetricSpace X]
/-- Compactness upgrades approximate crossings of a distance sphere to an
exact point that splits the distance. -/
theorem distance_sphere_split {p q : X} {r : ℝ}
    (hcompact : IsCompact (Metric.sphere p r))
    (hne : (Metric.sphere p r).Nonempty)
    (hcross : ∀ ε : ℝ, 0 < ε → ∃ y ∈ Metric.sphere p r,
      r + dist y q ≤ dist p q + ε) :
    ∃ y ∈ Metric.sphere p r, dist p q = r + dist y q := by
  obtain ⟨y,hy,hmin⟩ := hcompact.exists_isMinOn hne
    ((continuous_id.dist continuous_const).continuousOn :
      ContinuousOn (fun y : X => dist y q) (Metric.sphere p r))
  refine ⟨y,hy,le_antisymm ?_ ?_⟩
  · calc
      dist p q ≤ dist p y + dist y q := dist_triangle p y q
      _ = r + dist y q := by rw [dist_comm p y,Metric.mem_sphere.mp hy]
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨z,hz,hbound⟩ := hcross ε hε
    have hle : dist y q ≤ dist z q := hmin hz
    linarith
end Sphere

/-- Connectedness makes the source infimum finite and nonnegative. -/
theorem lengthDistance_nonneg [PreconnectedSpace M] (g : RiemannianMetric S) (p q : M) :
    0 ≤ lengthDistance g p q :=
  LengthDistance.componentDistance_nonneg g p ⟨p,mem_connectedComponent⟩ ⟨q,by simp⟩

theorem lengthDistance_comm (g : RiemannianMetric S) (p q : M) :
    lengthDistance g p q = lengthDistance g q p :=
  congrArg sInf (LengthDistance.pathLengths_symm g p q)

theorem lengthDistance_triangle [PreconnectedSpace M] (g : RiemannianMetric S) (p q r : M) :
    lengthDistance g p r ≤ lengthDistance g p q + lengthDistance g q r :=
  LengthDistance.componentDistance_triangle g p ⟨p,mem_connectedComponent⟩ ⟨q,by simp⟩ ⟨r,by simp⟩

theorem lengthDistance_eq_zero_iff [PreconnectedSpace M] (g : RiemannianMetric S) (p q : M) :
    lengthDistance g p q = 0 ↔ p = q := by
  change componentDistance g p ⟨p,mem_connectedComponent⟩ ⟨q,by simp⟩ = 0 ↔ p = q
  rw [LengthDistance.componentDistance_eq_zero_iff_of_trapping g
    (LengthDistance.local_curve_trapping g)]
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

/-- Compatibility of the source distance balls with the original topology. -/
theorem lengthDistance_isOpen_iff [PreconnectedSpace M] (g : RiemannianMetric S) (U : Set M) :
    IsOpen U ↔ ∀ p ∈ U, ∃ ε > 0, ∀ q, lengthDistance g p q < ε → q ∈ U := by
  constructor
  · intro hU p hp
    obtain ⟨ε,hε,hball⟩ := LengthDistance.componentDistance_lt_mem_of_trapping g
      (LengthDistance.local_curve_trapping g) p ⟨p,mem_connectedComponent⟩ U hU hp
    exact ⟨ε,hε,fun q hq => hball ⟨q,by simp⟩ hq⟩
  · intro h
    apply isOpen_iff_forall_mem_open.mpr
    intro p hp
    obtain ⟨ε,hε,hball⟩ := h p hp
    obtain ⟨V,hV,hpV,hcurves⟩ := LengthDistance.local_short_curves g p ε hε
    refine ⟨V,?_,hV,hpV⟩
    intro q hq
    obtain ⟨a,b,γ,h0,h1,hL⟩ := hcurves q hq
    have hle := lengthDistance_le_length g γ
    rw [h0,h1] at hle
    exact hball q (hle.trans_lt hL)

/-- An actual metric on the original connected manifold, whose topology and
distance are the original topology and the original length infimum. -/
theorem lengthDistance_metric [PreconnectedSpace M] (g : RiemannianMetric S) :
    ∃ d : MetricSpace M,
      d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) ∧
      ∀ p q, @dist _ d.toDist p q = lengthDistance g p q := by
  let d := MetricSpace.ofDistTopology (lengthDistance g) (lengthDistance_self g)
    (lengthDistance_comm g) (lengthDistance_triangle g) (lengthDistance_isOpen_iff g)
    (fun p q => (lengthDistance_eq_zero_iff g p q).mp)
  exact ⟨d,rfl,fun _ _ => rfl⟩


/-- The intrinsic distance is continuous in the original product topology. -/
theorem lengthDistance_continuous [PreconnectedSpace M] (g : RiemannianMetric S) :
    Continuous (fun z : M × M => lengthDistance g z.1 z.2) := by
  obtain ⟨d,htop,hd⟩ := lengthDistance_metric g
  let d' := d.replaceTopology htop.symm
  letI := d'
  have h : Continuous (fun z : M × M => @dist _ d'.toDist z.1 z.2) :=
    continuous_fst.dist continuous_snd
  have heq : (fun z : M × M => @dist _ d'.toDist z.1 z.2) =
      (fun z : M × M => lengthDistance g z.1 z.2) := funext (fun z => hd z.1 z.2)
  exact heq ▸ h

open SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.GeodesicData P202.ExponentialData P202.LeviCivitaData

/-- Every entire radial ray is continuous as an actual curve in M. -/
theorem radial_position_continuous (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p) (v : TangentSpace S p) :
    Continuous (fun t : ℝ => fiberExponential F p (t • v)) := by
  have hdom : univ ⊆ (F.interval ⟨p,v⟩).carrier := by
    rw [full_interval C F hF p hfull v]
  have hc := GeodesicCriticalityCorners.maximal_position_smoothCurveOn C F hF ⟨p,v⟩ hdom
  have heq : (fun t : ℝ => fiberExponential F p (t • v)) =
      (fun t => (F.curve ⟨p,v⟩ t).1) := by
    funext t
    exact (ExponentialNormalCoordinates.radial_identity_at C F hF p v t (hdom (mem_univ t))).2
  rw [heq]
  exact continuousOn_univ.mp hc.1

/-- Reduction of distance attainment to the two geometric facts provided by
the sphere argument: a starting equality and extension of any equality time
strictly before the endpoint distance. Neither fact is assumed in the original
specification. -/
theorem attainment_of_ray_extension [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p)
    (hprop : ∀ q : M, q ≠ p → ∃ (v : TangentSpace S p) (ε : ℝ),
      tangentNorm g p v = 1 ∧ ε ≤ lengthDistance g p q ∧
      lengthDistance g (fiberExponential F p (ε • v)) q = lengthDistance g p q - ε ∧
      ∀ t ∈ Icc ε (lengthDistance g p q), t < lengthDistance g p q →
        lengthDistance g (fiberExponential F p (t • v)) q = lengthDistance g p q - t →
        ∃ s ∈ Ioc t (lengthDistance g p q),
          lengthDistance g (fiberExponential F p (s • v)) q = lengthDistance g p q - s) :
    ∀ q : M, ∃ v : TangentSpace S p,
      fiberExponential F p v = q ∧ tangentNorm g p v = lengthDistance g p q := by
  intro q
  by_cases hq : q = p
  · subst q
    refine ⟨0,(ExponentialNormalCoordinates.zero_section_at C F hF p).2,?_⟩
    rw [SmoothMetrics.tangentNorm_zero,lengthDistance_self]
  obtain ⟨v,ε,hunit,hε,hstart,hstep⟩ := hprop q hq
  let d := lengthDistance g p q
  have hcont : Continuous (fun t : ℝ =>
      lengthDistance g (fiberExponential F p (t • v)) q) :=
    (lengthDistance_continuous g).comp
      ((radial_position_continuous C F hF p hfull v).prodMk continuous_const)
  have hzero := distance_equality_reaches_endpoint hε hcont hstart hstep
  have hend : fiberExponential F p (d • v) = q :=
    (lengthDistance_eq_zero_iff g _ q).mp hzero
  refine ⟨d • v,hend,?_⟩
  rw [SmoothMetrics.tangentNorm_smul,hunit,mul_one,abs_of_nonneg (lengthDistance_nonneg g p q)]


/-- Containment in a ball about any fixed center is exactly metric
boundedness, including for the empty set. -/
theorem bounded_iff_distance_bound {X : Type*} [MetricSpace X] (p : X) (K : Set X) :
    Bornology.IsBounded K ↔ ∃ R : ℝ, ∀ q ∈ K, dist p q ≤ R := by
  rw [Metric.isBounded_iff_subset_closedBall p]
  constructor
  · rintro ⟨R,hR⟩
    refine ⟨R,?_⟩
    intro q hq
    have hmem := hR hq
    simpa only [Metric.mem_closedBall,dist_comm] using hmem
  · rintro ⟨R,hR⟩
    refine ⟨R,?_⟩
    intro q hq
    rw [Metric.mem_closedBall,dist_comm]
    exact hR q hq

/-- Near-infimal competitors exist for the original curve class. -/
theorem short_competitor [PreconnectedSpace M] (g : RiemannianMetric S)
    (p q : M) {r : ℝ} (hr : lengthDistance g p q < r) :
    ∃ a b : ℝ, ∃ c : PiecewiseC1Curve S a b,
      c a = p ∧ c b = q ∧ length g c < r :=
  (LengthDistance.componentDistance_lt_iff g p
    ⟨p, mem_connectedComponent⟩ ⟨q, by simp⟩ r).mp hr

/-- A sufficiently short distance from a normal center has an actual normal
vector of exactly that norm. The escape estimate is applied to a near-infimal
competitor, so this statement includes all global competitors. -/
theorem local_attaining_vector [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) :
    ∃ r > 0, ∀ q : M, lengthDistance g p q < r →
      ∃ v : TangentSpace S p, fiberExponential F p v = q ∧
        tangentNorm g p v = lengthDistance g p q ∧
        (⟨p,v⟩ : Phase S) ∈ exponentialDomain F := by
  obtain ⟨E,r,R,d,hE,hr,hrR,hd,hmin⟩ :=
    NormalMinimality.normal_minimality S g C hC F hF p
  refine ⟨r,hr,?_⟩
  intro q hq
  obtain ⟨a,b,c,h0,h1,hL⟩ := short_competitor g p q hq
  have hstay := NormalMinimality.normal_chart_short_curve_stays
    g C hC F hF p E r R d hd hr hrR c h0 hL
  have hqs : q ∈ d.source := h1 ▸ hstay b ⟨c.ordered,le_rfl⟩
  let v := E.symm (d q).val
  obtain ⟨hvR,hv⟩ := NormalMinimality.normal_chart_inverse g F p E R d hd q hqs
  have hvbound := NormalMinimality.normal_chart_comparison
    g C hC F hF p E R d hd v hvR c h0 (h1.trans hv.symm) hstay
  have hvr : tangentNorm g p v < r := hvbound.trans_lt hL
  have hdist := (hmin v hvr).2.1
  obtain ⟨hqcomp,heq⟩ := hdist
  refine ⟨v,hv,?_,(NormalMinimality.normal_chart_exp g F p E R d hd v hvR).1⟩
  change tangentNorm g p v = sInf (pathLengths g p q)
  rw [← hv]
  exact heq.symm

/-- Local distance spheres are compact in the original manifold topology.
No full exponential domain at this center is assumed. -/
theorem compact_small_distance_spheres [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) :
    ∃ r > 0, ∀ ε : ℝ, 0 ≤ ε → ε < r →
      IsCompact {q : M | lengthDistance g p q = ε} := by
  obtain ⟨E,r,R,d,hE,hr,hrR,hd,hmin⟩ :=
    NormalMinimality.normal_minimality S g C hC F hF p
  obtain ⟨s,hs,hlocal⟩ := local_attaining_vector g C hC F hF p
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro ε hε hεr
  have hclosed : IsClosed {q : M | lengthDistance g p q = ε} :=
    isClosed_eq ((lengthDistance_continuous g).comp
      (continuous_const.prodMk continuous_id)) continuous_const
  apply (compact_normal_closed_ball g C F hF p E ε R d
    ((lt_of_lt_of_le hεr (min_le_left _ _)).trans hrR) hd).of_isClosed_subset hclosed
  intro q hq
  obtain ⟨v,hv,hn,_⟩ := hlocal q (by
    change lengthDistance g p q = ε at hq
    rw [hq]; exact lt_of_lt_of_le hεr (min_le_right _ _))
  exact ⟨v,by change tangentNorm g p v ≤ ε; rw [hn,hq],hv⟩

/-- Splitting a competitor at a distance-sphere crossing gives the required
approximate bound without any regular or unit-speed reparametrization. -/
theorem approximate_sphere_crossing [PreconnectedSpace M]
    (g : RiemannianMetric S) (p q : M) {r : ℝ}
    (hr : 0 ≤ r) (hrd : r ≤ lengthDistance g p q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : M, lengthDistance g p y = r ∧
      r + lengthDistance g y q ≤ lengthDistance g p q + ε := by
  obtain ⟨a,b,c,h0,h1,hL⟩ := short_competitor g p q (lt_add_of_pos_right _ hε)
  have hc : ContinuousOn (fun t => lengthDistance g p (c t)) (Icc a b) :=
    (lengthDistance_continuous g).comp_continuousOn (continuousOn_const.prodMk c.continuousOn)
  have hrange : r ∈ Icc (lengthDistance g p (c a)) (lengthDistance g p (c b)) := by
    rw [h0,h1,lengthDistance_self]
    exact ⟨hr,hrd⟩
  obtain ⟨t,ht,hrt⟩ := intermediate_value_Icc c.ordered hc hrange
  change lengthDistance g p (c t) = r at hrt
  let cp := PiecewiseCurves.restrict c a t le_rfl ht.1 ht.2
  let cs := PiecewiseCurves.restrict c t b ht.1 ht.2 le_rfl
  have hp := lengthDistance_le_length g cp
  have hs := lengthDistance_le_length g cs
  change lengthDistance g (c a) (c t) ≤ ∫ u in a..t, speed g c u at hp
  change lengthDistance g (c t) (c b) ≤ ∫ u in t..b, speed g c u at hs
  rw [h0,hrt] at hp
  rw [h1] at hs
  have hsi := PiecewiseCurves.speed_integrable g c
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hsi.mono_set (by rw [uIcc_of_le ht.1,uIcc_of_le c.ordered]; exact Icc_subset_Icc_right ht.2))
    (hsi.mono_set (by rw [uIcc_of_le ht.2,uIcc_of_le c.ordered]; exact Icc_subset_Icc_left ht.1))
  refine ⟨c t,hrt,?_⟩
  change (∫ u in a..b, speed g c u) < lengthDistance g p q + ε at hL
  linarith

/-- The compact-sphere argument in the source, at any center. -/
theorem small_sphere_distance_split [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p q : M)
    (hpq : p ≠ q) :
    ∃ (r : ℝ) (v : TangentSpace S p), 0 < r ∧ r < lengthDistance g p q ∧
      tangentNorm g p v = r ∧
      (⟨p,v⟩ : Phase S) ∈ exponentialDomain F ∧
      lengthDistance g (fiberExponential F p v) q = lengthDistance g p q - r := by
  obtain ⟨r₀,hr₀,hcompact⟩ := compact_small_distance_spheres g C hC F hF p
  obtain ⟨s,hs,hlocal⟩ := local_attaining_vector g C hC F hF p
  have hd : 0 < lengthDistance g p q := lt_of_le_of_ne (lengthDistance_nonneg g p q)
    (fun h => hpq ((lengthDistance_eq_zero_iff g p q).mp h.symm))
  obtain ⟨r,hr,hrlim⟩ := exists_between (lt_min (lt_min hr₀ hs) hd)
  have hrr₀ : r < r₀ := (hrlim.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hrs : r < s := (hrlim.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  have hrd : r < lengthDistance g p q := hrlim.trans_le (min_le_right _ _)
  let K := {y : M | lengthDistance g p y = r}
  have hK : IsCompact K := hcompact r hr.le hrr₀
  have hne : K.Nonempty := by
    obtain ⟨y,hy,_⟩ := approximate_sphere_crossing g p q hr.le hrd.le (by norm_num : (0:ℝ) < 1)
    exact ⟨y,hy⟩
  have hcont : ContinuousOn (fun y : M => lengthDistance g y q) K :=
    ((lengthDistance_continuous g).comp (continuous_id.prodMk continuous_const)).continuousOn
  obtain ⟨y,hy,hbest⟩ := hK.exists_isMinOn hne hcont
  have hsplit : lengthDistance g p q = r + lengthDistance g y q := by
    apply le_antisymm
    · have htri := lengthDistance_triangle g p y q
      change lengthDistance g p y = r at hy
      rwa [hy] at htri
    · apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨z,hz,hbound⟩ := approximate_sphere_crossing g p q hr.le hrd.le hε
      have hle : lengthDistance g y q ≤ lengthDistance g z q := hbest hz
      linarith
  obtain ⟨v,hv,hn,hdom⟩ := hlocal y (by change lengthDistance g p y = r at hy; rw [hy]; exact hrs)
  refine ⟨r,v,hr,hrd,hn.trans hy,hdom,?_⟩
  rw [hv]
  linarith


/-- A positive splitting radius provides a unit radial direction and the
starting distance equality in the Hopf–Rinow propagation argument. -/
theorem ray_start [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p q : M) (hpq : q ≠ p) :
    ∃ (v : TangentSpace S p) (ε : ℝ), tangentNorm g p v = 1 ∧
      0 < ε ∧ ε < lengthDistance g p q ∧
      lengthDistance g (fiberExponential F p (ε • v)) q = lengthDistance g p q - ε := by
  obtain ⟨ε,w,hε,hεd,hn,hdom,heq⟩ :=
    small_sphere_distance_split g C hC F hF p q (Ne.symm hpq)
  refine ⟨ε⁻¹ • w,ε,?_,hε,hεd,?_⟩
  · rw [SmoothMetrics.tangentNorm_smul,hn,abs_of_pos (inv_pos.mpr hε)]
    exact inv_mul_cancel₀ (ne_of_gt hε)
  · have hscale : ε • (ε⁻¹ • w) = w := by
      rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hε),one_smul]
    simpa only [hscale] using heq

/-- A short exponential vector can be represented at unit speed on any
translated time interval. Only that vector's time-one existence is used. -/
theorem shifted_unit_segment
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (x : M) (w : TangentSpace S x)
    (δ t : ℝ) (hδ : 0 < δ) (hw : tangentNorm g x w = δ)
    (hdom : (⟨x,w⟩ : Phase S) ∈ exponentialDomain F) :
    ∃ (J : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
      (γ : PiecewiseC1Curve S t (t+δ)),
      IsGeodesicOn S C J.carrier q ∧ Icc t (t+δ) ⊆ J.carrier ∧
      q t = (⟨x,δ⁻¹ • w⟩ : Phase S) ∧
      (q (t+δ)).1 = fiberExponential F x w ∧
      (∀ s ∈ J.carrier, tangentNorm g (q s).1 (q s).2 = 1) ∧
      (∀ s : ℝ, γ s = (q s).1) ∧ length g γ = δ := by
  let I := F.interval ⟨x,w⟩
  let J := GeodesicIVP.affineInterval I δ⁻¹ (-(δ⁻¹*t))
    (inv_ne_zero (ne_of_gt hδ))
  let q := affineCurve S (F.curve ⟨x,w⟩) δ⁻¹ (-(δ⁻¹*t))
  have hgeo : IsGeodesicOn S C J.carrier q :=
    GeodesicIVP.geodesic_affine C δ⁻¹ (-(δ⁻¹*t)) (hF ⟨x,w⟩).2.2.1
  have htime0 : δ⁻¹*t + -(δ⁻¹*t) = 0 := by ring
  have htime1 : δ⁻¹*(t+δ) + -(δ⁻¹*t) = 1 := by
    calc
      _ = δ⁻¹ * δ := by ring
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hδ)
  have hbase : Icc (0 : ℝ) 1 ⊆ I.carrier :=
    (F.interval ⟨x,w⟩).ordConnected.out (hF ⟨x,w⟩).1 hdom
  have hJ : Icc t (t+δ) ⊆ J.carrier := by
    intro s hs
    apply hbase
    change δ⁻¹*s + -(δ⁻¹*t) ∈ Icc (0:ℝ) 1
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hs.1 (inv_pos.mpr hδ).le
      linarith
    · have hmul := mul_le_mul_of_nonneg_left hs.2 (inv_pos.mpr hδ).le
      linarith
  have hqt : q t = (⟨x,δ⁻¹ • w⟩ : Phase S) := by
    change (⟨(F.curve ⟨x,w⟩ (δ⁻¹*t + -(δ⁻¹*t))).1,
      δ⁻¹ • (F.curve ⟨x,w⟩ (δ⁻¹*t + -(δ⁻¹*t))).2⟩ : Phase S) = _
    rw [htime0,(hF ⟨x,w⟩).2.1]
  have hunit0 : tangentNorm g (q t).1 (q t).2 = 1 := by
    have hn := congrArg (fun z : Phase S => tangentNorm g z.1 z.2) hqt
    rw [hn,SmoothMetrics.tangentNorm_smul,hw,abs_of_pos (inv_pos.mpr hδ)]
    exact inv_mul_cancel₀ (ne_of_gt hδ)
  have hunit : ∀ s ∈ J.carrier, tangentNorm g (q s).1 (q s).2 = 1 := by
    intro s hs
    exact (GeodesicIVP.constant_speed S g C hC J q hgeo s hs t
      (hJ ⟨le_rfl,by linarith⟩)).trans hunit0
  let γ := geodesicRepresentative C J q hgeo (a := t) (b := t+δ) (by linarith) hJ
  refine ⟨J,q,γ,hgeo,hJ,hqt,?_,hunit,fun _ => rfl,?_⟩
  · change (F.curve ⟨x,w⟩ (δ⁻¹*(t+δ) + -(δ⁻¹*t))).1 = _
    rw [htime1]
    rfl
  · have hlen := GeodesicCriticalityCorners.geodesic_piece_length_of_eqOn g C hC J q hgeo
      (a := t) (b := t+δ) (by linarith) hJ γ (fun _ _ => rfl)
    change (∫ s in t..(t+δ), speed g γ s) = δ
    rw [hlen,hunit0]
    ring


/-- Two adjacent unit-speed geodesics with minimizing total length have
identical phases at their join. This specializes the finite no-corner theorem. -/
theorem minimizing_two_geodesics_phase_match [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (I J : D13Unified.OpenTimeInterval)
    (q r : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    (hr : IsGeodesicOn S C J.carrier r) {t δ : ℝ}
    (ht : 0 < t) (hδ : 0 < δ)
    (hdomq : Icc 0 t ⊆ I.carrier) (hdomr : Icc t (t+δ) ⊆ J.carrier)
    (hmeet : (q t).1 = (r t).1)
    (hunitq : tangentNorm g (q t).1 (q t).2 = 1)
    (hunitr : tangentNorm g (r t).1 (r t).2 = 1)
    (hdist0 : lengthDistance g (q 0).1 (q t).1 = t)
    (hdist1 : lengthDistance g (q 0).1 (r (t+δ)).1 = t+δ) : q t = r t := by
  have hqt : t ∈ I.carrier := hdomq ⟨ht.le,le_rfl⟩
  have hq0 : (0:ℝ) ∈ I.carrier := hdomq ⟨le_rfl,ht.le⟩
  let c := geodesicRepresentative C I q hq ht.le hdomq
  let d := geodesicRepresentative C J r hr (by linarith : t ≤ t+δ) hdomr
  obtain ⟨γ,hleft,hright,hL⟩ := LengthLaws.concatenation_length g c d hmeet
  have hleft' : EqOn γ (fun s => (q s).1) (Icc 0 t) := hleft
  have hright' : EqOn γ (fun s => (r s).1) (Icc t (t+δ)) := hright
  have hnorm0 : tangentNorm g (q 0).1 (q 0).2 = 1 :=
    (GeodesicIVP.constant_speed S g C hC I q hq 0 hq0 t hqt).trans hunitq
  have hLc : length g c = t := by
    change (∫ s in 0..t, speed g c s) = t
    rw [GeodesicCriticalityCorners.geodesic_piece_length_of_eqOn g C hC I q hq ht hdomq c
      (fun _ _ => rfl),hnorm0]
    ring
  have hLd : length g d = δ := by
    change (∫ s in t..t+δ, speed g d s) = δ
    rw [GeodesicCriticalityCorners.geodesic_piece_length_of_eqOn g C hC J r hr
      (by linarith) hdomr d (fun _ _ => rfl),hunitr]
    ring
  have hLγ : length g γ = t+δ := by rw [hL,hLc,hLd]
  let node : Fin 3 → ℝ := ![0,t,t+δ]
  have hnode : StrictMono node := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [node] at * <;> linarith
  let domains : Fin 2 → D13Unified.OpenTimeInterval := ![I,J]
  let phases : Fin 2 → ℝ → Phase S := ![q,r]
  have hgeos : ∀ i, IsGeodesicOn S C (domains i).carrier (phases i) := by
    intro i
    fin_cases i
    · exact hq
    · exact hr
  have hdomains : ∀ i : Fin 2,
      Icc (node i.castSucc) (node i.succ) ⊆ (domains i).carrier := by
    intro i
    fin_cases i
    · exact hdomq
    · exact hdomr
  have hpieces : ∀ i : Fin 2, EqOn γ (fun s => (phases i s).1)
      (Icc (node i.castSucc) (node i.succ)) := by
    intro i
    fin_cases i
    · exact hleft'
    · exact hright'
  have hnonconstant : ∀ i : Fin 2, ∃ s ∈ Icc (node i.castSucc) (node i.succ),
      ∃ u ∈ Icc (node i.castSucc) (node i.succ), (phases i s).1 ≠ (phases i u).1 := by
    intro i
    fin_cases i
    · change ∃ s ∈ Icc (0:ℝ) t, ∃ u ∈ Icc (0:ℝ) t, (q s).1 ≠ (q u).1
      refine ⟨0,⟨le_rfl,ht.le⟩,t,⟨ht.le,le_rfl⟩,?_⟩
      intro heq
      have hz := (lengthDistance_eq_zero_iff g _ _).mpr heq
      linarith
    · change ∃ s ∈ Icc t (t+δ), ∃ u ∈ Icc t (t+δ), (r s).1 ≠ (r u).1
      refine ⟨t,⟨le_rfl,by linarith⟩,t+δ,⟨by linarith,le_rfl⟩,?_⟩
      intro heq
      have hx : (q t).1 = (r (t+δ)).1 := hmeet.trans heq
      rw [← hx] at hdist1
      linarith
  have hminimal : (∫ s in node 0..node (Fin.last 2), speed g γ s) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last 2))) := by
    change length g γ = endpointDistance g (γ 0) (γ (t+δ))
    rw [hLγ,endpointDistance_eq_lengthDistance,
      hleft' ⟨le_rfl,ht.le⟩,hright' ⟨by linarith,le_rfl⟩,hdist1]
  have hcorner := GeodesicCriticalityCorners.minimizing_broken_geodesic_no_corner
    g C hC γ node hnode domains phases hgeos hdomains hpieces hnonconstant hminimal (0 : Fin 1)
  change unitVelocity g (fun z : ℝ × ℝ => γ z.2) 0 t t =
    unitVelocity g (fun z : ℝ × ℝ => γ z.2) t (t+δ) t at hcorner
  have hvelq := GeodesicCriticalityCorners.unitVelocity_heq_of_eqOn g
    (F := fun z : ℝ × ℝ => γ z.2) (G := fun z : ℝ × ℝ => (q z.2).1) ht
    (t := t) ⟨ht.le,le_rfl⟩ hleft'
  have hvelr := GeodesicCriticalityCorners.unitVelocity_heq_of_eqOn g
    (F := fun z : ℝ × ℝ => γ z.2) (G := fun z : ℝ × ℝ => (r z.2).1) (by linarith : t < t+δ)
    (t := t) ⟨le_rfl,by linarith⟩ hright'
  have hvel : HEq (unitVelocity g (fun z : ℝ × ℝ => (q z.2).1) 0 t t)
      (unitVelocity g (fun z : ℝ × ℝ => (r z.2).1) t (t+δ) t) :=
    hvelq.symm.trans ((heq_of_eq hcorner).trans hvelr)
  rw [GeodesicCriticalityCorners.geodesic_segment_unitVelocity_eq g C I q hq ht hdomq ⟨ht.le,le_rfl⟩,
    GeodesicCriticalityCorners.geodesic_segment_unitVelocity_eq g C J r hr (by linarith) hdomr ⟨le_rfl,by linarith⟩,
    hunitq,hunitr,inv_one,one_smul,one_smul] at hvel
  exact Sigma.ext hmeet hvel

/-- The no-corner argument extends each positive equality time along the
same complete radial ray. Completeness is used only at the initial center. -/
theorem ray_distance_equality_extension [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p)
    (q : M) (v : TangentSpace S p) (hunit : tangentNorm g p v = 1)
    (t : ℝ) (ht : 0 < t) (htq : t < lengthDistance g p q)
    (heq : lengthDistance g (fiberExponential F p (t • v)) q = lengthDistance g p q - t) :
    ∃ s ∈ Ioc t (lengthDistance g p q),
      lengthDistance g (fiberExponential F p (s • v)) q = lengthDistance g p q - s := by
  let ρ := F.curve ⟨p,v⟩
  let I := F.interval ⟨p,v⟩
  have hρ : IsGeodesicOn S C I.carrier ρ := (hF ⟨p,v⟩).2.2.1
  have hI : I.carrier = univ := full_interval C F hF p hfull v
  have hmem (s : ℝ) : s ∈ I.carrier := by rw [hI]; trivial
  have hinit : ρ 0 = (⟨p,v⟩ : Phase S) := (hF ⟨p,v⟩).2.1
  have hρ0 : (ρ 0).1 = p := congrArg Sigma.fst hinit
  have hrad (s : ℝ) : fiberExponential F p (s • v) = (ρ s).1 :=
    (ExponentialNormalCoordinates.radial_identity_at C F hF p v s (hmem s)).2
  let x := fiberExponential F p (t • v)
  have hx : x ≠ q := by
    intro h
    have hz : lengthDistance g x q = 0 := by rw [h,lengthDistance_self]
    change lengthDistance g x q = lengthDistance g p q - t at heq
    linarith
  obtain ⟨δ,w,hδ,hδq,hw,hwdom,hsplit⟩ := small_sphere_distance_split g C hC F hF x q hx
  obtain ⟨J,r,γ,hr,hJ,hrt,hend,hrunit,htrace,hL⟩ :=
    shifted_unit_segment g C hC F hF x w δ t hδ hw hwdom
  have hrtx := congrArg (fun z : Phase S => z.1) hrt
  change (r t).1 = x at hrtx
  have hbound : lengthDistance g x (fiberExponential F x w) ≤ δ := by
    have h := lengthDistance_le_length g γ
    rw [htrace t,htrace (t+δ),hrtx,hend,hL] at h
    exact h
  have hpt : lengthDistance g p x = t := by
    have hupp := distance_exponential_le_norm g C hC F hF p hfull (t • v)
    rw [SmoothMetrics.tangentNorm_smul,hunit,mul_one,abs_of_pos ht] at hupp
    have hlo := lengthDistance_triangle g p x q
    change lengthDistance g x q = lengthDistance g p q - t at heq
    exact le_antisymm hupp (by linarith)
  have hpz : lengthDistance g p (fiberExponential F x w) = t+δ := by
    have hupp := lengthDistance_triangle g p x (fiberExponential F x w)
    have hlo := lengthDistance_triangle g p (fiberExponential F x w) q
    rw [hpt] at hupp
    change lengthDistance g x q = lengthDistance g p q - t at heq
    exact le_antisymm (by linarith) (by linarith)
  have hdomρ : Icc (0:ℝ) t ⊆ I.carrier := fun s _ => hmem s
  have hunitρ : tangentNorm g (ρ t).1 (ρ t).2 = 1 := by
    have hu0 := congrArg (fun z : Phase S => tangentNorm g z.1 z.2) hinit
    exact (GeodesicIVP.constant_speed S g C hC I ρ hρ t (hmem t) 0 (hmem 0)).trans
      (hu0.trans hunit)
  have hmeet : (ρ t).1 = (r t).1 := (hrad t).symm.trans hrtx.symm
  have hdist0 : lengthDistance g (ρ 0).1 (ρ t).1 = t := by
    rw [hρ0,← hrad t]
    exact hpt
  have hdist1 : lengthDistance g (ρ 0).1 (r (t+δ)).1 = t+δ := by
    rw [hρ0,hend]
    exact hpz
  have hphase : ρ t = r t := minimizing_two_geodesics_phase_match
    g C hC I J ρ r hρ hr ht hδ hdomρ hJ hmeet hunitρ
      (hrunit t (hJ ⟨le_rfl,by linarith⟩)) hdist0 hdist1
  have hequal := GeodesicIVP.overlap_unique S C I J ρ r hρ hr t
    ⟨hmem t,hJ ⟨le_rfl,by linarith⟩⟩ hphase
  have hpoint : fiberExponential F p ((t+δ) • v) = fiberExponential F x w :=
    (hrad (t+δ)).trans ((congrArg Sigma.fst
      (hequal ⟨hmem (t+δ),hJ ⟨by linarith,le_rfl⟩⟩)).trans hend)
  have htd : t+δ < lengthDistance g p q := by
    change lengthDistance g x q = lengthDistance g p q - t at heq
    linarith
  refine ⟨t+δ,⟨by linarith,htd.le⟩,?_⟩
  rw [hpoint,hsplit]
  change lengthDistance g x q = lengthDistance g p q - t at heq
  linarith


/-- Every endpoint is attained at precisely its distance, using a full
exponential map at this one center only. -/
theorem attaining_vectors [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p) :
    ∀ q : M, ∃ v : TangentSpace S p,
      fiberExponential F p v = q ∧ tangentNorm g p v = lengthDistance g p q := by
  apply attainment_of_ray_extension g C F hF p hfull
  intro q hq
  obtain ⟨v,ε,hunit,hε,hεd,hstart⟩ := ray_start g C hC F hF p q hq
  refine ⟨v,ε,hunit,hεd.le,hstart,?_⟩
  intro t ht htd heq
  exact ray_distance_equality_extension g C hC F hF p hfull q v hunit t
    (hε.trans_le ht.1) htd heq

/-- The single-center exponential implication of Hopf–Rinow, including
minimizing geodesics, the exact closed-ball image, and properness. -/
theorem complete_exponential_minimizers :
    P202Specs.Geometry.CompleteExponentialMinimizers.complete_exponential_minimizersType.{u} := by
  intro n M _ _ S g C hC F hF p hfull
  exact conclusions_of_vectors g C hC F hF p hfull
    (attaining_vectors g C hC F hF p hfull)

end P202.Geometry.CompleteExponentialMinimizers
