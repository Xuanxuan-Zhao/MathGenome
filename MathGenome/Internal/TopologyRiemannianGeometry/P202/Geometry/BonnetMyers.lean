import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.BonnetMyers
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MyersDiameterCompact
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CoveringMetricCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SubgroupCoverConstruction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.Monodromy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.EuclideanLineGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.EuclideanLineDistance
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.BonnetMyers
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MapData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData
  P202.CurvatureData P202.RicciData P202.MyersData
  P202.CompletenessData P202.CoveringMetricData P202.CompleteExponentialData
  P202Specs.Topology
open Set Filter
open scoped _root_.Topology
universe u

/-- Euclidean chart balls give the original source's semilocal simple
connectivity hypothesis. No simple connectivity of the manifold is assumed. -/
theorem manifold_semilocallySimplyConnected {n : ℕ} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n .euclidean M) :
    SemilocallySimplyConnected M := by
  intro x
  let c := SmoothManifolds.TopologicalManifold.chartAt S.topologicalManifold x
  let e := c.transHomeomorph (Homeomorph.Set.univ (Euclidean n))
  have hx : x ∈ e.source := SmoothManifolds.TopologicalManifold.mem_chartAt_source S.topologicalManifold x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let V := Metric.ball (e x) r
  let U := e.symm '' V
  have hV : V ⊆ e.symm.source := hball
  have hopen : IsOpen U := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hV
  have hxU : x ∈ U := ⟨e x, Metric.mem_ball_self hr, e.left_inv hx⟩
  haveI : ContractibleSpace V := (convex_ball (e x) r).contractibleSpace
    ⟨e x, Metric.mem_ball_self hr⟩
  let h := e.symm.homeomorphOfImageSubsetSource hV (rfl : e.symm '' V = U)
  haveI : ContractibleSpace U := h.symm.contractibleSpace
  have hsc : IsSimplyConnected U := (inferInstance : SimplyConnectedSpace U)
  refine ⟨U, hopen, hxU, ?_⟩
  intro a ha
  obtain ⟨F, _⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hsc).2 x a ha
  exact congrArg ofClass (Path.Homotopic.Quotient.eq.mpr ⟨F⟩)

/-- Closed discrete fibers in a compact total space are finite. -/
theorem finite_covering_fiber {E B : Type u} [TopologicalSpace E]
    [TopologicalSpace B] [T1Space B] (p : E → B) (hp : Covering p)
    (hE : IsCompact (univ : Set E)) (b : B) : Finite (Fiber p b) := by
  letI : CompactSpace E := ⟨hE⟩
  have hc := P202.Topology.covering_to_library hp
  haveI : CompactSpace (Fiber p b) := isCompact_iff_compactSpace.mp (isClosed_singleton.preimage hc.continuous).isCompact
  haveI : DiscreteTopology (Fiber p b) := (hc b).discreteTopology_fiber
  exact finite_of_compact_of_discrete

/-- In the actual trivial-subgroup cover, the endpoint action identifies the
fiber with the canonical fundamental-group set. -/
theorem universal_fiber_equiv {M : Type u} [TopologicalSpace M]
    [PathConnectedSpace M] [LocallyPathConnectedSpace M]
    (hs : SemilocallySimplyConnected M) (b : M) :
    Nonempty (Pi1 M b ≃ Fiber
      (SubgroupCover.endpoint (⊥ : Subgroup (Pi1 M b))) b) := by
  let H : Subgroup (Pi1 M b) := ⊥
  let E := SubgroupCover b H
  let p : C(E, M) := ⟨SubgroupCover.endpoint H,
    P202.Topology.SubgroupCoverConstruction.endpoint_continuous H hs⟩
  have hp : Covering p := P202.Topology.SubgroupCoverConstruction.covering M hs b H
  letI : PathConnectedSpace E := P202.Topology.SubgroupCoverConstruction.pathConnected M hs b H
  let e : Fiber p b := ⟨SubgroupCover.basepoint H, rfl⟩
  have he : fiberSubgroup p b e = ⊥ :=
    P202.Topology.SubgroupCoverConstruction.imageSubgroup M hs b H p.continuous
  have hbij : Function.Bijective (fiberAction p b e) := by
    constructor
    · intro g h hh
      have hg := (P202.Topology.fiberAction_eq_iff hp b e g h).mp hh
      rw [QuotientGroup.rightRel_apply, he] at hg
      exact (mul_inv_eq_one.mp hg).symm
    · intro y
      exact P202.Topology.monodromyTransitive E M p hp b e y
  exact ⟨Equiv.ofBijective _ hbij⟩

/-- Curvature is intertwined by the differential of a local isometry.
Global fields are used only as representatives of local germs. -/
theorem localIsometry_curvature {n : ℕ} {E B : Type u}
    [TopologicalSpace E] [TopologicalSpace B]
    {T : SmoothManifold n .euclidean E} {S : SmoothManifold n .euclidean B}
    (h : RiemannianMetric T) (g : RiemannianMetric S)
    (D : Connection (tangentBundle T)) (C : Connection (tangentBundle S))
    (hD : IsLeviCivita h D) (hC : IsLeviCivita g C)
    (Q : CurvatureTensor T) (R : CurvatureTensor S)
    (hQ : RepresentsCurvature D Q) (hR : RepresentsCurvature C R)
    (p : E → B) (hi : IsLocalIsometry h g p) (x : E)
    (u v w : TangentSpace T x) :
    SmoothManifolds.differential T S p hi.1.1 x (Q.val x u v w) =
      R.val (p x) (SmoothManifolds.differential T S p hi.1.1 x u)
        (SmoothManifolds.differential T S p hi.1.1 x v)
        (SmoothManifolds.differential T S p hi.1.1 x w) := by
  let L := SmoothManifolds.differential T S p hi.1.1
  have hL := SmoothManifolds.differential_spec T S p hi.1.1
  obtain ⟨A, hA, hmA⟩ := hi.2
  have hAL : A = L := by
    funext q
    exact (SmoothManifolds.differential_exists T S p hi.1.1 q).unique (hA q) (hL q)
  have hm : IsMetricPreserving h g p L := hAL ▸ hmA
  let X := CurvatureAlgebra.fieldLift (S := T) x u
  let Y := CurvatureAlgebra.fieldLift (S := T) x v
  let Z := CurvatureAlgebra.fieldLift (S := T) x w
  obtain ⟨X', hX⟩ := LeviCivita.exists_related_germ p hi.1 L hL X x
  obtain ⟨Y', hY⟩ := LeviCivita.exists_related_germ p hi.1 L hL Y x
  obtain ⟨Z', hZ⟩ := LeviCivita.exists_related_germ p hi.1 L hL Z x
  have hcov (U V : Field T) (U' V' : Field S)
      (hU : ∀ᶠ q in 𝓝 x, L q (U.val q) = U'.val (p q))
      (hV : ∀ᶠ q in 𝓝 x, L q (V.val q) = V'.val (p q)) :
      ∀ᶠ q in 𝓝 x, L q ((D.cov U V).val q) = (C.cov U' V').val (p q) := by
    filter_upwards [hU.eventually_nhds, hV.eventually_nhds] with q hUq hVq
    exact LeviCivita.connection_related_at TorsionAndMetric.torsion_apply
      p hi.1 L hL h g hm D C hD hC U V U' V' q hUq hVq
  have hbr : ∀ᶠ q in 𝓝 x,
      L q ((P202.TorsionMetricData.bracket X Y).val q) =
        (P202.TorsionMetricData.bracket X' Y').val (p q) := by
    filter_upwards [hX.eventually_nhds, hY.eventually_nhds] with q hXq hYq
    exact LeviCivita.bracket_related_at p hi.1.1 L hL X Y X' Y' q hXq hYq
  have hXYZ := (hcov X (D.cov Y Z) X' (C.cov Y' Z') hX (hcov Y Z Y' Z' hY hZ)).self_of_nhds
  have hYXZ := (hcov Y (D.cov X Z) Y' (C.cov X' Z') hY (hcov X Z X' Z' hX hZ)).self_of_nhds
  have hbrZ := (hcov (P202.TorsionMetricData.bracket X Y) Z
    (P202.TorsionMetricData.bracket X' Y') Z' hbr hZ).self_of_nhds
  have hcurv : L x ((curvature D X Y Z).val x) =
      (curvature C X' Y' Z').val (p x) := by
    simp only [P202.CurvatureData.curvature, ConnectionForms.section_add_apply,
      ConnectionForms.section_smul_apply, map_add, map_smul, hXYZ, hYXZ, hbrZ]
  have hx : X.val x = u := CurvatureAlgebra.fieldLift_value x u
  have hy : Y.val x = v := CurvatureAlgebra.fieldLift_value x v
  have hz : Z.val x = w := CurvatureAlgebra.fieldLift_value x w
  have hpx : X'.val (p x) = L x u := by rw [← hX.self_of_nhds, hx]
  have hpy : Y'.val (p x) = L x v := by rw [← hY.self_of_nhds, hy]
  have hpz : Z'.val (p x) = L x w := by rw [← hZ.self_of_nhds, hz]
  rw [← hQ X Y Z x, ← hR X' Y' Z' (p x), hx, hy, hz, hpx, hpy, hpz] at hcurv
  exact hcurv

/-- Ricci naturality follows by conjugating the contracted endomorphism.
The trace is the original trace on the derivation tangent spaces. -/
theorem localIsometry_ricci :
    P202Specs.Geometry.BonnetMyers.localIsometry_ricciType.{u} := by
  intro n E B _ _ T S h g D C hD hC Q R hQ hR p hi x v w
  letI : AddCommGroup (TangentSpace T x) := Module.addCommMonoidToAddCommGroup ℝ
  letI : AddCommGroup (TangentSpace S (p x)) := Module.addCommMonoidToAddCommGroup ℝ
  let L := SmoothManifolds.differential T S p hi.1.1
  obtain ⟨e, he⟩ := SmoothManifolds.Tensors.local_diffeomorphism_differential T S p hi.1
  have heL : (e x).toLinearMap = L x :=
    (SmoothManifolds.differential_exists T S p hi.1.1 x).unique (he x)
      (SmoothManifolds.differential_spec T S p hi.1.1 x)
  let A : TangentSpace T x →ₗ[ℝ] TangentSpace T x :=
    { toFun := fun u => Q.val x u v w
      map_add' := by intros; simp only [map_add, LinearMap.add_apply]
      map_smul' := by intros; simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  let B' : TangentSpace S (p x) →ₗ[ℝ] TangentSpace S (p x) :=
    { toFun := fun u => R.val (p x) u (L x v) (L x w)
      map_add' := by intros; simp only [map_add, LinearMap.add_apply]
      map_smul' := by intros; simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hab : (e x).conj A = B' := by
    apply LinearMap.ext
    intro z
    change (e x) (Q.val x ((e x).symm z) v w) = R.val (p x) z (L x v) (L x w)
    have hh := localIsometry_curvature h g D C hD hC Q R hQ hR p hi x ((e x).symm z) v w
    change L x _ = _ at hh
    have hz : L x ((e x).symm z) = z := by
      rw [← heL]
      exact (e x).apply_symm_apply z
    rw [hz] at hh
    change (e x).toLinearMap _ = _
    rw [heL]
    exact hh
  change LinearMap.trace ℝ (TangentSpace T x) A =
    LinearMap.trace ℝ (TangentSpace S (p x)) B'
  rw [← hab]
  exact (LinearMap.trace_conj' A (e x)).symm



/-- Ricci lower bounds pass to any local isometry; the normalization uses
exactly the same dimension and the same positive constant. -/
theorem localIsometry_ricciLowerBound {n : ℕ} {E B : Type u}
    [TopologicalSpace E] [TopologicalSpace B]
    {T : SmoothManifold n .euclidean E} {S : SmoothManifold n .euclidean B}
    (h : RiemannianMetric T) (g : RiemannianMetric S)
    (D : Connection (tangentBundle T)) (C : Connection (tangentBundle S))
    (hD : IsLeviCivita h D) (hC : IsLeviCivita g C)
    (Q : CurvatureTensor T) (R : CurvatureTensor S)
    (hQ : RepresentsCurvature D Q) (hR : RepresentsCurvature C R)
    (p : E → B) (hi : IsLocalIsometry h g p) (k : ℝ)
    (hk : RicciLowerBound g R k) : RicciLowerBound h Q k := by
  intro x v
  rw [localIsometry_ricci h g D C hD hC Q R hQ hR p hi]
  obtain ⟨L, hL, hmetric⟩ := hi.2
  have hcan : L x = SmoothManifolds.differential T S p hi.1.1 x :=
    (SmoothManifolds.differential_exists T S p hi.1.1 x).unique (hL x)
      (SmoothManifolds.differential_spec T S p hi.1.1 x)
  rw [← hcan, ← hmetric x v v]
  exact hk (p x) (L x v)

/-- Construct the complete pullback metric first, transfer curvature, then
apply the accepted diameter/compactness theorem upstairs. -/
theorem universal_cover : P202Specs.Geometry.BonnetMyers.universal_coverType.{u} := by
  intro n M _ _ S g C hC R hR hn k hk hbound hcomplete b
  letI : T2Space M := S.topologicalManifold.hausdorff
  letI : LocallyPathConnectedSpace M := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  letI : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  have hs := manifold_semilocallySimplyConnected S
  let H : Subgroup (Pi1 M b) := ⊥
  let E := SubgroupCover b H
  let p : E → M := SubgroupCover.endpoint H
  have hp : Covering p := P202.Topology.SubgroupCoverConstruction.covering M hs b H
  letI : PathConnectedSpace E := P202.Topology.SubgroupCoverConstruction.pathConnected M hs b H
  obtain ⟨T, _, hT, _⟩ :=
    CoveringMetricCompleteness.canonical_geometry S g p hp |>.2.2
  obtain ⟨h, hi, hmetric, hcomp⟩ :=
    CoveringMetricCompleteness.covering_complete_connectedBase T S p hT g hcomplete
  obtain ⟨D, hD, _⟩ := LeviCivita.exists_unique h
  obtain ⟨Q, hQ, _⟩ := CurvatureAlgebra.tensor_exists_unique D
  have hbound' := localIsometry_ricciLowerBound h g D C hD hC Q R hQ hR p hi k hbound
  have hcomplete' : LengthMetricComplete h :=
    (CoveringMetricCompleteness.connected_complete_iff h).mp hcomp
  have hcompact := (MyersDiameterCompact.diameter_compact T h D hD Q hQ hn k hk
    hbound' hcomplete').2.2
  exact ⟨T, hT, h, D, Q, hi, hmetric, hD, hQ, hbound', hcomplete', hcompact,
    universal_fiber_equiv hs b, finite_covering_fiber p hp hcompact b⟩

/-- The full dimension-at-least-two Bonnet--Myers conclusion. -/
theorem bonnet_myers : P202Specs.Geometry.BonnetMyers.bonnet_myersType.{u} := by
  intro n M _ _ S g C hC R hR hn k hk hbound hcomplete
  obtain ⟨hdist, hdiam, hcompact⟩ :=
    MyersDiameterCompact.diameter_compact S g C hC R hR hn k hk hbound hcomplete
  refine ⟨hdist, hdiam, hcompact, fun b => ?_⟩
  obtain ⟨T, hp, h, D, Q, hi, hmetric, hD, hQ, hbound', hcomplete', hcompact', ⟨e⟩, hf⟩ :=
    universal_cover S g C hC R hR hn k hk hbound hcomplete b
  letI := hf
  exact Finite.of_injective e e.injective

/-- The standard Euclidean-line example required by paper.tex:4739–4742. -/
theorem euclidean_line : P202Specs.Geometry.BonnetMyers.euclidean_lineType := by
  obtain ⟨S, g, C, R, hchart, hg, hC, hR, hricci, hbound⟩ :=
    EuclideanLineGeometry.euclidean_line_geometry
  obtain ⟨hdist, hcomplete, hunbounded⟩ :=
    EuclideanLineDistance.euclidean_line_distance S g hchart hg
  exact ⟨S, g, C, R, hchart, hg, inferInstance, hcomplete,
    hC, hR, hricci, hbound, hdist, hunbounded⟩

end P202.Geometry.BonnetMyers
