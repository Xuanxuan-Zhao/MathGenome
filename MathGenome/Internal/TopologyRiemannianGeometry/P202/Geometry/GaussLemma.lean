import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GaussLemma
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialNormalCoordinates
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.TorsionAndMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.Geometry.GaussLemma
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.GeodesicData
  P202.LeviCivitaData P202.ExponentialData P202.GaussData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

variable (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
  (hF : IsMaximalFamily S C F)

section RadialCalculus
include C hF

/-- The coordinate function used to define the fiber differential really is
differentiable at every point of the original exponential domain. -/
theorem fiberDifferential_hasFDerivAt (p : M) (v : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F p v ∈ d.source) :
    let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
    let f := fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val
    HasFDerivAt f (fderiv ℝ f (E v)) (E v) := by
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  have h := ExponentialNormalCoordinates.fiberExponential_contDiffAt C F hF
    p e he hp d hd (E v)
    (by simpa only [E, LinearEquiv.symm_apply_apply] using hv)
    (by simpa only [E, LinearEquiv.symm_apply_apply] using hq)
  exact (h.differentiableAt (by simp)).hasFDerivAt

/-- Along a ray the exponential is the original maximal geodesic, even at
singular values of the exponential. This is its radial derivative at time one. -/
theorem radial_curve_derivative (p : M) (v : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F p v ∈ d.source) :
    HasDerivAt (fun t : ℝ => (d (fiberExponential F p (t • v))).val)
      ((tangentStructure S).fiberCoordinates.equiv d hd
        (fiberExponential F p v) hq (F.curve ⟨p, v⟩ 1).2) 1 := by
  have hv1 : 1 ∈ (F.interval ⟨p, v⟩).carrier := hv
  have hvel := ((hF ⟨p, v⟩).2.2.1 1 hv1).1
  have hder := CurveCovariantDerivative.velocity_coordinates hvel (mem_univ 1) d hd hq
  rw [hasDerivWithinAt_univ] at hder
  apply hder.congr_of_eventuallyEq
  filter_upwards [(F.interval ⟨p, v⟩).isOpen.mem_nhds hv1] with t ht
  exact congrArg (fun q : M => (d q).val)
    (ExponentialNormalCoordinates.radial_identity_at C F hF p v t ht).2

/-- The derivative in the radial direction is the actual terminal velocity. -/
theorem fiberDifferential_radial (p : M) (v : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F p v ∈ d.source) :
    fiberDifferential F p v e he hp d hd hq v = (F.curve ⟨p, v⟩ 1).2 := by
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let D := (tangentStructure S).fiberCoordinates.equiv d hd
    (fiberExponential F p v) hq
  let f := fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val
  have hline : HasDerivAt (fun t : ℝ => t • E v) (E v) 1 := by
    simpa only [one_smul, id_eq] using! (hasDerivAt_id (1 : ℝ)).smul_const (E v)
  have hf := fiberDifferential_hasFDerivAt C F hF p v hv e he hp d hd hq
  have hchain := hf.comp_hasDerivAt_of_eq 1 hline (by simp [E])
  have heq : (fun t : ℝ => f (t • E v)) =
      (fun t : ℝ => (d (fiberExponential F p (t • v))).val) := by
    funext t
    simp only [f, map_smul, LinearEquiv.symm_apply_apply]
  change HasDerivAt (fun t : ℝ => f (t • E v)) _ _ at hchain
  rw [heq] at hchain
  have he := hchain.unique (radial_curve_derivative C F hF p v hv d hd hq)
  apply D.injective
  change D (D.symm ((fderiv ℝ f (E v)) (E v))) = _
  simpa only [LinearEquiv.apply_symm_apply] using he

end RadialCalculus

/-- Radial length preservation follows already from geodesic constant speed. -/
theorem radial_length : P202Specs.Geometry.GaussLemma.radial_lengthType.{u} := by
  intro n M _ S g C hC F hF p v hv e he hp d hd hq
  rw [fiberDifferential_radial C F hF p v hv e he hp d hd hq]
  have h := GeodesicIVP.constant_speed S g C hC (F.interval ⟨p, v⟩)
    (F.curve ⟨p, v⟩) (hF ⟨p, v⟩).2.2.1 1 hv 0 (hF ⟨p, v⟩).1
  have hi : F.curve ⟨p, v⟩ 0 = (⟨p, v⟩ : Phase S) := (hF ⟨p, v⟩).2.1
  rw [hi] at h
  exact h

/-- The zero-vector case needs no nonsingularity premise. -/
theorem gauss_lemma_zero (g : RiemannianMetric S) (p : M)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F p 0 ∈ d.source) (w : TangentSpace S p) :
    let L := fiberDifferential F p 0 e he hp d hd hq
    pairing g (fiberExponential F p 0) (L 0) (L w) = pairing g p 0 w := by
  simp only [map_zero, LinearMap.zero_apply]

/-- The initial energy in the variation has precisely the required derivative.
This computation stays in the original tangent fiber and needs no auxiliary
norm or topology on that fiber. -/
theorem initial_squared_speed_derivative (g : RiemannianMetric S) (p : M)
    (v w : TangentSpace S p) :
    HasDerivAt (fun s : ℝ => pairing g p (v + s • w) (v + s • w))
      (2 * pairing g p v w) 0 := by
  let a := pairing g p v v
  let b := pairing g p v w
  let c := pairing g p w w
  have hsym : pairing g p w v = pairing g p v w := g.symmetric p w v
  have heq : (fun s : ℝ => pairing g p (v + s • w) (v + s • w)) =
      (fun s : ℝ => a + (s * b + s * b) + s * s * c) := by
    funext s
    dsimp only [a, b, c]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hsym]
    ring
  rw [heq]
  have hlin : HasDerivAt (fun s : ℝ => s * b) b 0 := by
    simpa only [id_eq, one_mul] using! (hasDerivAt_id (0 : ℝ)).mul_const b
  have hquad : HasDerivAt (fun s : ℝ => s * s * c) 0 0 := by
    simpa only [Pi.mul_apply, id_eq, mul_zero, zero_mul, add_zero] using!
      ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const c
  convert ((hasDerivAt_const (0 : ℝ) a).add (hlin.add hlin)).add hquad using 1 <;>
    dsimp only [b] <;> ring

/-- The energy identity used in the variation holds on the entire actual
maximal interval, including its initial point. -/
theorem geodesic_squared_speed (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p) (t : ℝ)
    (ht : t ∈ (F.interval ⟨p, v⟩).carrier) :
    pairing g (F.curve ⟨p, v⟩ t).1 (F.curve ⟨p, v⟩ t).2
      (F.curve ⟨p, v⟩ t).2 = pairing g p v v := by
  let I := F.interval ⟨p, v⟩
  let q := F.curve ⟨p, v⟩
  let h : ℝ → ℝ := fun s => pairing g (q s).1 (q s).2 (q s).2
  have hd (s : ℝ) (hs : s ∈ I.carrier) : HasDerivAt h 0 s := by
    have hg := (hF ⟨p, v⟩).2.2.1 s hs
    simpa only [h, map_zero, LinearMap.zero_apply, add_zero] using
      GeodesicIVP.pairing_self_derivative g C hC.2 hg.1 hg.2
  have heq : h t = h 0 := I.isOpen.is_const_of_deriv_eq_zero
    I.ordConnected.isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht (hF ⟨p, v⟩).1
  change pairing g (q t).1 (q t).2 (q t).2 = _
  change pairing g (q t).1 (q t).2 (q t).2 =
    pairing g (q 0).1 (q 0).2 (q 0).2 at heq
  have hi : q 0 = (⟨p, v⟩ : Phase S) := (hF ⟨p, v⟩).2.1
  rw [hi] at heq
  exact heq

/-- The scalar integration step on the actual open interval, including the
initial point. No endpoint regularity needs to be assumed separately. -/
theorem pairing_at_one_of_hasDerivAt
    (I : D13Unified.OpenTimeInterval) (h0 : 0 ∈ I.carrier) (h1 : 1 ∈ I.carrier)
    (h : ℝ → ℝ) (a : ℝ)
    (hd : ∀ t ∈ I.carrier, HasDerivAt h a t) (hz : h 0 = 0) : h 1 = a := by
  have hlin (t : ℝ) : HasDerivAt (fun s : ℝ => s * a) a t := by
    simpa only [id_eq, one_mul] using! (hasDerivAt_id t).mul_const a
  have heq : EqOn h (fun s : ℝ => s * a) I.carrier :=
    I.isOpen.eqOn_of_deriv_eq I.ordConnected.isPreconnected
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t _ => (hlin t).differentiableAt.differentiableWithinAt)
      (fun t ht => (hd t ht).deriv.trans (hlin t).deriv.symm)
      h0 (by simpa only [zero_mul] using hz)
  simpa only [one_mul] using heq h1

/-- The intrinsic geodesic condition at one time depends only on the phase germ. -/
theorem geodesicAt_congr (C : Connection (tangentBundle S))
    {q r : ℝ → Phase S} {t : ℝ} (hqr : q =ᶠ[𝓝 t] r)
    (hq : HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2 ∧
      HasCovariantDerivativeAt C (fun s => (q s).1) (fun s => (q s).2) t 0) :
    HasVelocityWithinAt S (fun s => (r s).1) univ t (r t).2 ∧
      HasCovariantDerivativeAt C (fun s => (r s).1) (fun s => (r s).2) t 0 := by
  have hpoint : q t = r t := hqr.eq_of_nhds
  have hbase : (fun s => (r s).1) =ᶠ[𝓝 t] (fun s => (q s).1) :=
    hqr.symm.fun_comp Sigma.fst
  have hv : HasVelocityWithinAt S (fun s => (r s).1) univ t (r t).2 := by
    rcases hq.1 with ⟨hc, e, he, hp, hd⟩
    have hcont : ContinuousAt (fun s => (r s).1) t :=
      ((continuousWithinAt_univ _ _).mp hc).congr_of_eventuallyEq hbase
    let V : Phase S → Prop := fun w => ∃ e, ∃ he : e ∈ S.smoothStructure.val,
      ∃ hp : w.1 ∈ e.source,
        HasDerivWithinAt (fun s => (e (r s).1).val)
          ((tangentStructure S).fiberCoordinates.equiv e he w.1 hp w.2) univ t
    have hV : V (q t) := by
      refine ⟨e, he, hp, ?_⟩
      exact hd.congr_of_eventuallyEq_of_mem
        ((hbase.fun_comp (fun p => (e p).val)).filter_mono (nhdsWithin_le_nhds))
        (mem_univ t)
    have hV' : V (r t) := hpoint ▸ hV
    exact ⟨(continuousWithinAt_univ _ _).mpr hcont, hV'⟩
  refine ⟨hv, ?_⟩
  rcases hq.2 with ⟨V, hV, U, hU, b, hp, v', hd, hz⟩
  have hVeq : V = (q t).2 := CurveCovariantDerivative.velocity_unique
    (mem_univ t) uniqueDiffWithinAt_univ hV hq.1
  subst V
  have hcoef : coefficientsAlong b (fun s => (r s).1) (fun s => (r s).2) =ᶠ[𝓝 t]
      coefficientsAlong b (fun s => (q s).1) (fun s => (q s).2) := by
    filter_upwards [hqr] with s hs
    exact congrArg (fun w : Phase S => coefficientsAlong b (fun _ => w.1) (fun _ => w.2) t) hs.symm
  let A : Phase S → Prop := fun w => ∃ hp : w.1 ∈ U,
    (0 : TangentSpace S w.1) =
      frameDerivative C b (fun _ => w.1) (fun _ => w.2) t hp w.2 v'
  have hA : A (q t) := ⟨hp, hz⟩
  obtain ⟨hp', hz'⟩ : A (r t) := hpoint ▸ hA
  exact ⟨(r t).2, hv, U, hU, b, hp', v',
    hd.congr_of_eventuallyEq_of_mem
      (hcoef.filter_mono nhdsWithin_le_nhds) (mem_univ t), hz'⟩


section Variation
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  P202.TorsionMetricData
variable {N : Type u} [TopologicalSpace N]
  {R : SmoothManifold 2 .euclidean N}

/-- The local first-variation identity before integration. It applies to
arbitrary-rank smooth surfaces in a Riemannian manifold; geodesicity is only
needed to remove the explicitly displayed acceleration term. -/
theorem variation_pairing_identity
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C)
    (e : ModelChart 2 .euclidean N) (he : e ∈ R.smoothStructure.val)
    (hfull : e.source = univ)
    (f : N → M) (hf : IsSmoothMap R S f)
    (P : PullbackBundle (tangentBundle S) R f) :
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle),
    P202.PullbackData.IsPullback (tangentBundle S) C f hf P CP →
    let ds := fullChartConstantField e he hfull (Pi.single (0 : Fin 2) 1)
    let dt := fullChartConstantField e he hfull (Pi.single (1 : Fin 2) 1)
    ∀ (V T : Section P.space.bundle),
      (∀ q, V.val q = SmoothManifolds.differential R S f hf q (ds.val q)) →
      (∀ q, T.val q = SmoothManifolds.differential R S f hf q (dt.val q)) →
    ∀ q,
      2 * scalarDerivative R (fun z => pairing g (f z) (V.val z) (T.val z))
        q (dt.val q) =
      scalarDerivative R (fun z => pairing g (f z) (T.val z) (T.val z))
        q (ds.val q) +
      2 * pairing g (f q) (V.val q) ((CP.cov dt T).val q) := by
  letI := P.space.topology
  intro CP hCP ds dt V T hV hT q
  have hcomm := TorsionAndMetric.two_parameter_torsion_free
    e he hfull C hC.1 f hf P CP hCP V T hV hT q
  have ht := TorsionAndMetric.metric_map_product (tangentBundle S) g C hC.2
    f hf P CP hCP dt V T q
  have hs := TorsionAndMetric.metric_map_product (tangentBundle S) g C hC.2
    f hf P CP hCP ds T T q
  change scalarDerivative R (fun z => pairing g (f z) (V.val z) (T.val z))
    q (dt.val q) = _ at ht
  change scalarDerivative R (fun z => pairing g (f z) (T.val z) (T.val z))
    q (ds.val q) = _ at hs
  change (CP.cov ds T).val q = (CP.cov dt V).val q at hcomm
  rw [hcomm] at hs
  have hsym := g.symmetric (f q) (T.val q) ((CP.cov dt V).val q)
  change pairing g (f q) (T.val q) ((CP.cov dt V).val q) =
    pairing g (f q) ((CP.cov dt V).val q) (T.val q) at hsym
  dsimp only [pairing] at ht hs hsym ⊢
  linarith only [ht, hs, hsym]

end Variation

section PullbackCurves
open SmoothManifolds (ModelKind)
open SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
universe v w
variable {m r : ℕ} {a b : ModelKind} {A N : Type u}
  [TopologicalSpace A] [TopologicalSpace N]
  {R : SmoothManifold m a N} {Q : SmoothManifold n b A}
  {ι : Type v} {E : A → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]

/-- The intrinsic smooth differential carries actual within velocities to
actual within velocities, including one-sided parameter germs. -/
theorem velocity_smooth_postcomposition
    (f : N → A) (hf : IsSmoothMap R Q f)
    {c : ℝ → N} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    {v : TangentSpace R (c t)} (hv : HasVelocityWithinAt R c J t v) :
    HasVelocityWithinAt Q (f ∘ c) J t
      (SmoothManifolds.differential R Q f hf (c t) v) := by
  obtain ⟨e, he, hp⟩ := R.smoothStructure.property.1.1 (c t)
  obtain ⟨d, hd, hpd⟩ := Q.smoothStructure.property.1.1 (f (c t))
  obtain ⟨U, hU, hpU, H, hH, hrep⟩ := (hf (c t)).2 e he d hd hp hpd
  have hj := SmoothManifolds.differential_jacobian R Q f hf (c t)
    (SmoothManifolds.differential R Q f hf (c t))
    (SmoothManifolds.differential_spec R Q f hf (c t))
    e d he hd hp hpd
    ((tangentStructure R).fiberCoordinates.equiv e he (c t) hp)
    ((tangentStructure Q).fiberCoordinates.equiv d hd (f (c t)) hpd)
    ((tangentStructure R).fiberCoordinates.isCoordinates e he (c t) hp)
    ((tangentStructure Q).fiberCoordinates.isCoordinates d hd (f (c t)) hpd)
    U H hU hpU hH hrep v
  refine ⟨(hf (c t)).1.comp_continuousWithinAt hv.1, d, hd, hpd, ?_⟩
  dsimp only [Function.comp_apply]
  rw [hj]
  exact ((hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivWithinAt t (CurveCovariantDerivative.velocity_coordinates hv ht e he hp)
    |>.congr_of_eventuallyEq_of_mem (hrep.comp_tendsto hv.1).symm ht

/-- Restricting a pullback section to a curve differentiates by the original
connection. The target velocity is obtained from the smooth differential;
no rank condition on the map or extension of the curve is required. -/
theorem pullback_section_curve_derivative
    (B : SmoothVectorBundle Q r ι E) (C : Connection B)
    (f : N → A) (hf : IsSmoothMap R Q f) (P : PullbackBundle B R f) :
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle),
    P202.PullbackData.IsPullback B C f hf P CP →
    ∀ (z : Section P.space.bundle) (c : ℝ → N) (J : Set ℝ) (t : ℝ)
      (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
      (v : TangentSpace R (c t)),
    HasVelocityWithinAt R c J t v →
    HasCovariantDerivativeWithinAt C (f ∘ c) (fun s => z.val (c s)) J t
      (pointDerivative CP z.val (c t) v) := by
  letI := P.space.topology
  intro CP hCP z c J t ht hJ v hv
  have hfv := velocity_smooth_postcomposition f hf ht hv
  obtain ⟨U, hU, hp, ⟨e⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (f (c t))
  let ep := PullbackConnections.pullFrame B f hf P hU e
  have hz := CurveCovariantDerivative.derivative_section CP z ht hv
  obtain ⟨z', hz'⟩ := CurveCovariantDerivative.exists_coefficients_deriv CP ht hz ep hp
  have heq := CurveCovariantDerivative.local_formula CP ht hJ hz ep hp hv hz'
  have hcoeff : coefficientsAlong ep c (fun s => z.val (c s)) =
      coefficientsAlong e (f ∘ c) (fun s => z.val (c s)) := by
    funext s
    classical
    unfold coefficientsAlong
    simp only [mem_preimage, Function.comp_apply]
    split_ifs <;> rfl
  have hm : connectionMatrix CP ep ⟨c t, hp⟩ v =
      connectionMatrix C e ⟨f (c t), hp⟩
        (SmoothManifolds.differential R Q f hf (c t) v) := by
    ext i j
    exact PullbackConnections.frame_rule_of_isPullback B f hf P C CP hCP U hU _
      e ep (fun _ _ => rfl) ⟨c t, hp⟩ v i j
  refine ⟨_, hfv, U, hU, e, hp, z', ?_, ?_⟩
  · rwa [← hcoeff]
  · rw [heq]
    unfold frameDerivative
    rw [hm, hcoeff]
    rfl

/-- A pullback covariant derivative in a field direction is the original
covariant derivative along every curve with that velocity. -/
theorem pullback_cov_curve_derivative
    (B : SmoothVectorBundle Q r ι E) (C : Connection B)
    (f : N → A) (hf : IsSmoothMap R Q f) (P : PullbackBundle B R f) :
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle),
    P202.PullbackData.IsPullback B C f hf P CP →
    ∀ (z : Section P.space.bundle) (X : Field R)
      (c : ℝ → N) (J : Set ℝ) (t : ℝ)
      (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t),
    HasVelocityWithinAt R c J t (X.val (c t)) →
    HasCovariantDerivativeWithinAt C (f ∘ c) (fun s => z.val (c s)) J t
      ((CP.cov X z).val (c t)) := by
  letI := P.space.topology
  intro CP hCP z X c J t ht hJ hv
  rw [← ConnectionForms.pointDerivative_global P.space.bundle CP z (c t) X]
  exact pullback_section_curve_derivative B C f hf P CP hCP z c J t ht hJ _ hv

/-- In particular, a field parallel along the image curve has zero pullback
covariant derivative in the curve direction. -/
theorem pullback_cov_zero_of_parallel
    (B : SmoothVectorBundle Q r ι E) (C : Connection B)
    (f : N → A) (hf : IsSmoothMap R Q f) (P : PullbackBundle B R f) :
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle),
    P202.PullbackData.IsPullback B C f hf P CP →
    ∀ (z : Section P.space.bundle) (X : Field R)
      (c : ℝ → N) (J : Set ℝ) (t : ℝ)
      (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t),
    HasVelocityWithinAt R c J t (X.val (c t)) →
    HasCovariantDerivativeWithinAt C (f ∘ c) (fun s => z.val (c s)) J t 0 →
    (CP.cov X z).val (c t) = 0 := by
  letI := P.space.topology
  intro CP hCP z X c J t ht hJ hv hz
  exact CurveCovariantDerivative.covariantDerivative_unique C ht hJ
    (pullback_cov_curve_derivative B C f hf P CP hCP z X c J t ht hJ hv) hz

/-- A smooth bundle metric pairs arbitrary smooth pullback sections smoothly,
even if the underlying smooth map has singular differential. -/
theorem metric_pullback_pairing_smooth
    (B : SmoothVectorBundle Q r ι E)
    (h : SmoothManifolds.BundleMetricData.SmoothFiberMetric B)
    (f : N → A) (hf : IsSmoothMap R Q f) (P : PullbackBundle B R f) :
    letI := P.space.topology
    ∀ (z y : Section P.space.bundle) (q : N),
    VectorSmoothAt R.smoothStructure.val
      (fun a => h.form (f a) (z.val a) (y.val a)) q := by
  letI := P.space.topology
  intro z y q
  obtain ⟨a, e, he⟩ := PullbackConnections.exists_expansion B f hf P z q
  obtain ⟨b, d, hd⟩ := PullbackConnections.exists_expansion B f hf P y q
  have hs (a : GlobalSmooth R) : VectorSmoothAt R.smoothStructure.val a.val q :=
    (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
      ((SmoothManifolds.mem_globalSmoothAlgebra_iff R _).mp a.property q)
  have hsum : VectorSmoothAt R.smoothStructure.val
      (fun x => ∑ i : Fin r, ∑ j : Fin r,
        (a i).val x * ((b j).val x * h.form (f x) ((e i).val (f x)) ((d j).val (f x)))) q := by
    apply VectorSmoothAt.sum
    intro i
    apply VectorSmoothAt.sum
    intro j
    have hg := (TorsionAndMetric.metricPairing_smooth B h (e i) (d j) (f q)).comp
      Q.smoothStructure.property.1.1 (hf q)
    exact ((hs (a i)).prod (((hs (b j)).prod hg).postcomp
      (contDiff_fst.mul contDiff_snd))).postcomp (contDiff_fst.mul contDiff_snd)
  apply hsum.congr
  filter_upwards [he, hd] with x hx hy
  rw [hx, hy]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end PullbackCurves

section FullChartCurves
open SmoothManifolds.MapData SmoothManifolds.FrameData
  SmoothManifolds.LieBracketData P202.TorsionMetricData
variable {N : Type u} [TopologicalSpace N]
  {R : SmoothManifold 2 .euclidean N}

/-- A coordinate curve with constant coordinate velocity has the corresponding
full-chart constant field as its intrinsic velocity. -/
theorem fullChart_velocity
    (e : ModelChart 2 .euclidean N) (he : e ∈ R.smoothStructure.val)
    (hfull : e.source = univ) (w : Euclidean 2)
    (c : ℝ → N) (t : ℝ) (hc : ContinuousAt c t)
    (hd : HasDerivAt (fun s => (e (c s)).val) w t) :
    HasVelocityWithinAt R c univ t
      ((fullChartConstantField e he hfull w).val (c t)) := by
  have hp : c t ∈ e.source := hfull ▸ mem_univ _
  refine ⟨hc.continuousWithinAt, e, he, hp, ?_⟩
  have hw := P202.TorsionMetricData.fullChartConstantField_coefficients e he hfull w (c t)
  simp only [SmoothManifolds.LieBracketData.coefficients, dif_pos hp] at hw
  rw [hw]
  exact hd.hasDerivWithinAt

/-- Scalar differentiation along a coordinate line computes the intrinsic
directional derivative in the corresponding constant field. -/
theorem fullChart_scalarDerivative
    (e : ModelChart 2 .euclidean N) (he : e ∈ R.smoothStructure.val)
    (hfull : e.source = univ) (w : Euclidean 2)
    (c : ℝ → N) (t : ℝ) (hc : ContinuousAt c t)
    (hd : HasDerivAt (fun s => (e (c s)).val) w t)
    (h : N → ℝ) (hh : VectorSmoothAt R.smoothStructure.val h (c t))
    (a : ℝ) (ha : HasDerivAt (h ∘ c) a t) :
    scalarDerivative R h (c t)
      ((fullChartConstantField e he hfull w).val (c t)) = a := by
  have hchain := CurveCovariantDerivative.scalar_chain
    (fullChart_velocity e he hfull w c t hc hd) h hh
  rw [hasDerivWithinAt_univ] at hchain
  exact hchain.unique ha

/-- In a geodesic variation, the transverse derivative of squared speed is
twice the initial pairing. Only the germ of the energy identity is needed. -/
theorem variation_energy_derivative
    (g : RiemannianMetric S) (p : M) (v w : TangentSpace S p)
    (e : ModelChart 2 .euclidean N) (he : e ∈ R.smoothStructure.val)
    (hfull : e.source = univ)
    (f : N → M) (hf : IsSmoothMap R S f)
    (P : SmoothManifolds.BundleOperationsData.PullbackBundle (tangentBundle S) R f) :
    letI := P.space.topology
    ∀ (T : Section P.space.bundle) (c : ℝ → N),
      ContinuousAt c 0 →
      HasDerivAt (fun s => (e (c s)).val) (Pi.single (0 : Fin 2) 1) 0 →
      (fun s => pairing g (f (c s)) (T.val (c s)) (T.val (c s))) =ᶠ[𝓝 0]
        (fun s => pairing g p (v + s • w) (v + s • w)) →
      scalarDerivative R (fun q => pairing g (f q) (T.val q) (T.val q))
        (c 0) ((fullChartConstantField e he hfull (Pi.single (0 : Fin 2) 1)).val
          (c 0)) = 2 * pairing g p v w := by
  letI := P.space.topology
  intro T c hc hd henergy
  apply fullChart_scalarDerivative e he hfull _ c 0 hc hd
    (fun q => pairing g (f q) (T.val q) (T.val q))
    (metric_pullback_pairing_smooth (tangentBundle S) g f hf P T T (c 0))
  exact (initial_squared_speed_derivative g p v w).congr_of_eventuallyEq henergy

/-- The geometric first-variation identity integrates along an actual open
time interval. The energy derivative and acceleration are kept explicit so
that they can be supplied by the original maximal geodesics. -/
theorem variation_pairing_endpoint
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C)
    (e : ModelChart 2 .euclidean N) (he : e ∈ R.smoothStructure.val)
    (hfull : e.source = univ)
    (f : N → M) (hf : IsSmoothMap R S f)
    (P : SmoothManifolds.BundleOperationsData.PullbackBundle (tangentBundle S) R f) :
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle),
    P202.PullbackData.IsPullback (tangentBundle S) C f hf P CP →
    let ds := fullChartConstantField e he hfull (Pi.single (0 : Fin 2) 1)
    let dt := fullChartConstantField e he hfull (Pi.single (1 : Fin 2) 1)
    ∀ (V T : Section P.space.bundle),
      (∀ q, V.val q = SmoothManifolds.differential R S f hf q (ds.val q)) →
      (∀ q, T.val q = SmoothManifolds.differential R S f hf q (dt.val q)) →
    ∀ (I : D13Unified.OpenTimeInterval)
      (h0 : 0 ∈ I.carrier) (h1 : 1 ∈ I.carrier)
      (c : ℝ → N),
      (∀ t ∈ I.carrier, ContinuousAt c t) →
      (∀ t ∈ I.carrier, HasDerivAt (fun s => (e (c s)).val)
        (Pi.single (1 : Fin 2) 1) t) →
    ∀ (a : ℝ),
      (∀ t ∈ I.carrier,
        scalarDerivative R (fun q => pairing g (f q) (T.val q) (T.val q))
          (c t) (ds.val (c t)) = 2 * a) →
      (∀ t ∈ I.carrier, (CP.cov dt T).val (c t) = 0) →
      V.val (c 0) = 0 →
      pairing g (f (c 1)) (T.val (c 1)) (V.val (c 1)) = a := by
  letI := P.space.topology
  intro CP hCP ds dt V T hV hT I h0 h1 c hc hcoords a henergy hacc hzero
  let h : ℝ → ℝ := fun t => pairing g (f (c t)) (V.val (c t)) (T.val (c t))
  have hd (t : ℝ) (ht : t ∈ I.carrier) : HasDerivAt h a t := by
    have hv := fullChart_velocity e he hfull (Pi.single (1 : Fin 2) 1)
      c t (hc t ht) (hcoords t ht)
    have hm := metric_pullback_pairing_smooth (tangentBundle S) g f hf P V T (c t)
    have hchain := CurveCovariantDerivative.scalar_chain hv
      (fun q => pairing g (f q) (V.val q) (T.val q)) hm
    rw [hasDerivWithinAt_univ] at hchain
    have hi := variation_pairing_identity g C hC e he hfull f hf P CP hCP
      V T hV hT (c t)
    change 2 * scalarDerivative R (fun q => pairing g (f q) (V.val q) (T.val q))
      (c t) (dt.val (c t)) =
      scalarDerivative R (fun q => pairing g (f q) (T.val q) (T.val q))
        (c t) (ds.val (c t)) +
      2 * pairing g (f (c t)) (V.val (c t)) ((CP.cov dt T).val (c t)) at hi
    have hz : pairing g (f (c t)) (V.val (c t)) ((CP.cov dt T).val (c t)) = 0 := by
      rw [hacc t ht]
      exact map_zero _
    rw [henergy t ht, hz] at hi
    have hs : scalarDerivative R (fun q => pairing g (f q) (V.val q) (T.val q))
        (c t) (dt.val (c t)) = a := by linarith only [hi]
    change HasDerivAt h
      (scalarDerivative R (fun q => pairing g (f q) (V.val q) (T.val q))
        (c t) (dt.val (c t))) t at hchain
    rwa [hs] at hchain
  have hz : h 0 = 0 := by
    dsimp only [h]
    rw [hzero]
    simp only [pairing, map_zero, LinearMap.zero_apply]
  calc
    _ = h 1 := g.symmetric (f (c 1)) (T.val (c 1)) (V.val (c 1))
    _ = a := pairing_at_one_of_hasDerivAt I h0 h1 h a hd hz

end FullChartCurves

section GeodesicGerms
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
variable {m : ℕ} {a : SmoothManifolds.ModelKind} {N : Type u}
  [TopologicalSpace N] {R : SmoothManifold m a N}

/-- A phase geodesic germ forces the corresponding pullback acceleration to vanish. -/
theorem pullback_cov_zero_of_geodesic_germ
    (C : Connection (tangentBundle S))
    (f : N → M) (hf : IsSmoothMap R S f)
    (P : PullbackBundle (tangentBundle S) R f) :
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle),
    P202.PullbackData.IsPullback (tangentBundle S) C f hf P CP →
    ∀ (T : Section P.space.bundle) (X : Field R)
      (c : ℝ → N) (t : ℝ) (q : ℝ → Phase S),
    HasVelocityWithinAt R c univ t (X.val (c t)) →
    q =ᶠ[𝓝 t] (fun s => (⟨f (c s), T.val (c s)⟩ : Phase S)) →
    (HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2 ∧
      HasCovariantDerivativeAt C (fun s => (q s).1) (fun s => (q s).2) t 0) →
    (CP.cov X T).val (c t) = 0 := by
  letI := P.space.topology
  intro CP hCP T X c t q hc heq hq
  have hr := geodesicAt_congr C heq hq
  exact pullback_cov_zero_of_parallel (tangentBundle S) C f hf P CP hCP T X
    c univ t (mem_univ t) uniqueDiffWithinAt_univ hc hr.2


end GeodesicGerms

/-- Coordinate derivative of the exponential along an affine tangent line. -/
theorem fiberDifferential_line_derivative
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F p v ∈ d.source) (w : TangentSpace S p) :
    HasDerivAt (fun s : ℝ => (d (fiberExponential F p (v + s • w))).val)
      ((tangentStructure S).fiberCoordinates.equiv d hd
        (fiberExponential F p v) hq (fiberDifferential F p v e he hp d hd hq w)) 0 := by
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let D := (tangentStructure S).fiberCoordinates.equiv d hd
    (fiberExponential F p v) hq
  let f := fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val
  have hline : HasDerivAt (fun s : ℝ => E v + s • E w) (E w) 0 := by
    simpa only [zero_smul, add_zero, id_eq, one_smul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) (E v)).add ((hasDerivAt_id (0 : ℝ)).smul_const (E w))
  have hf := fiberDifferential_hasFDerivAt C F hF p v hv e he hp d hd hq
  have hchain := hf.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp [E])
  have heq : (fun s : ℝ => f (E v + s • E w)) =
      (fun s : ℝ => (d (fiberExponential F p (v + s • w))).val) := by
    funext s
    simp only [f, map_add, map_smul, LinearEquiv.symm_apply_apply]
  change HasDerivAt (fun s : ℝ => f (E v + s • E w)) _ _ at hchain
  rw [heq] at hchain
  simpa only [fiberDifferential, LinearMap.comp_apply, LinearMap.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, f, E, D] using! hchain

/-- Tangent phases are equal when their actual chart coordinates agree. -/
theorem phase_eq_of_coordinates
    (x y : M) (hxy : x = y)
    (a : TangentSpace S x) (b : TangentSpace S y)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hx : x ∈ d.source) (hy : y ∈ d.source)
    (heq : (tangentStructure S).fiberCoordinates.equiv d hd x hx a =
      (tangentStructure S).fiberCoordinates.equiv d hd y hy b) :
    (⟨x, a⟩ : Phase S) = ⟨y, b⟩ := by
  subst y
  exact congrArg (Sigma.mk x) (((tangentStructure S).fiberCoordinates.equiv d hd x hx).injective heq)


/-- Pairings respect equality of the actual tangent phases in both entries. -/
theorem pairing_eq_of_phases (g : RiemannianMetric S)
    {x y : M} {a b : TangentSpace S x} {c d : TangentSpace S y}
    (hac : (⟨x, a⟩ : Phase S) = ⟨y, c⟩)
    (hbd : (⟨x, b⟩ : Phase S) = ⟨y, d⟩) :
    pairing g x a b = pairing g y c d := by
  have hxy : x = y := congrArg Sigma.fst hac
  subst y
  have ha : a = c := eq_of_heq (Sigma.mk.inj_iff.mp hac).2
  have hb : b = d := eq_of_heq (Sigma.mk.inj_iff.mp hbd).2
  rw [ha, hb]

section Endpoint
open SmoothManifolds.MapData P202.TorsionMetricData
variable {N : Type u} [TopologicalSpace N] {R : SmoothManifold 2 .euclidean N}

/-- A coordinate line identifies the differential of a smooth surface in the
corresponding coordinate direction with the actual derivative of that line. -/
theorem fullChart_differential_coordinates
    (e : ModelChart 2 .euclidean N) (he : e ∈ R.smoothStructure.val)
    (hfull : e.source = univ) (a : Euclidean 2)
    (f : N → M) (hf : IsSmoothMap R S f)
    (q : N) (c : ℝ → N) (hc0 : c 0 = q)
    (hc : ContinuousAt c 0)
    (hcoords : HasDerivAt (fun s : ℝ => (e (c s)).val) a 0)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : f q ∈ d.source)
    (z : Euclidean n)
    (hz : HasDerivAt (fun s : ℝ => (d (f (c s))).val) z 0) :
    (tangentStructure S).fiberCoordinates.equiv d hd (f q) hq
      (SmoothManifolds.differential R S f hf q
        ((fullChartConstantField e he hfull a).val q)) = z := by
  subst q
  have hv := fullChart_velocity e he hfull a c 0 hc hcoords
  have hvf := velocity_smooth_postcomposition f hf (mem_univ 0) hv
  have hder := CurveCovariantDerivative.velocity_coordinates hvf (mem_univ 0) d hd hq
  rw [hasDerivWithinAt_univ] at hder
  exact hder.unique hz

/-- A constant horizontal germ gives zero variation field. -/
theorem fullChart_differential_zero_of_constant
    (e : ModelChart 2 .euclidean N) (he : e ∈ R.smoothStructure.val)
    (hfull : e.source = univ) (a : Euclidean 2)
    (f : N → M) (hf : IsSmoothMap R S f)
    (q : N) (c : ℝ → N) (hc0 : c 0 = q)
    (hc : ContinuousAt c 0)
    (hcoords : HasDerivAt (fun s : ℝ => (e (c s)).val) a 0)
    (hconstant : (fun s => f (c s)) =ᶠ[𝓝 0] (fun _ => f q)) :
    SmoothManifolds.differential R S f hf q
      ((fullChartConstantField e he hfull a).val q) = 0 := by
  obtain ⟨d, hd, hq⟩ := S.smoothStructure.property.1.1 (f q)
  have hz : HasDerivAt (fun s : ℝ => (d (f (c s))).val) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (d (f q)).val).congr_of_eventuallyEq
      (hconstant.fun_comp (fun x => (d x).val))
  apply ((tangentStructure S).fiberCoordinates.equiv d hd (f q) hq).injective
  simpa only [map_zero] using fullChart_differential_coordinates
    e he hfull a f hf q c hc0 hc hcoords d hd hq 0 hz

/-- An exponential horizontal germ gives precisely the fiber differential,
expressed as equality of phases to keep the intrinsic tangent fibers intact. -/
theorem fullChart_differential_exponential_endpoint
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F)
    (b : ModelChart n .euclidean M) (hb : b ∈ S.smoothStructure.val)
    (hp : p ∈ b.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F p v ∈ d.source) (w : TangentSpace S p)
    (e : ModelChart 2 .euclidean N) (he : e ∈ R.smoothStructure.val)
    (hfull : e.source = univ) (a : Euclidean 2)
    (f : N → M) (hf : IsSmoothMap R S f)
    (q : N) (c : ℝ → N) (hc0 : c 0 = q)
    (hc : ContinuousAt c 0)
    (hcoords : HasDerivAt (fun s : ℝ => (e (c s)).val) a 0)
    (hline : (fun s => f (c s)) =ᶠ[𝓝 0]
      (fun s => fiberExponential F p (v + s • w))) :
    (⟨f q, SmoothManifolds.differential R S f hf q
      ((fullChartConstantField e he hfull a).val q)⟩ : Phase S) =
      ⟨fiberExponential F p v, fiberDifferential F p v b hb hp d hd hq w⟩ := by
  have hbase : f q = fiberExponential F p v := by
    simpa only [hc0, zero_smul, add_zero] using hline.self_of_nhds
  have hq' : f q ∈ d.source := by rw [hbase]; exact hq
  have hz := (fiberDifferential_line_derivative C F hF p v hv b hb hp d hd hq w).congr_of_eventuallyEq (hline.fun_comp (fun x => (d x).val))
  exact phase_eq_of_coordinates (f q) (fiberExponential F p v) hbase _ _
    d hd hq' hq (fullChart_differential_coordinates e he hfull a f hf
      q c hc0 hc hcoords d hd hq' _ hz)

end Endpoint
theorem pairing_eq_of_phase_eq (g : RiemannianMetric S)
    {p q : M} {a b : TangentSpace S p} {c d : TangentSpace S q}
    (h1 : (⟨p, a⟩ : Phase S) = ⟨q, c⟩)
    (h2 : (⟨p, b⟩ : Phase S) = ⟨q, d⟩) :
    pairing g p a b = pairing g q c d := by
  cases h1
  have hb : b = d := eq_of_heq (Sigma.mk.inj_iff.mp h2).2
  rw [hb]

theorem zero_of_phase_eq
    {p q : M} {a : TangentSpace S p}
    (h : (⟨p, a⟩ : Phase S) = ⟨q, 0⟩) : a = 0 := by
  have hp : p = q := congrArg Sigma.fst h
  cases hp
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2


open SmoothManifolds.MapData
/-- Initial phases of the usual affine velocity variation, in real coordinates. -/
def variationPhase (F : CurveFamily (Phase S)) (p : M)
    (v w : TangentSpace S p) (x : Euclidean 2) : Phase S :=
  ⟨p, v + x 0 • w⟩

theorem variationPhase_continuous (F : CurveFamily (Phase S)) (p : M)
    (v w : TangentSpace S p) : Continuous (variationPhase F p v w) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  have hc : Continuous (fun x : Euclidean 2 => E v + x 0 • E w) :=
    continuous_const.add ((continuous_apply 0).smul continuous_const)
  apply continuous_iff_continuousAt.mpr
  intro x
  have hi := ExponentialNormalCoordinates.fiberInclusion_continuousAt p e he hp
    (E v + x 0 • E w)
  have hi' : ContinuousAt (fun y : Euclidean 2 =>
      (⟨p, E.symm (E v + y 0 • E w)⟩ : Phase S)) x :=
    hi.comp (f := fun x : Euclidean 2 => E v + x 0 • E w) hc.continuousAt
  exact hi'.congr (Eventually.of_forall (fun y => by
    simp only [variationPhase, map_add, map_smul, LinearEquiv.symm_apply_apply]))

def variationDomain (F : CurveFamily (Phase S)) (p : M)
    (v w : TangentSpace S p) : Set (Euclidean 2) :=
  {x | (x 1, variationPhase F p v w x) ∈ flowDomain F}

theorem variationDomain_isOpen (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) : IsOpen (variationDomain F p v w) := by
  exact (GeodesicIVP.domain_open_smooth S C F hF).1.preimage
    ((continuous_apply 1).prodMk (variationPhase_continuous F p v w))

theorem variationDomain_zero {C : Connection (tangentBundle S)} (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) : (0 : Euclidean 2) ∈ variationDomain F p v w := by
  simpa only [variationDomain, variationPhase, Pi.zero_apply, zero_smul, add_zero,
    mem_setOf_eq, flowDomain] using (hF ⟨p, v⟩).1

abbrev VariationParameter (F : CurveFamily (Phase S)) (p : M)
    (v w : TangentSpace S p) : Type u := ULift.{u} (variationDomain F p v w)

instance variationParameter_secondCountable (F : CurveFamily (Phase S)) (p : M)
    (v w : TangentSpace S p) : SecondCountableTopology (VariationParameter F p v w) :=
  Homeomorph.ulift.secondCountableTopology

noncomputable def variationChart (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) :
    ModelChart 2 .euclidean (VariationParameter F p v w) :=
  Homeomorph.ulift.toOpenPartialHomeomorph.trans
    ((⟨variationDomain F p v w, variationDomain_isOpen C F hF p v w⟩ :
      TopologicalSpace.Opens (Euclidean 2)).openPartialHomeomorphSubtypeCoe
        ⟨⟨0, variationDomain_zero F hF p v w⟩⟩ |>.transHomeomorph
          (Homeomorph.Set.univ (Euclidean 2)).symm)

@[simp] theorem variationChart_source (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) :
    (variationChart C F hF p v w).source = univ := by
  simp [variationChart]

@[simp] theorem variationChart_apply (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (q : VariationParameter F p v w) :
    (variationChart C F hF p v w q).val = q.down.val := rfl

noncomputable def variationManifold (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) :
    SmoothManifold 2 .euclidean (VariationParameter F p v w) :=
  SmoothManifolds.RegularLevels.singleChartManifold
    (variationChart C F hF p v w) (variationChart_source C F hF p v w)

theorem variationChart_mem (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) :
    variationChart C F hF p v w ∈ (variationManifold C F hF p v w).smoothStructure.val :=
  SmoothManifolds.RegularLevels.singleChartManifold_chart_mem _ _

def variationSurface (F : CurveFamily (Phase S)) (p : M)
    (v w : TangentSpace S p) (q : VariationParameter F p v w) : M :=
  (F.curve (variationPhase F p v w q.down.val) (q.down.val 1)).1

theorem variationSurface_smooth (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) :
    IsSmoothMap (variationManifold C F hF p v w) S (variationSurface F p v w) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let b := (tangentStructure S).chart e he
  have hb := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
  let j : Euclidean 2 → ℝ × Euclidean (n+n) := fun x =>
    (x 1, (tangentStructure S).productCoordinates.linearEquiv
      ((e p).val, E v + x 0 • E w))
  have hj : ContDiff ℝ (⊤ : ℕ∞) j := by
    exact (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1).prodMk
      ((tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv.contDiff.comp
        (contDiff_const.prodMk (contDiff_const.add ((contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0).smul contDiff_const))))
  let a := variationChart C F hF p v w
  let R := variationManifold C F hF p v w
  have ha : a ∈ R.smoothStructure.val := variationChart_mem C F hF p v w
  have hphase (x : Euclidean 2) : variationPhase F p v w x ∈ b.source := by
    simpa only [variationPhase, b, (tangentStructure S).chart_source, mem_preimage,
      SmoothManifolds.TangentBundleData.projection] using hp
  have hchart (x : Euclidean 2) :
      (b (variationPhase F p v w x)).val =
        (tangentStructure S).productCoordinates.linearEquiv ((e p).val, E v + x 0 • E w) := by
    dsimp only [variationPhase, b]
    rw [(tangentStructure S).chart_apply e he _ hp]
    simp only [map_add, map_smul, E]
  intro q
  let z : ℝ × Phase S := (q.down.val 1, variationPhase F p v w q.down.val)
  have hz : z ∈ flowDomain F := q.down.property
  have hpos := (GeodesicIVP.domain_open_smooth S C F hF).2 z hz |>.2
  have hzmap : Continuous (fun y : VariationParameter F p v w =>
      (y.down.val 1, variationPhase F p v w y.down.val)) :=
    ((continuous_apply 1).prodMk (variationPhase_continuous F p v w)).comp (continuous_subtype_val.comp Homeomorph.ulift.continuous)
  have hc : ContinuousAt (variationSurface F p v w) q := hpos.1.comp (f := fun y : VariationParameter F p v w =>
    (y.down.val 1, variationPhase F p v w y.down.val)) hzmap.continuousAt
  obtain ⟨d, hd, hpd⟩ := S.smoothStructure.property.1.1 (variationSurface F p v w q)
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    R.smoothStructure.property.1 S.smoothStructure.property.1 _ q).mpr
  refine ⟨hc, a, ha, d, hd, (variationChart_source C F hF p v w).symm ▸ mem_univ q, hpd, ?_⟩
  obtain ⟨U, hU, hzU, H, hH, heq⟩ := hpos.2 b hb d hd (hphase q.down.val) hpd
  refine ⟨j ⁻¹' U, hU.preimage hj.continuous, ?_, H ∘ j,
    hH.comp hj.contDiffOn (fun _ hx => hx), ?_⟩
  · simpa only [mem_preimage, j, z, hchart, a, variationChart_apply] using hzU
  · have h := heq.comp_tendsto hzmap.continuousAt
    simpa only [Function.comp_def, j, z, hchart, a, variationChart_apply,
      variationSurface] using h


/-- Coordinates for a horizontal parameter s and time t. -/
def variationPoint (s t : ℝ) : Euclidean 2 := fun i => if i = 0 then s else t

@[simp] theorem variationPoint_zero (s t : ℝ) : variationPoint s t 0 = s := by
  simp [variationPoint]
@[simp] theorem variationPoint_one (s t : ℝ) : variationPoint s t 1 = t := by
  simp [variationPoint]

theorem variationPoint_time_derivative (s t : ℝ) :
    HasDerivAt (variationPoint s) (Pi.single (1 : Fin 2) 1) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [variationPoint, Pi.single_apply]
      using hasDerivAt_const t s
  · simpa [variationPoint, Pi.single_apply] using! hasDerivAt_id t

/-- The actual parameter domain contains precisely each maximal time slice. -/
theorem variationPoint_mem {C : Connection (tangentBundle S)}
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (s t : ℝ)
    (ht : t ∈ (F.interval ⟨p, v + s • w⟩).carrier) :
    variationPoint s t ∈ variationDomain F p v w := by
  simpa only [variationDomain, variationPhase, variationPoint_zero, variationPoint_one,
    mem_setOf_eq, flowDomain] using ht

/-- Time curves are total representatives, with values outside their actual
maximal interval irrelevant to every derivative assertion. -/
noncomputable def variationTimeCurve {C : Connection (tangentBundle S)}
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (s t : ℝ) : VariationParameter F p v w := by
  classical
  exact if ht : t ∈ (F.interval ⟨p, v + s • w⟩).carrier then
    ⟨⟨variationPoint s t, variationPoint_mem F hF p v w s t ht⟩⟩ else
    ⟨⟨variationPoint s 0, variationPoint_mem F hF p v w s 0 (hF _).1⟩⟩

theorem variationTimeCurve_germ {C : Connection (tangentBundle S)}
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (s t : ℝ)
    (ht : t ∈ (F.interval ⟨p, v + s • w⟩).carrier) :
    (fun u => (variationTimeCurve F hF p v w s u).down.val) =ᶠ[𝓝 t] variationPoint s := by
  classical
  filter_upwards [(F.interval ⟨p, v + s • w⟩).isOpen.mem_nhds ht] with u hu
  simp only [variationTimeCurve, dif_pos hu]

theorem variationTimeCurve_continuousAt {C : Connection (tangentBundle S)}
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (s t : ℝ)
    (ht : t ∈ (F.interval ⟨p, v + s • w⟩).carrier) :
    ContinuousAt (variationTimeCurve F hF p v w s) t := by
  apply (Homeomorph.ulift.comp_continuousAt_iff _ _).mp
  apply tendsto_subtype_rng.mpr
  exact (variationPoint_time_derivative s t).continuousAt.congr
    (variationTimeCurve_germ F hF p v w s t ht).symm

theorem variationTimeCurve_derivative (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (s t : ℝ)
    (ht : t ∈ (F.interval ⟨p, v + s • w⟩).carrier) :
    HasDerivAt (fun u => (variationChart C F hF p v w
      (variationTimeCurve F hF p v w s u)).val) (Pi.single (1 : Fin 2) 1) t := by
  exact (variationPoint_time_derivative s t).congr_of_eventuallyEq
    (variationTimeCurve_germ F hF p v w s t ht)

@[simp] theorem variationSurface_timeCurve {C : Connection (tangentBundle S)}
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (s t : ℝ)
    (ht : t ∈ (F.interval ⟨p, v + s • w⟩).carrier) :
    variationSurface F p v w (variationTimeCurve F hF p v w s t) =
      (F.curve ⟨p, v + s • w⟩ t).1 := by
  classical
  simp only [variationTimeCurve, dif_pos ht, variationSurface, variationPhase,
    variationPoint_zero, variationPoint_one]


@[simp] theorem variationPoint_coordinates (x : Euclidean 2) :
    variationPoint (x 0) (x 1) = x := by
  funext i
  fin_cases i <;> simp [variationPoint]

theorem variationTimeCurve_at {C : Connection (tangentBundle S)}
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (q : VariationParameter F p v w) :
    variationTimeCurve F hF p v w (q.down.val 0) (q.down.val 1) = q := by
  classical
  have ht : q.down.val 1 ∈ (F.interval ⟨p, v + q.down.val 0 • w⟩).carrier := q.down.property
  apply ULift.ext
  apply Subtype.ext
  simp only [variationTimeCurve, dif_pos ht, variationPoint_coordinates]

theorem variationSurface_timeCurve_germ {C : Connection (tangentBundle S)}
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (s t : ℝ)
    (ht : t ∈ (F.interval ⟨p, v + s • w⟩).carrier) :
    (fun u => variationSurface F p v w (variationTimeCurve F hF p v w s u)) =ᶠ[𝓝 t]
      (fun u => (F.curve ⟨p, v + s • w⟩ u).1) := by
  filter_upwards [(F.interval ⟨p, v + s • w⟩).isOpen.mem_nhds ht] with u hu
  exact variationSurface_timeCurve F hF p v w s u hu

open P202.TorsionMetricData in
/-- The second differential of the variation is its actual geodesic velocity,
recorded as equality of intrinsic phase points. -/
theorem variationSurface_time_phase (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (q : VariationParameter F p v w) :
    let R := variationManifold C F hF p v w
    let a := variationChart C F hF p v w
    let ha := variationChart_mem C F hF p v w
    let f := variationSurface F p v w
    let hf := variationSurface_smooth C F hF p v w
    let dt := fullChartConstantField a ha (variationChart_source C F hF p v w) (Pi.single (1 : Fin 2) 1)
    (⟨f q, SmoothManifolds.differential R S f hf q (dt.val q)⟩ : Phase S) =
      F.curve (variationPhase F p v w q.down.val) (q.down.val 1) := by
  dsimp only
  let R := variationManifold C F hF p v w
  let a := variationChart C F hF p v w
  let ha := variationChart_mem C F hF p v w
  let f := variationSurface F p v w
  let hf := variationSurface_smooth C F hF p v w
  let dt := fullChartConstantField a ha (variationChart_source C F hF p v w) (Pi.single (1 : Fin 2) 1)
  let c := variationTimeCurve F hF p v w (q.down.val 0)
  let t := q.down.val 1
  have ht : t ∈ (F.interval ⟨p, v + q.down.val 0 • w⟩).carrier := q.down.property
  have hct : c t = q := variationTimeCurve_at F hF p v w q
  have hv := fullChart_velocity a ha (variationChart_source C F hF p v w) (Pi.single (1 : Fin 2) 1) c t
    (variationTimeCurve_continuousAt F hF p v w (q.down.val 0) t ht)
    (variationTimeCurve_derivative C F hF p v w (q.down.val 0) t ht)
  have hvf := velocity_smooth_postcomposition f hf (mem_univ t) hv
  have hgamma := ((hF ⟨p, v + q.down.val 0 • w⟩).2.2.1 t ht).1
  have hgerm := variationSurface_timeCurve_germ F hF p v w (q.down.val 0) t ht
  have htarget : f (c t) = (F.curve ⟨p, v + q.down.val 0 • w⟩ t).1 := hgerm.eq_of_nhds
  obtain ⟨d, hd, hpd⟩ := S.smoothStructure.property.1.1
    (F.curve ⟨p, v + q.down.val 0 • w⟩ t).1
  have hfd : f (c t) ∈ d.source := htarget.symm ▸ hpd
  have hcoords := CurveCovariantDerivative.velocity_coordinates hvf (mem_univ t) d hd hfd
  have hcoordsGamma := CurveCovariantDerivative.velocity_coordinates hgamma (mem_univ t) d hd hpd
  rw [hasDerivWithinAt_univ] at hcoords hcoordsGamma
  have hder := hcoords.congr_of_eventuallyEq (hgerm.fun_comp (fun z => (d z).val)).symm
  have hsame := hder.unique hcoordsGamma
  let b := (tangentStructure S).chart d hd
  let z : Phase S := ⟨f (c t), SmoothManifolds.differential R S f hf (c t) (dt.val (c t))⟩
  have hz : z ∈ b.source := by
    simpa only [b, (tangentStructure S).chart_source, mem_preimage,
      SmoothManifolds.TangentBundleData.projection, z] using hfd
  have hgam : F.curve ⟨p, v + q.down.val 0 • w⟩ t ∈ b.source := by
    simpa only [b, (tangentStructure S).chart_source, mem_preimage,
      SmoothManifolds.TangentBundleData.projection] using hpd
  have hphase : z = F.curve ⟨p, v + q.down.val 0 • w⟩ t := by
    apply b.injOn hz hgam
    apply Subtype.ext
    change ((tangentStructure S).chart d hd z).val = _
    rw [(tangentStructure S).chart_apply d hd z hfd,
      (tangentStructure S).chart_apply d hd _ hpd]
    exact congrArg (tangentStructure S).productCoordinates.linearEquiv
      (Prod.ext (congrArg (fun z => (d z).val) htarget) hsame)
  dsimp only [z] at hphase
  rw [hct] at hphase
  exact hphase


theorem variationPoint_horizontal_derivative (s t : ℝ) :
    HasDerivAt (fun r => variationPoint (s + r) t) (Pi.single (0 : Fin 2) 1) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [variationPoint, Pi.single_apply]
      using (hasDerivAt_id (0 : ℝ)).const_add s
  · simpa [variationPoint, Pi.single_apply]
      using hasDerivAt_const (0 : ℝ) t

noncomputable def variationHorizontalCurve (F : CurveFamily (Phase S))
    (p : M) (v w : TangentSpace S p) (q : VariationParameter F p v w) (r : ℝ) :
    VariationParameter F p v w := by
  classical
  exact if hr : variationPoint (q.down.val 0 + r) (q.down.val 1) ∈ variationDomain F p v w then
    ⟨⟨variationPoint (q.down.val 0 + r) (q.down.val 1), hr⟩⟩ else q

theorem variationHorizontalCurve_at (F : CurveFamily (Phase S))
    (p : M) (v w : TangentSpace S p) (q : VariationParameter F p v w) :
    variationHorizontalCurve F p v w q 0 = q := by
  classical
  have hq : variationPoint (q.down.val 0 + 0) (q.down.val 1) ∈ variationDomain F p v w := by
    simpa only [add_zero, variationPoint_coordinates] using q.down.property
  apply ULift.ext
  apply Subtype.ext
  simp only [variationHorizontalCurve, dif_pos hq]
  simp only [add_zero, variationPoint_coordinates]

theorem variationHorizontalCurve_germ (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (q : VariationParameter F p v w) :
    (fun r => (variationHorizontalCurve F p v w q r).down.val) =ᶠ[𝓝 0]
      (fun r => variationPoint (q.down.val 0 + r) (q.down.val 1)) := by
  classical
  have hq : variationPoint (q.down.val 0 + 0) (q.down.val 1) ∈ variationDomain F p v w := by
    simpa only [add_zero, variationPoint_coordinates] using q.down.property
  have he : ∀ᶠ r in 𝓝 (0 : ℝ), variationPoint (q.down.val 0 + r) (q.down.val 1) ∈
      variationDomain F p v w :=
    (variationPoint_horizontal_derivative (q.down.val 0) (q.down.val 1)).continuousAt.preimage_mem_nhds
      ((variationDomain_isOpen C F hF p v w).mem_nhds hq)
  filter_upwards [he] with r hr
  simp only [variationHorizontalCurve, dif_pos hr]

theorem variationHorizontalCurve_continuousAt (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (q : VariationParameter F p v w) :
    ContinuousAt (variationHorizontalCurve F p v w q) 0 := by
  apply (Homeomorph.ulift.comp_continuousAt_iff _ _).mp
  apply tendsto_subtype_rng.mpr
  have h := (variationPoint_horizontal_derivative (q.down.val 0) (q.down.val 1)).continuousAt.congr
    (variationHorizontalCurve_germ C F hF p v w q).symm
  exact h

theorem variationHorizontalCurve_derivative (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (q : VariationParameter F p v w) :
    HasDerivAt (fun r => (variationChart C F hF p v w
      (variationHorizontalCurve F p v w q r)).val) (Pi.single (0 : Fin 2) 1) 0 := by
  exact (variationPoint_horizontal_derivative (q.down.val 0) (q.down.val 1)).congr_of_eventuallyEq
    (variationHorizontalCurve_germ C F hF p v w q)

open P202.TorsionMetricData
/-- The variation at initial time has constant base point along every
horizontal germ, including the zero velocity. -/
theorem variationSurface_horizontal_initial_germ
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (v w : TangentSpace S p)
    (q : VariationParameter F p v w) (hqtime : q.down.val 1 = 0) :
    (fun r => variationSurface F p v w (variationHorizontalCurve F p v w q r)) =ᶠ[𝓝 0]
      (fun _ => variationSurface F p v w q) := by
  have hbase : variationSurface F p v w q = p := by
    dsimp only [variationSurface, variationPhase]
    rw [hqtime]
    exact congrArg Sigma.fst (hF ⟨p, v + q.down.val 0 • w⟩).2.1
  filter_upwards [variationHorizontalCurve_germ C F hF p v w q] with r hr
  rw [hbase]
  dsimp only [variationSurface]
  rw [hr]
  simp only [variationPhase, variationPoint_zero, variationPoint_one, hqtime]
  exact congrArg Sigma.fst (hF ⟨p, v + (q.down.val 0 + r) • w⟩).2.1

/-- At (0,1), the horizontal surface germ is the affine line in the actual
fiber exponential, so its derivative is the full fiber differential. -/
theorem variationSurface_horizontal_terminal_germ
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (v w : TangentSpace S p)
    (q : VariationParameter F p v w)
    (hqzero : q.down.val 0 = 0) (hqone : q.down.val 1 = 1) :
    (fun r => variationSurface F p v w (variationHorizontalCurve F p v w q r)) =ᶠ[𝓝 0]
      (fun r => fiberExponential F p (v + r • w)) := by
  filter_upwards [variationHorizontalCurve_germ C F hF p v w q] with r hr
  dsimp only [variationSurface]
  rw [hr]
  simp only [variationPhase, variationPoint_zero, variationPoint_one, hqzero, hqone,
    zero_add, fiberExponential, exponential]

/-- The horizontal differential vanishes at initial time. -/
theorem variationSurface_initial_differential
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (v w : TangentSpace S p)
    (q : VariationParameter F p v w) (hqtime : q.down.val 1 = 0) :
    let R := variationManifold C F hF p v w
    let a := variationChart C F hF p v w
    let ha := variationChart_mem C F hF p v w
    let f := variationSurface F p v w
    let hf := variationSurface_smooth C F hF p v w
    let ds := fullChartConstantField a ha (variationChart_source C F hF p v w) (Pi.single (0 : Fin 2) 1)
    SmoothManifolds.differential R S f hf q (ds.val q) = 0 := by
  dsimp only
  exact fullChart_differential_zero_of_constant
    (variationChart C F hF p v w) (variationChart_mem C F hF p v w) (variationChart_source C F hF p v w)
    (Pi.single (0 : Fin 2) 1) (variationSurface F p v w)
    (variationSurface_smooth C F hF p v w) q (variationHorizontalCurve F p v w q)
    (variationHorizontalCurve_at F p v w q)
    (variationHorizontalCurve_continuousAt C F hF p v w q)
    (variationHorizontalCurve_derivative C F hF p v w q)
    (variationSurface_horizontal_initial_germ C F hF p v w q hqtime)

/-- Terminal horizontal differential comparison in the original tangent
phases, with no nonsingularity or positive-radius hypothesis. -/
theorem variationSurface_terminal_differential
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (v : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F)
    (b : ModelChart n .euclidean M) (hb : b ∈ S.smoothStructure.val)
    (hp : p ∈ b.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F p v ∈ d.source) (w : TangentSpace S p)
    (q : VariationParameter F p v w)
    (hqzero : q.down.val 0 = 0) (hqone : q.down.val 1 = 1) :
    let R := variationManifold C F hF p v w
    let a := variationChart C F hF p v w
    let ha := variationChart_mem C F hF p v w
    let f := variationSurface F p v w
    let hf := variationSurface_smooth C F hF p v w
    let ds := fullChartConstantField a ha (variationChart_source C F hF p v w) (Pi.single (0 : Fin 2) 1)
    (⟨f q, SmoothManifolds.differential R S f hf q (ds.val q)⟩ : Phase S) =
      ⟨fiberExponential F p v, fiberDifferential F p v b hb hp d hd hq w⟩ := by
  dsimp only
  exact fullChart_differential_exponential_endpoint C F hF p v hv b hb hp d hd hq w
    (variationChart C F hF p v w) (variationChart_mem C F hF p v w) (variationChart_source C F hF p v w)
    (Pi.single (0 : Fin 2) 1) (variationSurface F p v w)
    (variationSurface_smooth C F hF p v w) q (variationHorizontalCurve F p v w q)
    (variationHorizontalCurve_at F p v w q)
    (variationHorizontalCurve_continuousAt C F hF p v w q)
    (variationHorizontalCurve_derivative C F hF p v w q)
    (variationSurface_horizontal_terminal_germ C F hF p v w q hqzero hqone)


open SmoothManifolds.BundleOperationsData
noncomputable def variationDs (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) : Field (variationManifold C F hF p v w) :=
  fullChartConstantField (variationChart C F hF p v w)
    (variationChart_mem C F hF p v w) (variationChart_source C F hF p v w)
    (Pi.single (0 : Fin 2) 1)

noncomputable def variationDt (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) : Field (variationManifold C F hF p v w) :=
  fullChartConstantField (variationChart C F hF p v w)
    (variationChart_mem C F hF p v w) (variationChart_source C F hF p v w)
    (Pi.single (1 : Fin 2) 1)

theorem variation_squared_speed
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p) (q : VariationParameter F p v w) :
    let R := variationManifold C F hF p v w
    let f := variationSurface F p v w
    let hf := variationSurface_smooth C F hF p v w
    let dt := variationDt C F hF p v w
    let Z := SmoothManifolds.differential R S f hf q (dt.val q)
    pairing g (f q) Z Z =
      pairing g p (v + q.down.val 0 • w) (v + q.down.val 0 • w) := by
  have hphase := variationSurface_time_phase C F hF p v w q
  have heq := congrArg (fun z : Phase S => pairing g z.1 z.2 z.2) hphase
  exact heq.trans (geodesic_squared_speed g C hC F hF p
    (v + q.down.val 0 • w) (q.down.val 1) q.down.property)

/-- The mixed endpoint pairing is obtained by integrating the actual geodesic variation. -/
theorem exponential_variation_pairing
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v w : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F) :
    let R := variationManifold C F hF p v w
    let f := variationSurface F p v w
    let hf := variationSurface_smooth C F hF p v w
    let ds := variationDs C F hF p v w
    let dt := variationDt C F hF p v w
    let c := variationTimeCurve F hF p v w 0
    pairing g (f (c 1))
      (SmoothManifolds.differential R S f hf (c 1) (dt.val (c 1)))
      (SmoothManifolds.differential R S f hf (c 1) (ds.val (c 1))) = pairing g p v w := by
  let R := variationManifold C F hF p v w
  let a := variationChart C F hF p v w
  have ha : a ∈ R.smoothStructure.val := variationChart_mem C F hF p v w
  have hfull : a.source = univ := variationChart_source C F hF p v w
  let f := variationSurface F p v w
  let hf := variationSurface_smooth C F hF p v w
  let ds := variationDs C F hF p v w
  let dt := variationDt C F hF p v w
  let c := variationTimeCurve F hF p v w 0
  let I := F.interval ⟨p, v⟩
  have h0 : 0 ∈ I.carrier := (hF ⟨p, v⟩).1
  have h1 : 1 ∈ I.carrier := hv
  have htime (t : ℝ) (ht : t ∈ I.carrier) :
      t ∈ (F.interval ⟨p, v + (0 : ℝ) • w⟩).carrier := by simpa only [zero_smul, add_zero] using ht
  have hc (t : ℝ) (ht : t ∈ I.carrier) : ContinuousAt c t :=
    variationTimeCurve_continuousAt F hF p v w 0 t (htime t ht)
  have hcoords (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivAt (fun s => (a (c s)).val) (Pi.single (1 : Fin 2) 1) t :=
    variationTimeCurve_derivative C F hF p v w 0 t (htime t ht)
  let P := P202.PullbackData.bundle (tangentBundle S) R f hf
  letI := P.space.topology
  let CP := PullbackConnections.pullback (tangentBundle S) f hf P C
  have hCP := PullbackConnections.pullback_isPullback (tangentBundle S) f hf P C
  let V := TorsionAndMetric.differentialAlong f hf P ds
  let T := TorsionAndMetric.differentialAlong f hf P dt
  have hV (q) : V.val q = SmoothManifolds.differential R S f hf q (ds.val q) := rfl
  have hT (q) : T.val q = SmoothManifolds.differential R S f hf q (dt.val q) := rfl
  have hacc (t : ℝ) (ht : t ∈ I.carrier) : (CP.cov dt T).val (c t) = 0 := by
    have hvel := fullChart_velocity a ha hfull (Pi.single (1 : Fin 2) 1)
      c t (hc t ht) (hcoords t ht)
    have heq : F.curve ⟨p, v⟩ =ᶠ[𝓝 t]
        (fun s => (⟨f (c s), T.val (c s)⟩ : Phase S)) := by
      filter_upwards [variationTimeCurve_germ F hF p v w 0 t (htime t ht)] with s hs
      have hh := variationSurface_time_phase C F hF p v w (c s)
      change (⟨f (c s), T.val (c s)⟩ : Phase S) = _ at hh
      simpa only [c, hs, variationPhase, variationPoint_zero, variationPoint_one,
        zero_smul, add_zero] using hh.symm
    exact pullback_cov_zero_of_geodesic_germ C f hf P CP hCP T dt c t
      (F.curve ⟨p, v⟩) hvel heq ((hF ⟨p, v⟩).2.2.1 t ht)
  have henergy (t : ℝ) (ht : t ∈ I.carrier) :
      scalarDerivative R (fun q => pairing g (f q) (T.val q) (T.val q))
        (c t) (ds.val (c t)) = 2 * pairing g p v w := by
    let b := variationHorizontalCurve F p v w (c t)
    have hb := variationHorizontalCurve_germ C F hF p v w (c t)
    have hct : (c t).down.val 0 = 0 := by
      have hh := (variationTimeCurve_germ F hF p v w 0 t (htime t ht)).eq_of_nhds
      exact congrFun hh 0 |>.trans (variationPoint_zero 0 t)
    have he : (fun s => pairing g (f (b s)) (T.val (b s)) (T.val (b s))) =ᶠ[𝓝 0]
        (fun s => pairing g p (v + s • w) (v + s • w)) := by
      filter_upwards [hb] with s hs
      have hh := variation_squared_speed g C hC F hF p v w (b s)
      change pairing g (f (b s)) (T.val (b s)) (T.val (b s)) = _ at hh
      change (b s).down.val = variationPoint ((c t).down.val 0 + s) ((c t).down.val 1) at hs
      rw [hs, variationPoint_zero, hct, zero_add] at hh
      exact hh
    have hh := variation_energy_derivative g p v w a ha hfull f hf P T b
      (variationHorizontalCurve_continuousAt C F hF p v w (c t))
      (variationHorizontalCurve_derivative C F hF p v w (c t)) he
    have hb0 : b 0 = c t := variationHorizontalCurve_at F p v w (c t)
    have hh' : scalarDerivative R (fun q => pairing g (f q) (T.val q) (T.val q))
        (b 0) (ds.val (b 0)) = 2 * pairing g p v w := hh
    exact (congrArg (fun q => scalarDerivative R
      (fun z => pairing g (f z) (T.val z) (T.val z)) q (ds.val q)) hb0.symm).trans hh'
  have hzero : V.val (c 0) = 0 := by
    have hct : (c 0).down.val 1 = 0 := by
      have hh := (variationTimeCurve_germ F hF p v w 0 0 (htime 0 h0)).eq_of_nhds
      exact congrFun hh 1 |>.trans (variationPoint_one 0 0)
    exact variationSurface_initial_differential C F hF p v w (c 0) hct
  exact variation_pairing_endpoint g C hC a ha hfull f hf P CP hCP V T hV hT
    I h0 h1 c hc hcoords (pairing g p v w) henergy hacc hzero

/-- Gauss lemma on the entire actual fiber domain of the exponential map. -/
theorem gauss_lemma : P202Specs.Geometry.GaussLemma.gauss_lemmaType.{u} := by
  intro n M _ S g C hC F hF p v hv e he hp d hd hq w
  let L := fiberDifferential F p v e he hp d hd hq
  change pairing g (fiberExponential F p v) (L v) (L w) = pairing g p v w
  let R := variationManifold C F hF p v w
  let f := variationSurface F p v w
  let hf := variationSurface_smooth C F hF p v w
  let ds := variationDs C F hF p v w
  let dt := variationDt C F hF p v w
  let c := variationTimeCurve F hF p v w 0
  have h1 : 1 ∈ (F.interval ⟨p, v + (0 : ℝ) • w⟩).carrier := by
    rw [zero_smul, add_zero]
    exact hv
  have hx : (c 1).down.val = variationPoint 0 1 :=
    (variationTimeCurve_germ F hF p v w 0 1 h1).eq_of_nhds
  have hx0 : (c 1).down.val 0 = 0 := by rw [hx, variationPoint_zero]
  have hx1 : (c 1).down.val 1 = 1 := by rw [hx, variationPoint_one]
  have hV := variationSurface_terminal_differential C F hF p v hv
    e he hp d hd hq w (c 1) hx0 hx1
  change (⟨f (c 1), SmoothManifolds.differential R S f hf (c 1)
    (ds.val (c 1))⟩ : Phase S) = ⟨fiberExponential F p v, L w⟩ at hV
  have hT := variationSurface_time_phase C F hF p v w (c 1)
  change (⟨f (c 1), SmoothManifolds.differential R S f hf (c 1)
    (dt.val (c 1))⟩ : Phase S) = _ at hT
  have hT' : (⟨f (c 1), SmoothManifolds.differential R S f hf (c 1)
      (dt.val (c 1))⟩ : Phase S) = ⟨fiberExponential F p v, L v⟩ := by
    calc
      _ = F.curve ⟨p, v⟩ 1 := by
        simpa only [hx, variationPhase, variationPoint_zero, variationPoint_one,
          zero_smul, add_zero] using hT
      _ = _ := by
        dsimp only [L]
        rw [fiberDifferential_radial C F hF p v hv e he hp d hd hq]
        rfl
  have heq := pairing_eq_of_phase_eq g hT' hV
  have hpair := exponential_variation_pairing g C hC F hF p v w hv
  exact heq.symm.trans hpair

/-- Angular vectors perpendicular to the initial radius remain perpendicular
under the exponential differential, without a rank condition. -/
theorem angular_orthogonality :
    P202Specs.Geometry.GaussLemma.angular_orthogonalityType.{u} := by
  intro n M _ S g C hC F hF p v hv e he hp d hd hq w hw
  exact (gauss_lemma S g C hC F hF p v hv e he hp d hd hq w).trans hw


end P202.Geometry.GaussLemma
