import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.DiffeomorphismLocal
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.LocalSigned
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.ProductsAndSigns

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.DiffeomorphismLocalResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  ExteriorData FormPullbackData OrientationData OrientationProductData
  LocalIntegrationData Set MeasureTheory Filter Module
universe u

/-- The coefficient transformation law for arbitrary intrinsic fiber coordinates.
It is algebraic and therefore applies also to zero-dimensional fibers. -/
theorem topCoefficient_pullback {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (D : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (K : FiberCoordinates S) (L : FiberCoordinates T)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hq : f p ∈ d.source) (ω : Field T n) :
    topCoefficient K c hc p hp (pullbackField S T f D ω) =
      topCoefficient L d hd (f p) hq ω *
        (((L.equiv d hd (f p) hq).toLinearMap.comp (D p)).comp
          (K.equiv c hc p hp).symm.toLinearMap).det := by
  let B : Basis (Fin n) ℝ (TangentSpace T (f p)) :=
    (Pi.basisFun ℝ (Fin n)).map (L.equiv d hd (f p) hq).symm
  have hb (i : Fin n) : B i = CovectorData.coordinateVector L d hd (f p) hq i := by
    simp [B, CovectorData.coordinateVector, Pi.basisFun_apply]
  have hdet : B.det (fun i => D p (CovectorData.coordinateVector K c hc p hp i)) =
      (((L.equiv d hd (f p) hq).toLinearMap.comp (D p)).comp
          (K.equiv c hc p hp).symm.toLinearMap).det := by
    rw [Basis.det_apply, ← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
    congr 1
  unfold topCoefficient pullbackField
  rw [FormPullbackResults.evaluate_fiberPullback]
  have h := congrArg (fun A : AlternatingMap ℝ (TangentSpace T (f p)) ℝ (Fin n) =>
    A (fun i => D p (CovectorData.coordinateVector K c hc p hp i)))
    (AlternatingMap.eq_smul_basis_det (R := ℝ) (M := TangentSpace T (f p)) B (evaluate (TangentSpace T (f p)) n (ω (f p))))
  simpa only [smul_apply, smul_eq_mul, hdet, ← funext hb] using h

/-- Smooth maps pull continuous top forms back to continuous top forms. No
compactness or invertibility is needed for this continuity assertion. -/
theorem continuous_pullback_of_smooth {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f)
    (D : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hD : ∀ p, IsDifferential S T f p (D p))
    (ω : Field T n) (hω : IsContinuousTopForm ω) :
    IsContinuousTopForm (pullbackField S T f D ω) := by
  intro K c hc
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨L⟩ := TangentBundle.fiberCoordinates_exists T
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p.val)
  obtain ⟨U, hU, hpU, H, hH, hHeq⟩ := (hf p.val).2 c hc d hd p.property hfp
  obtain ⟨V, hVeq, hV, hpV⟩ := mem_nhds_iff.mp hHeq
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  have hcc : Continuous (fun x : c.source => (c x.val).val) :=
    continuous_subtype_val.comp (c.continuousOn.comp_continuous continuous_subtype_val
      (fun x => x.property))
  let O : Set c.source := {x | f x.val ∈ d.source ∧ x.val ∈ V ∧ (c x.val).val ∈ U}
  have hO : IsOpen O := by
    convert ((d.open_source.preimage (hfc.comp continuous_subtype_val)).inter
      (hV.preimage continuous_subtype_val)).inter (hU.preimage hcc) using 1
    ext x
    simp only [O, mem_inter_iff, mem_setOf_eq, mem_preimage]
    tauto
  have hpO : p ∈ O := ⟨hfp, hpV, hpU⟩
  have hvO : Continuous (fun x : O => (x.val : c.source)) := continuous_subtype_val
  have hvC : Continuous (fun x : c.source => (x.val : M)) := continuous_subtype_val
  have hfx : Continuous (fun x : O => f x.val.val) := (hfc.comp hvC).comp hvO
  have hcoeffmap : Continuous (fun x : O =>
      (⟨f x.val.val, x.property.1⟩ : d.source)) :=
    hfx.subtype_mk _
  have hcoeff := (hω L d hd).comp hcoeffmap
  have hderH : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ H) U :=
    hH.fderiv_of_isOpen hU (by simp)
  have hder : Continuous (fun x : O => fderiv ℝ H (c x.val.val).val) :=
    hderH.continuousOn.comp_continuous
      (hcc.comp continuous_subtype_val) (fun x => x.property.2.2)
  have heq (x : O) :
      topCoefficient K c hc x.val.val x.val.property (pullbackField S T f D ω) =
      topCoefficient L d hd (f x.val.val) x.property.1 ω *
        (fderiv ℝ H (c x.val.val).val).det := by
    rw [topCoefficient_pullback S T f D K L c d hc hd _ _ x.property.1 ω]
    congr 1
    congr 1
    apply LinearMap.ext
    intro v
    have hrep : (fun y => H (c y).val) =ᶠ[𝓝 x.val.val] (fun y => (d (f y)).val) :=
      Filter.mem_of_superset (hV.mem_nhds x.property.2.1) hVeq
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_coe] using
      differential_jacobian S T f hf x.val.val (D x.val.val) (hD x.val.val)
        c d hc hd x.val.property x.property.1
        (K.equiv c hc x.val.val x.val.property) (L.equiv d hd (f x.val.val) x.property.1)
        (K.isCoordinates c hc _ _) (L.isCoordinates d hd _ _)
        U H hU x.property.2.2 hH hrep ((K.equiv c hc x.val.val x.val.property).symm v)
  have hcont : Continuous (fun x : O =>
      topCoefficient K c hc x.val.val x.val.property (pullbackField S T f D ω)) := by
    simp_rw [heq]
    exact hcoeff.mul (ContinuousLinearMap.continuous_det.comp hder)
  have hwithin := hcont.continuousAt (x := ⟨p, hpO⟩)
  have hw : ContinuousWithinAt
      (fun x : c.source => topCoefficient K c hc x.val x.property
        (pullbackField S T f D ω)) O p :=
    (continuousWithinAt_iff_continuousAt_domRestrict _ hpO).mpr hwithin
  exact hw.continuousAt (hO.mem_nhds hpO)

/-- The continuity clause for the original diffeomorphisms. -/
theorem continuous_pullback :
    Specs.SmoothManifolds.Integration.DiffeomorphismLocal.continuous_pullbackType.{u} := by
  intro n a b M N _ _ S T F E hE η
  exact continuous_pullback_of_smooth S T F.toEquiv F.contDiff_toFun
    (fun p => (E p).toLinearMap) hE η.field η.continuous

/-- An invertible fiber differential neither creates nor removes a zero value. -/
theorem pullback_eq_zero_iff {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p))
    (ω : Field T n) (p : M) :
    pullbackField S T f (fun p => (E p).toLinearMap) ω p = 0 ↔ ω (f p) = 0 := by
  exact (exteriorPower.map_injective_field
    (LinearMap.dualMap_injective_of_surjective (E p).surjective)).eq_iff' (by simp)

/-- Closed support commutes with pullback by a homeomorphism when the fiber
maps are invertible. This supplies both support directions used in localization. -/
theorem pullback_support_eq {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (F : M ≃ₜ N)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F p)) (ω : Field T n) :
    sectionSupport (pullbackField S T F (fun p => (E p).toLinearMap) ω) =
      F ⁻¹' sectionSupport ω := by
  have hz : {p | pullbackField S T F (fun p => (E p).toLinearMap) ω p ≠ 0} =
      F ⁻¹' {q | ω q ≠ 0} := by
    ext p
    exact not_congr (pullback_eq_zero_iff S T F E ω p)
  unfold SmoothManifolds.sectionSupport ModelData.sectionSupport
  rw [hz, F.preimage_closure]

/-- The intrinsic determinant-ray sign is the ratio of the two chart signs
and the sign of the coordinate differential. -/
theorem coordinate_sign {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p))
    (o : Orientation S) (q : Orientation T) (s : SignedCharts S) (t : SignedCharts T)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts q.val t)
    (K : FiberCoordinates S) (L : FiberCoordinates T)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hq : f p ∈ d.source) :
    signValue (orientationSign o q E p) * signValue (t.sign d hd ⟨f p, hq⟩) =
      signValue (s.sign c hc ⟨p, hp⟩) *
      (SignType.sign ((K.equiv c hc p hp).symm.trans
        ((E p).trans (L.equiv d hd (f p) hq))).toLinearMap.det : ℝ) := by
  let U := K.equiv c hc p hp
  let Z := L.equiv d hd (f p) hq
  let A := U.symm.trans ((E p).trans Z)
  let sc := s.sign c hc ⟨p, hp⟩
  let sd := t.sign d hd ⟨f p, hq⟩
  have ho : OrientationResults.coordinateRayEquiv K c hc ⟨p, hp⟩ sc = o.val p := by
    rw [OrientationResults.coordinateRayEquiv_apply]
    exact (hs K c hc ⟨p, hp⟩).choose_spec
  have hq' : OrientationResults.coordinateRayEquiv L d hd ⟨f p, hq⟩ sd = q.val (f p) := by
    rw [OrientationResults.coordinateRayEquiv_apply]
    exact (ht L d hd ⟨f p, hq⟩).choose_spec
  have hro : Module.Ray.map (determinantMap n U) (o.val p) =
      OrientationResults.standardRayEquiv n sc := by
    rw [← ho]
    exact OrientationResults.map_coordinateRayEquiv K c hc ⟨p, hp⟩ sc
  have hrq : Module.Ray.map (determinantMap n Z) (q.val (f p)) =
      OrientationResults.standardRayEquiv n sd := by
    rw [← hq']
    exact OrientationResults.map_coordinateRayEquiv L d hd ⟨f p, hq⟩ sd
  have hiff := OrientationProducts.determinantRay_eq_iff U Z (E p) (o.val p) (q.val (f p))
  rw [hro, hrq, OrientationProducts.topExterior_ray_map] at hiff
  have hn : A.toLinearMap.det ≠ 0 := by
    simpa only [LinearEquiv.coe_det] using A.det.ne_zero
  change signValue (orientationSign o q E p) * signValue sd =
    signValue sc * (SignType.sign A.toLinearMap.det : ℝ)
  simp only [orientationSign, hiff]
  let r := OrientationResults.standardRayEquiv n true
  have hstd (b : Bool) : OrientationResults.standardRayEquiv n b =
      if b then r else -r := rfl
  have hnr : r ≠ -r := Module.Ray.ne_neg_self r
  have hnr' : -r ≠ r := Ne.symm hnr
  have hnn : - -r = r := neg_neg r
  by_cases ha : 0 < A.toLinearMap.det
  · rw [if_pos ha, sign_pos ha]
    cases sc <;> cases sd <;>
      simp [hstd, signValue, hnr, hnr', hnn, -neg_rayOfNeZero]
  · have ha' : A.toLinearMap.det < 0 := lt_of_le_of_ne (le_of_not_gt ha) hn
    rw [if_neg ha, sign_neg ha']
    cases sc <;> cases sd <;>
      simp [hstd, signValue, hnr, hnr', hnn, -neg_rayOfNeZero]

/-- Ambient representative of a coordinate map between possibly different
models. Only its restriction to the relative source is relevant. -/
def ambientMap {n : ℕ} {a b : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b))
    (x : Euclidean n) : Euclidean n :=
  if hx : x ∈ modelSet n a then (e ⟨x, hx⟩).val else 0

@[simp] theorem ambientMap_at {n : ℕ} {a b : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b))
    (x : ModelSpace n a) : ambientMap e x.val = (e x).val := by
  simp only [ambientMap, dif_pos x.property]

/-- The ambient representative has exactly the same injectivity and image
as the model homeomorphism. -/
theorem ambientMap_geometry {n : ℕ} {a b : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b)) :
    InjOn (ambientMap e) (LocalIntegrationResults.ambientDomain e.source) ∧
    ambientMap e '' LocalIntegrationResults.ambientDomain e.source =
      LocalIntegrationResults.ambientDomain e.target := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    simp only [ambientMap_at] at hxy
    exact congrArg Subtype.val (e.injOn hx hy (Subtype.ext hxy))
  · ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e x, e.map_source hx, ambientMap_at e x |>.symm⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(e.symm y).val, ⟨e.symm y, e.map_target hy, rfl⟩, ?_⟩
      rw [ambientMap_at, e.right_inv hy]

/-- An ambient smooth extension differentiates the coordinate map on the full
relative model domain, including any true boundary points. -/
theorem ambientMap_hasFDerivWithinAt {n : ℕ} {a b : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b))
    (x : ModelSpace n a) (hx : x ∈ e.source)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hxU : x.val ∈ U)
    (H : Euclidean n → Euclidean n) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U)
    (heq : ∀ y ∈ e.source, y.val ∈ U → H y.val = (e y).val) :
    HasFDerivWithinAt (ambientMap e) (fderiv ℝ H x.val)
      (LocalIntegrationResults.ambientDomain e.source) x.val := by
  have hder := ((hH.differentiableOn (by simp) x.val hxU).differentiableAt
    (hU.mem_nhds hxU)).hasFDerivAt.hasFDerivWithinAt
    (s := LocalIntegrationResults.ambientDomain e.source)
  refine hder.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU)] with z hz hzU
    obtain ⟨y, hy, rfl⟩ := hz
    rw [ambientMap_at, heq y hy hzU]
  · rw [ambientMap_at, heq x hx hxU]

/-- The coordinate homeomorphism induced by the original diffeomorphism. -/
def coordinateMap {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (F : M ≃ₜ N) (c : ModelChart n a M) (d : ModelChart n b N) :
    OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b) :=
  c.symm.trans (F.toOpenPartialHomeomorph.trans d)

@[simp] theorem coordinateMap_source {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (F : M ≃ₜ N) (c : ModelChart n a M) (d : ModelChart n b N)
    (x : ModelSpace n a) :
    x ∈ (coordinateMap F c d).source ↔ x ∈ c.target ∧ F (c.symm x) ∈ d.source := by
  simp [coordinateMap, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph]

@[simp] theorem coordinateMap_target {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (F : M ≃ₜ N) (c : ModelChart n a M) (d : ModelChart n b N)
    (y : ModelSpace n b) :
    y ∈ (coordinateMap F c d).target ↔ y ∈ d.target ∧ F.symm (d.symm y) ∈ c.source := by
  simp [coordinateMap, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph]

/-- The Fréchet derivative on the relative domain is the original intrinsic
coordinate differential; no transported atlas certificate is assumed. -/
theorem coordinateMap_derivative {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p))
    (hE : ∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap)
    (K : FiberCoordinates S) (L : FiberCoordinates T)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hq : F.toEquiv p ∈ d.source) :
    HasFDerivWithinAt (ambientMap (coordinateMap F.toHomeomorph c d))
      ((((L.equiv d hd (F.toEquiv p) hq).toLinearMap.comp (E p).toLinearMap).comp
        (K.equiv c hc p hp).symm.toLinearMap).toContinuousLinearMap)
      (LocalIntegrationResults.ambientDomain (coordinateMap F.toHomeomorph c d).source)
      (c p).val := by
  let e := coordinateMap F.toHomeomorph c d
  have hx : c p ∈ e.source := by
    exact (coordinateMap_source _ _ _ _).mpr ⟨c.map_source hp, by
      change F.toEquiv (c.symm (c p)) ∈ d.source
      rw [c.left_inv hp]
      exact hq⟩
  obtain ⟨U, hU, hpU, H, hH, heq⟩ :=
    (chartContDiffAt_iff_modelExtension (⊤ : ℕ∞) c d F.toEquiv p hp hq
      (F.contDiff_toFun p).1).mp ((F.contDiff_toFun p).2 c hc d hd hp hq)
  have heq' : ∀ y ∈ e.source, y.val ∈ U → H y.val = (e y).val := by
    intro y hy hyU
    obtain ⟨hyc, hyd⟩ := (coordinateMap_source _ _ _ _).mp hy
    exact heq y hyc hyd hyU
  have hder := ambientMap_hasFDerivWithinAt e (c p) hx U hU hpU H hH heq'
  have hrep : (fun y => H (c y).val) =ᶠ[𝓝 p] (fun y => (d (F.toEquiv y)).val) := by
    filter_upwards [c.open_source.mem_nhds hp,
      (F.contDiff_toFun p).1.preimage_mem_nhds (d.open_source.mem_nhds hq),
      (continuous_subtype_val.continuousAt.comp (c.continuousAt hp)).preimage_mem_nhds
        (hU.mem_nhds hpU)] with y hyc hyd hyU
    simpa only [c.left_inv hyc] using
      heq (c y) (c.map_source hyc) (by simpa only [c.left_inv hyc, mem_preimage] using hyd) hyU
  have hj : (((L.equiv d hd (F.toEquiv p) hq).toLinearMap.comp (E p).toLinearMap).comp
        (K.equiv c hc p hp).symm.toLinearMap).toContinuousLinearMap =
        fderiv ℝ H (c p).val := by
    apply ContinuousLinearMap.ext
    intro v
    simpa only [ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap',
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      differential_jacobian S T F.toEquiv F.contDiff_toFun p (E p).toLinearMap (hE p)
        c d hc hd hp hq (K.equiv c hc p hp) (L.equiv d hd (F.toEquiv p) hq)
        (K.isCoordinates c hc p hp) (L.isCoordinates d hd (F.toEquiv p) hq)
        U H hU hpU hH hrep ((K.equiv c hc p hp).symm v)
  rwa [← hj] at hder

/-- Multiplication by any scalar function can only decrease closed support. -/
theorem weight_support_subset {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (ω : Field S n) (r : M → ℝ) :
    ModelData.sectionSupport (fun p => r p • ω p) ⊆ ModelData.sectionSupport ω := by
  apply closure_mono
  intro p hp hz
  exact hp (by simp [hz])

/-- Coefficient evaluation commutes with pointwise scalar multiplication. -/
theorem topCoefficient_weight {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (ω : Field S n) (r : M → ℝ) :
    topCoefficient K c hc p hp (fun q => r q • ω q) = r p * topCoefficient K c hc p hp ω := by
  simp only [topCoefficient, map_smul, smul_apply, smul_eq_mul]

/-- Signed coordinate naturality. Compactness and continuity are not needed
for this equality of Bochner integrals once both supports lie in the charts. -/
theorem coordinate_naturality_field {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p))
    (hE : ∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap)
    (η : Field T n) (o : Orientation S) (q : Orientation T)
    (s : SignedCharts S) (t : SignedCharts T)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts q.val t)
    (K : FiberCoordinates S) (L : FiberCoordinates T)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hcη : sectionSupport (pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η)
      ⊆ c.source) (hdη : sectionSupport η ⊆ d.source) :
    coordinateIntegral s K c hc (pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η) =
    coordinateIntegral t L d hd
      (fun y => signValue (orientationSign o q E (F.toEquiv.symm y)) • η y) := by
  let ω := pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η
  let r : N → ℝ := fun y => signValue (orientationSign o q E (F.toEquiv.symm y))
  let ξ : Field T n := fun y => r y • η y
  let e := coordinateMap F.toHomeomorph c d
  let U := LocalIntegrationResults.ambientDomain e.source
  let V := LocalIntegrationResults.ambientDomain e.target
  let ψ := ambientMap e
  let J := fderivWithin ℝ ψ U
  let f := signedCoordinateCoefficient s K c hc ω
  let g := signedCoordinateCoefficient t L d hd ξ
  have hU : MeasurableSet U := LocalIntegrationResults.ambientDomain_measurable e.open_source
  have hJ : ∀ x ∈ U, HasFDerivWithinAt ψ (J x) U x := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyc, hyd⟩ := (coordinateMap_source _ _ _ _).mp hy
    have hder := coordinateMap_derivative S T F E hE K L c d hc hd
      (c.symm y) (c.map_target hyc) hyd
    rw [c.right_inv hyc] at hder
    exact hder.differentiableWithinAt.hasFDerivWithinAt
  have hsupp : sectionSupport ω = F.toEquiv ⁻¹' sectionSupport η :=
    pullback_support_eq S T F.toHomeomorph E η
  have hfg : ∀ x ∈ U, |(J x).det| * g (ψ x) = f x := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyc, hyd⟩ := (coordinateMap_source _ _ _ _).mp hy
    let p := c.symm y
    have hp : p ∈ c.source := c.map_target hyc
    have hq : F.toEquiv p ∈ d.source := hyd
    have hcy : c p = y := c.right_inv hyc
    have hψ : ψ y.val = (d (F.toEquiv p)).val := ambientMap_at e y
    have hder := coordinateMap_derivative S T F E hE K L c d hc hd p hp hq
    rw [hcy] at hder
    have hlin : (((L.equiv d hd (F.toEquiv p) hq).toLinearMap.comp (E p).toLinearMap).comp
        (K.equiv c hc p hp).symm.toLinearMap) =
        ((K.equiv c hc p hp).symm.trans ((E p).trans (L.equiv d hd (F.toEquiv p) hq))).toLinearMap := by
      apply LinearMap.ext
      intro v
      rfl
    have hdet : (J y.val).det =
        ((K.equiv c hc p hp).symm.trans ((E p).trans (L.equiv d hd (F.toEquiv p) hq))).toLinearMap.det := by
      have hj := hder.fderivWithin (uniqueDiffOn_modelDomain e.open_source _ ⟨y, hy, rfl⟩)
      change J y.val = _ at hj
      rw [hj]
      change LinearMap.det _ = LinearMap.det _
      exact congrArg LinearMap.det hlin
    change |(J y.val).det| * signedCoordinateCoefficient t L d hd ξ (ψ y.val) =
      signedCoordinateCoefficient s K c hc ω y.val
    rw [hψ, ← hcy,
      LocalIntegrationResults.signedCoefficient_at t L d hd ξ ⟨F.toEquiv p, hq⟩,
      LocalIntegrationResults.signedCoefficient_at s K c hc ω ⟨p, hp⟩]
    change |(J (c p).val).det| *
        (signValue (t.sign d hd ⟨F.toEquiv p, hq⟩) * topCoefficient L d hd (F.toEquiv p) hq ξ) =
      signValue (s.sign c hc ⟨p, hp⟩) * topCoefficient K c hc p hp ω
    rw [hcy, hdet, topCoefficient_weight L d hd _ hq η r,
      topCoefficient_pullback S T F.toEquiv (fun p => (E p).toLinearMap) K L c d hc hd p hp hq η]
    have hr : r (F.toEquiv p) = signValue (orientationSign o q E p) := by
      simp only [r, F.toEquiv.symm_apply_apply]
    rw [hr]
    have hsign := coordinate_sign S T F.toEquiv E o q s t hs ht K L c d hc hd p hp hq
    have halg := LocalIntegrationResults.signed_coefficient_identity
      (signValue (s.sign c hc ⟨p, hp⟩))
      (signValue (orientationSign o q E p) * signValue (t.sign d hd ⟨F.toEquiv p, hq⟩))
      ((K.equiv c hc p hp).symm.trans ((E p).trans (L.equiv d hd (F.toEquiv p) hq))).toLinearMap.det
      (topCoefficient L d hd (F.toEquiv p) hq η) hsign
    rw [hlin]
    convert halg.symm using 1 <;> ring
  have hfU : Function.support f ⊆ U := by
    intro x hx
    obtain ⟨p, hp, hpc, hcx⟩ := LocalIntegrationResults.signedCoefficient_nonzero s K c hc ω x hx
    have hη : F.toEquiv p ∈ sectionSupport η := by
      rw [hsupp] at hp
      exact hp
    rw [← hcx]
    exact ⟨c p, (coordinateMap_source _ _ _ _).mpr
      ⟨c.map_source hpc, by
        change F.toEquiv (c.symm (c p)) ∈ d.source
        rw [c.left_inv hpc]
        exact hdη hη⟩, rfl⟩
  have hgV : Function.support g ⊆ V := by
    intro x hx
    obtain ⟨y, hy, hyd, hdx⟩ := LocalIntegrationResults.signedCoefficient_nonzero t L d hd ξ x hx
    have hη : y ∈ sectionSupport η := weight_support_subset η r hy
    have hω : F.toEquiv.symm y ∈ sectionSupport ω := by
      rw [hsupp]
      simpa only [mem_preimage, F.toEquiv.apply_symm_apply] using hη
    rw [← hdx]
    exact ⟨d y, (coordinateMap_target _ _ _ _).mpr
      ⟨d.map_source hyd, by
        change F.toEquiv.symm (d.symm (d y)) ∈ c.source
        rw [d.left_inv hyd]
        exact hcη hω⟩, rfl⟩
  have hsub := integral_image_eq_integral_abs_det_fderiv_smul volume hU hJ
    (ambientMap_geometry e).1 g
  rw [(ambientMap_geometry e).2] at hsub
  have hfint : (∫ x in U, f x) = ∫ x, f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      not_not.mp (fun hn => hx (hfU hn)))
  have hgint : (∫ x in V, g x) = ∫ x, g x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      not_not.mp (fun hn => hx (hgV hn)))
  change ∫ x, f x = ∫ x, g x
  rw [← hfint, ← hgint, hsub]
  apply setIntegral_congr_fun hU
  intro x hx
  exact (hfg x hx).symm

/-- The local clause in the original compact continuous top-form interface. -/
theorem coordinate_naturality :
    Specs.SmoothManifolds.Integration.DiffeomorphismLocal.coordinate_naturalityType.{u} := by
  intro n a b M N _ _ S T F E hE η o q s t hs ht K L c d hc hd hcη hdη
  exact coordinate_naturality_field S T F E hE η.field o q s t hs ht K L c d hc hd hcη hdη

end SmoothManifolds.DiffeomorphismLocalResults
