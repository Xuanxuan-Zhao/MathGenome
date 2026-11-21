import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GreenDivergenceCore
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.ClassicalFormulas
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ScalarCalculus
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GreenBoundaryFlux
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Stokes

/-! Divergence core of Theorem 6.7. The compact-support density theorem needs no
orientation. The oriented realization uses the actual contraction, derivative,
outward-first boundary volume and compatible density integrals. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology CompactlySupported
namespace P202.Geometry.GreenDivergenceCore
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.BoundaryData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData P202.GreenData
universe u
section Calculus
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem divergence_add (C : Connection (tangentBundle S)) (X Y : Field S) (p : M) :
    divergence C (X + Y) p = divergence C X p + divergence C Y p := by
  have he : pointDerivative C (X + Y).val p =
      pointDerivative C X.val p + pointDerivative C Y.val p := by
    apply LinearMap.ext
    intro v
    exact ConnectionForms.pointDerivative_add_section (tangentBundle S) C X Y p v
  unfold divergence
  rw [he, map_add]

theorem divergence_smul (C : Connection (tangentBundle S)) (t : ℝ)
    (X : Field S) (p : M) : divergence C (t • X) p = t * divergence C X p := by
  have he : pointDerivative C (t • X).val p = t • pointDerivative C X.val p := by
    apply LinearMap.ext
    intro v
    exact ConnectionForms.pointDerivative_smul_section (tangentBundle S) C X t p v
  unfold divergence
  rw [he, map_smul, smul_eq_mul]

theorem divergence_zero (C : Connection (tangentBundle S)) (p : M) :
    divergence C (0 : Field S) p = 0 := by
  have he := divergence_smul C 0 (0 : Field S) p
  simpa using he

theorem divergence_germ_congr (C : Connection (tangentBundle S)) (X Y : Field S)
    (p : M) (h : ∀ᶠ q in nhds p, X.val q = Y.val q) :
    divergence C X p = divergence C Y p := by
  unfold divergence
  exact congrArg (LinearMap.trace ℝ (TangentSpace S p))
    (ConnectionForms.pointDerivative_congr (tangentBundle S) C X.val Y.val p
      ⟨X, Filter.Eventually.of_forall (fun _ => rfl)⟩ h)

theorem divergence_support (C : Connection (tangentBundle S)) (X : Field S) :
    sectionSupport (divergence C X) ⊆ sectionSupport X.val := by
  apply closure_minimal
  · intro p hp
    by_contra hn
    have hz : ∀ᶠ q in nhds p, X.val q = 0 := by
      have hO : IsOpen ((sectionSupport X.val)ᶜ) := isClosed_closure.isOpen_compl
      filter_upwards [hO.mem_nhds hn] with q hq
      by_contra hne
      exact hq (subset_closure hne)
    exact hp ((divergence_germ_congr C X 0 p hz).trans (divergence_zero C p))
  · exact isClosed_closure

theorem divergence_compact_support (C : Connection (tangentBundle S)) (X : Field S)
    (hX : IsCompact (sectionSupport X.val)) : IsCompact (sectionSupport (divergence C X)) :=
  hX.of_isClosed_subset isClosed_closure (divergence_support C X)

theorem divergence_smooth (C : Connection (tangentBundle S)) (X : Field S) (p : M) :
    SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val (divergence C X) p := by
  classical
  obtain ⟨c, hc⟩ := (tangentBundle S).covers p
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hU : IsOpen (B.baseSet c) :=
    B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨p, hc⟩
  let f : M → ℝ := fun q => ∑ i : Fin n, component c (C.cov (e i) X) i q
  have hf : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val f p :=
    SmoothManifolds.FrameData.VectorSmoothAt.sum
      (fun i => ScalarCalculus.component_smooth (C.cov (e i) X) c ⟨p, hc⟩ i)
  apply hf.congr
  have he' := Filter.eventually_all.mpr he
  filter_upwards [he', hU.mem_nhds hc] with q hq hqc
  dsimp only [f]
  unfold divergence
  rw [LinearMap.trace_eq_matrix_trace ℝ (b.basis ⟨q, hqc⟩)]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  have hei : (e i).val q = (b.basis ⟨q, hqc⟩) i := by
    rw [hq i, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hqc]
    rfl
  rw [← hei, ConnectionForms.pointDerivative_global B C]
  change component c (C.cov (e i) X) i q =
    (b.basis ⟨q, hqc⟩).equivFun ((C.cov (e i) X).val q) i
  have hcoord : (b.basis ⟨q, hqc⟩).equivFun = B.fiberCoordinates c q hqc :=
    ScalarCalculus.coordinate_frame_equiv c ⟨q, hqc⟩
  rw [hcoord]
  rfl

theorem divergence_continuous (C : Connection (tangentBundle S)) (X : Field S) :
    Continuous (divergence C X) :=
  continuous_iff_continuousAt.mpr (fun p => (divergence_smooth C X p).1)

/-- The actual divergence can be integrated in the upstream compact-density
interface whenever X has compact support. -/
def compactDivergence (C : Connection (tangentBundle S)) (X : Field S)
    (hX : IsCompact (sectionSupport X.val)) : C_c(M, ℝ) :=
  ⟨⟨divergence C X, divergence_continuous C X⟩, divergence_compact_support C X hX⟩

theorem flux_continuous (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (X : Field S) : Continuous (flux g b X) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨U, hU, hp, N, hN⟩ := b.normal_smooth p
  let f : M → ℝ := fun q => pairing g q (X.val q) (N.val q)
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun q => (TorsionAndMetric.metricPairing_smooth (tangentBundle S) g X N q).1)
  have hcont : ContinuousAt (fun q : intrinsicBoundary S => f q.val) p :=
    hf.continuousAt.comp continuous_subtype_val.continuousAt
  apply hcont.congr
  filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds hp] with q hq
  change pairing g q.val (X.val q.val) (N.val q.val) = flux g b X q
  rw [hN q hq]
  rfl

theorem flux_support (g : RiemannianMetric S) (b : BoundaryGeometry g) (X : Field S) :
    sectionSupport (flux g b X) ⊆ Subtype.val ⁻¹' sectionSupport X.val := by
  apply closure_minimal
  · intro p hp
    by_contra hn
    have hz : X.val p.val = 0 := by
      by_contra hne
      exact hn (subset_closure hne)
    apply hp
    simp only [flux, hz, map_zero, LinearMap.zero_apply]
  · exact isClosed_closure.preimage continuous_subtype_val

theorem flux_compact_support (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (X : Field S) (hX : IsCompact (sectionSupport X.val)) :
    IsCompact (sectionSupport (flux g b X)) := by
  have hpre := ((SmoothManifolds.isClosed_intrinsicBoundary S).isClosedEmbedding_subtypeVal).isCompact_preimage hX
  exact hpre.of_isClosed_subset isClosed_closure (flux_support g b X)

def compactFlux (g : RiemannianMetric S) (b : BoundaryGeometry g) (X : Field S)
    (hX : IsCompact (sectionSupport X.val)) : C_c(intrinsicBoundary S, ℝ) :=
  ⟨⟨flux g b X, flux_continuous g b X⟩, flux_compact_support g b X hX⟩

/-- Divergence is real-linear on the original space of smooth fields. -/
def divergenceLinear (C : Connection (tangentBundle S)) (p : M) : Field S →ₗ[ℝ] ℝ where
  toFun X := divergence C X p
  map_add' X Y := divergence_add C X Y p
  map_smul' t X := divergence_smul C t X p

/-- A locally finite smooth partition gives a genuinely finite global field
decomposition on compact support. Differentiating this *global equality* will
cancel the derivatives of the localizers without any support-boundary exception. -/
theorem finite_field_partition (C : Connection (tangentBundle S)) (X : Field S)
    (hX : IsCompact (sectionSupport X.val)) {ι : Type*} (ρ : ι → GlobalSmooth S)
    (hlf : LocallyFinite (fun i => sectionSupport (ρ i).val))
    (hsum : ∀ p, ∑ᶠ i, (ρ i).val p = 1) :
    ∃ t : Finset ι,
      (∀ i ∉ t, mulSection (ρ i) X = 0) ∧
      X = ∑ i ∈ t, mulSection (ρ i) X ∧
      ∀ p, divergence C X p = ∑ i ∈ t, divergence C (mulSection (ρ i) X) p := by
  classical
  have hfin := hlf.finite_nonempty_inter_compact hX
  let t := hfin.toFinset
  have ht (p : M) (hp : X.val p ≠ 0) : Function.support (fun i => (ρ i).val p) ⊆ t := by
    intro i hi
    exact hfin.mem_toFinset.mpr ⟨p, subset_closure hi, subset_closure hp⟩
  have he : X = ∑ i ∈ t, mulSection (ρ i) X := by
    apply Subtype.ext
    funext p
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change X.val p = ∑ i ∈ t, (ρ i).val p • X.val p
    by_cases hp : X.val p = 0
    · simp [hp]
    · have hs : ∑ i ∈ t, (ρ i).val p = 1 := by
        rw [← finsum_eq_sum_of_support_subset _ (ht p hp)]
        exact hsum p
      rw [← Finset.sum_smul, hs, one_smul]
  refine ⟨t, ?_, he, ?_⟩
  · intro i hi
    apply Subtype.ext
    funext p
    change (ρ i).val p • X.val p = 0
    by_cases hp : X.val p = 0
    · simp [hp]
    · have hρ : (ρ i).val p = 0 := by
        by_contra hn
        exact hi (ht p hp hn)
      rw [hρ, zero_smul]
  · intro p
    have hh := congrArg (divergenceLinear C p) he
    simpa only [map_sum, divergenceLinear, LinearMap.coe_mk, AddHom.coe_mk] using hh

end Calculus

section ZeroDimension
variable {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 0 a M}

theorem divergence_value_zero_dimension (C : Connection (tangentBundle S))
    (X : Field S) (p : M) : divergence C X p = 0 := by
  obtain ⟨c, hc⟩ := (tangentBundle S).covers p
  let e := (tangentBundle S).fiberCoordinates c p hc
  letI : Subsingleton (TangentSpace S p) := e.injective.subsingleton
  unfold divergence
  rw [Subsingleton.elim (pointDerivative C X.val p) 0, map_zero]

theorem divergence_identity_zero_dimension (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g) :
    DivergenceIdentity g C b := by
  intro X _
  refine ⟨0, 0, fun p => ?_, fun p => ?_, ?_⟩
  · exact (divergence_value_zero_dimension C X p).symm
  · exact False.elim (by
      have h := p.property
      have he : intrinsicBoundary S = ∅ := SmoothManifolds.intrinsicBoundary_zero S
      simpa only [he, Set.mem_empty_iff_false] using h)
  · have hz : P202.VolumeData.integral g (0 : C_c(M, ℝ)) = 0 := by
      simpa using RiemannianVolume.integral_smul g 0 (0 : C_c(M, ℝ))
    have hb : P202.VolumeData.integral b.metric (0 : C_c(intrinsicBoundary S, ℝ)) = 0 := by
      simpa using RiemannianVolume.integral_smul b.metric 0 (0 : C_c(intrinsicBoundary S, ℝ))
    exact hz.trans hb.symm

end ZeroDimension


private theorem compactTopForm_ext {d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M}
    (α β : SmoothManifolds.LocalIntegrationData.CompactTopForm S)
    (h : α.field = β.field) : α = β := by
  cases α
  cases β
  cases h
  rfl

section Oriented
open SmoothManifolds.OrientationData SmoothManifolds.LocalIntegrationData
  SmoothManifolds.GlobalIntegrationData SmoothManifolds.ExteriorDerivativeData
  SmoothManifolds.BoundaryOrientationData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold (n+1) a M}

/-- First-slot contraction vanishes wherever the vector field vanishes. -/
theorem contraction_support (g : RiemannianMetric S) (o : Orientation S)
    (X : Field S) :
    sectionSupport (SmoothManifolds.CartanData.contraction
      (P202.VolumeData.cotangentBundle S) X.val (n+1)
      (P202.VolumeData.volumeForm g o).field) ⊆ sectionSupport X.val := by
  apply closure_minimal
  · intro p hp
    by_contra hn
    have hX : X.val p = 0 := by
      by_contra hne
      exact hn (subset_closure hne)
    apply hp
    apply (SmoothManifolds.CartanData.evaluationEquiv
      (P202.VolumeData.cotangentBundle S).tangent.fiberCoordinates p n).injective
    rw [SmoothManifolds.CartanResults.evaluationEquiv_apply, map_zero]
    apply AlternatingMap.ext
    intro v
    rw [SmoothManifolds.CartanResults.contraction_apply, hX]
    exact (SmoothManifolds.ExteriorData.evaluate (TangentSpace S p) (n+1)
      ((P202.VolumeData.volumeForm g o).field p)).map_coord_zero 0
        (by simp : Matrix.vecCons (0 : TangentSpace S p) v 0 = 0)
  · exact isClosed_closure

/-- No flow or tangency condition is needed at a true boundary point. -/
theorem contraction_regular_compact :
    P202Specs.Geometry.GreenDivergenceCore.contraction_regular_compactType.{u} := by
  intro n a M _ S g o X hX
  let C := P202.VolumeData.cotangentBundle S
  let B : ∀ k, SmoothManifolds.ExteriorData.FormBundle C k := fun k =>
    Classical.choice (SmoothManifolds.ExteriorAlgebraResults.exists_formBundle C k)
  have hv : SmoothManifolds.ExteriorData.IsForm (B (n+1))
      (P202.VolumeData.volumeForm g o).field :=
    (SmoothManifolds.ExteriorAlgebraResults.smooth_iff_coefficients C (n+1)
      (B (n+1)) _).mpr
      ((SmoothManifolds.ExteriorAlgebraResults.smooth_iff_coefficients C (n+1)
        (P202.VolumeData.topFormBundle S) _).mp (P202.VolumeData.volumeForm g o).smooth)
  have hw := SmoothManifolds.CartanResults.contraction_smooth C B
    (originalField S X) (n+1) (P202.VolumeData.volumeForm g o).field hv
  refine ⟨SmoothManifolds.ExteriorDerivativeResults.smooth_regular C n (B n) _ 1 hw,
    hX.of_isClosed_subset isClosed_closure (contraction_support g o X)⟩

/-- This assembly is conditional only on the pointwise differential identity.
Stokes is applied to the actual contraction, and both signed form integrals
are then identified with the fixed metric density integrals. -/
theorem oriented_stokes_from_derivative :
    P202Specs.Geometry.GreenDivergenceCore.oriented_stokes_from_derivativeType.{u} := by
  intro hD n a M _ S g C hC b o X hX
  obtain ⟨q, hq, hflux⟩ := GreenBoundaryFlux.boundary_flux g b o
  have hreg := contraction_regular_compact g o X hX
  let ω := SmoothManifolds.CartanData.contraction (P202.VolumeData.cotangentBundle S)
    X.val (n+1) (P202.VolumeData.volumeForm g o).field
  let F := compactDivergence C X hX
  let Q := compactFlux g b X hX
  let η := GreenBoundaryFlux.compactMetricForm g o F
  let β := GreenBoundaryFlux.compactMetricForm b.metric q Q
  have hη : HasExteriorDerivative (P202.VolumeData.cotangentBundle S) ω η.field :=
    hD g C hC o X
  have hβ : β.field = SmoothManifolds.FormPullbackData.pullbackField b.manifold S Subtype.val
      (SmoothManifolds.differential b.manifold S Subtype.val b.natural.1) ω :=
    (hflux X).symm
  refine ⟨q, hq, hreg.1, hreg.2, η, β, F, Q, hη, rfl, hβ, rfl,
    fun _ => rfl, fun _ => rfl, ?_⟩
  intro I J hI hJ
  obtain ⟨ζ, γ, hζ, _, hγ, he⟩ := SmoothManifolds.StokesResults.stokes S
    (P202.VolumeData.cotangentBundle S) b.manifold
    (P202.VolumeData.cotangentBundle b.manifold) b.natural o q hq
    (SmoothManifolds.differential b.manifold S Subtype.val b.natural.1)
    (SmoothManifolds.differential_spec b.manifold S Subtype.val b.natural.1)
    I J hI hJ ω hreg.1 hreg.2
  have heη : ζ = η := compactTopForm_ext ζ η
    (SmoothManifolds.ExteriorDerivativeResults.derivative_unique
      (P202.VolumeData.cotangentBundle S) n ω ζ.field η.field hζ hη)
  have heβ : γ = β := compactTopForm_ext γ β (hγ.trans hβ.symm)
  refine ⟨heη ▸ heβ ▸ he, ?_, ?_⟩
  · exact GreenBoundaryFlux.metric_integral_eq g o F η rfl I hI
  · exact GreenBoundaryFlux.metric_integral_eq b.metric q Q β rfl J hJ

end Oriented


section Localization
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Scalar multiplication cannot enlarge either closed support. -/
theorem mulSection_support (f : GlobalSmooth S) (X : Field S) :
    sectionSupport (mulSection f X).val ⊆ sectionSupport f.val ∩ sectionSupport X.val := by
  apply closure_minimal
  · intro p hp
    constructor
    · apply subset_closure
      intro hf
      apply hp
      change f.val p • X.val p = 0
      rw [hf, zero_smul]
    · apply subset_closure
      intro hX
      apply hp
      change f.val p • X.val p = 0
      rw [hX, smul_zero]
  · exact isClosed_closure.inter isClosed_closure

theorem metric_integral_zero (g : RiemannianMetric S) :
    P202.VolumeData.integral g (0 : C_c(M, ℝ)) = 0 := by
  simpa using RiemannianVolume.integral_smul g 0 (0 : C_c(M, ℝ))

/-- The representatives and the integral equality are both preserved by sums. -/
theorem integral_identity_add {m : ℕ} {k : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m k N} (g : RiemannianMetric S) (h : RiemannianMetric T)
    {f f' : M → ℝ} {q q' : N → ℝ}
    (hf : IntegralIdentity g h f q) (hf' : IntegralIdentity g h f' q') :
    IntegralIdentity g h (f + f') (q + q') := by
  obtain ⟨F, Q, hF, hQ, he⟩ := hf
  obtain ⟨F', Q', hF', hQ', he'⟩ := hf'
  refine ⟨F + F', Q + Q', fun p => ?_, fun p => ?_, ?_⟩
  · change F p + F' p = f p + f' p
    rw [hF, hF']
  · change Q p + Q' p = q p + q' p
    rw [hQ, hQ']
  · change RiemannianVolume.integral g (F + F') = RiemannianVolume.integral h (Q + Q')
    rw [RiemannianVolume.integral_add, RiemannianVolume.integral_add]
    exact congrArg₂ (fun x y : ℝ => x + y) he he' 

theorem integral_identity_sum {m : ℕ} {k : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m k N} (g : RiemannianMetric S) (h : RiemannianMetric T)
    {ι : Type*} (t : Finset ι) (f : ι → M → ℝ) (q : ι → N → ℝ)
    (hi : ∀ i, IntegralIdentity g h (f i) (q i)) :
    IntegralIdentity g h (∑ i ∈ t, f i) (∑ i ∈ t, q i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨0, 0, fun _ => rfl, fun _ => rfl,
      (metric_integral_zero g).trans (metric_integral_zero h).symm⟩
  | @insert i t hit ih =>
    simpa only [Finset.sum_insert hit] using integral_identity_add g h (hi i) ih

/-- Once a chart-supported density theorem is proved, no global orientation
is required to assemble it. The finite global field equality, rather than a
pointwise truncation, makes every derivative of a localizer cancel. -/
theorem divergence_from_chart_supported :
    P202Specs.Geometry.GreenDivergenceCore.divergence_from_chart_supportedType.{u} := by
  intro hlocal n a M _ S g C hC b X hX
  classical
  let ι := {c : ModelChart n a M // c ∈ S.smoothStructure.val}
  obtain ⟨w, hw, hsub⟩ := SmoothManifolds.exists_smooth_partition S
    (fun c : ι => c.val.source) (fun c => c.val.open_source) (fun p => by
      obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
      exact ⟨⟨c, hc⟩, hp⟩)
  let ρ : ι → GlobalSmooth S := fun c =>
    ⟨w c, (SmoothManifolds.mem_globalSmoothAlgebra_iff S (w c)).mpr (hw.1 c)⟩
  obtain ⟨t, _, he, hd⟩ := finite_field_partition C X hX ρ hw.2.2.1 hw.2.2.2
  have hcomp (c : ι) : IsCompact (sectionSupport (mulSection (ρ c) X).val) :=
    hX.of_isClosed_subset isClosed_closure
      (fun _ hp => (mulSection_support (ρ c) X hp).2)
  have hsupp (c : ι) : sectionSupport (mulSection (ρ c) X).val ⊆ c.val.source :=
    fun _ hp => hsub c (mulSection_support (ρ c) X hp).1
  have hi (c : ι) : IntegralIdentity g b.metric
      (divergence C (mulSection (ρ c) X)) (flux g b (mulSection (ρ c) X)) :=
    hlocal g C hC b (mulSection (ρ c) X) (hcomp c) c.val c.property (hsupp c)
  have hiSum := integral_identity_sum g b.metric t
    (fun c => divergence C (mulSection (ρ c) X))
    (fun c => flux g b (mulSection (ρ c) X)) hi
  have hdiv : (∑ c ∈ t, divergence C (mulSection (ρ c) X)) = divergence C X :=
    by
      funext p
      simpa only [Finset.sum_apply] using (hd p).symm
  have hflux : (∑ c ∈ t, flux g b (mulSection (ρ c) X)) = flux g b X := by
    conv_rhs => rw [he]
    funext p
    simp only [flux, Submodule.coe_sum, Finset.sum_apply, map_sum, LinearMap.sum_apply]
  rw [hdiv, hflux] at hiSum
  exact hiSum

end Localization


section Representatives
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Actual compact continuous representatives for both density integrals. -/
theorem divergence_flux_representatives :
    P202Specs.Geometry.GreenDivergenceCore.divergence_flux_representativesType.{u} := by
  intro n a M _ S g C b X hX
  exact ⟨compactDivergence C X hX, compactFlux g b X hX,
    fun _ => rfl, fun _ => rfl⟩

theorem divergence_identity_iff (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g) :
    DivergenceIdentity g C b ↔ ∀ (X : Field S) (hX : IsCompact (sectionSupport X.val)),
      P202.VolumeData.integral g (compactDivergence C X hX) =
        P202.VolumeData.integral b.metric (compactFlux g b X hX) := by
  constructor
  · intro hD X hX
    obtain ⟨F, Q, hF, hQ, he⟩ := hD X hX
    have hFe : F = compactDivergence C X hX := by ext p; exact hF p
    have hQe : Q = compactFlux g b X hX := by ext p; exact hQ p
    exact hFe ▸ hQe ▸ he
  · intro hD X hX
    exact ⟨compactDivergence C X hX, compactFlux g b X hX,
      fun _ => rfl, fun _ => rfl, hD X hX⟩
end Representatives

section LocalModel
open SmoothManifolds.ClassicalData
/-- The full-space local calculation, with no restrictions on the Gram matrix. -/
theorem weighted_flux_derivative {n : ℕ} (r : Euclidean (n+1) → ℝ)
    (X : Euclidean (n+1) → Euclidean (n+1)) (x : Euclidean (n+1))
    (hr : DifferentiableAt ℝ r x) (hX : DifferentiableAt ℝ X x) :
    extDeriv (fun y => r y • fluxForm X y) x =
      (∑ i : Fin (n+1), fderiv ℝ (fun y => r y • X y) x (frame (n+1) i) i) •
        volume (n+1) := by
  have he : (fun y => r y • fluxForm X y) = fluxForm (fun y => r y • X y) := by
    funext y
    exact ((volume (n+1)).curryLeft.map_smul (r y) (X y)).symm
  rw [he, ← extDerivWithin_univ]
  have h := SmoothManifolds.ClassicalResults.divergence_form n Set.univ
    (fun y => r y • X y) x (uniqueDiffWithinAt_univ) ((hr.smul hX).differentiableWithinAt)
  simpa only [divergenceWithin, partialWithin, fderivWithin_univ] using h

end LocalModel

section CoordinateFlux
open SmoothManifolds hiding SmoothManifold ModelChart TangentSpace Euclidean modelSet ModelSpace sectionSupport
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData
  SmoothManifolds.LocalIntegrationData SmoothManifolds.ClassicalData
  SmoothManifolds.BundleOperationsData SmoothManifolds.FormPullbackData
  SmoothManifolds.VectorFieldData

set_option maxHeartbeats 2400000 in
theorem contraction_coordinates_flux {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (n+1) a M} (C : CotangentBundle S)
    (X : VectorFieldData.Section S) (σ : ExteriorData.Field S (n+1))
    (c : ModelChart (n+1) a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv (n+1) n
      (fun I => coefficients C n c hc (CartanData.contraction C X (n+1) σ) p I) =
    topCoefficient C.tangent.fiberCoordinates c hc p.val p.property σ •
      (volume (n+1)).curryLeft
        (C.tangent.fiberCoordinates.equiv c hc p.val p.property (X p.val)) := by
  let E := C.tangent.fiberCoordinates.equiv c hc p.val p.property
  let A := ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv (n+1) (n+1)
    (fun I => coefficients C (n+1) c hc σ p I)
  have hA : A = topCoefficient C.tangent.fiberCoordinates c hc p.val p.property σ •
      volume (n+1) := by
    rw [ClassicalResults.topForm_eq_coefficient_volume A]
    congr 1
    unfold topCoefficient CovectorData.coordinateVector
    simpa only [A, E, coefficients, Module.Basis.equivFun_apply, topCoefficient,
      CovectorData.coordinateVector, frame] using
      (@ExteriorDerivativeResults.coefficientAlternating_evaluate.{u}
        (TangentSpace S p.val) _ _ (n+1) (n+1) E
        (σ p.val) (frame (n+1)))
  apply ContinuousAlternatingMap.ext
  intro v
  have hleft := @ExteriorDerivativeResults.coefficientAlternating_evaluate.{u}
        (TangentSpace S p.val) _ _ (n+1) n E
    (CartanData.contraction C X (n+1) σ p.val) v
  change _ = topCoefficient C.tangent.fiberCoordinates c hc p.val p.property σ *
    (volume (n+1)).curryLeft (E (X p.val)) v
  simp only [E, Module.Basis.equivFun_apply] at hleft
  dsimp only [coefficients]
  rw [hleft, CartanResults.contraction_apply]
  have hAeval := @ExteriorDerivativeResults.coefficientAlternating_evaluate.{u}
    (TangentSpace S p.val) _ _ (n+1) (n+1) E (σ p.val) (Matrix.vecCons (E (X p.val)) v)
  have htuple : (fun i => E.symm (Matrix.vecCons (E (X p.val)) v i)) =
      Matrix.vecCons (X p.val) (fun i => E.symm (v i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [htuple] at hAeval
  simp only [E, Module.Basis.equivFun_apply] at hAeval
  rw [← hAeval]
  change A (Matrix.vecCons (E (X p.val)) v) = _
  rw [hA]
  rfl

end CoordinateFlux

end P202.Geometry.GreenDivergenceCore


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
namespace P202.Geometry.GreenDivergenceCore
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData SmoothManifolds.BundleData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem scalarDerivative_ambient (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) {f : M → ℝ}
    (hf : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val f p)
    (F : Euclidean n → ℝ) (U : Set (Euclidean n))
    (hU : IsOpen U) (hpU : (c p).val ∈ U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (he : (fun q => F (c q).val) =ᶠ[nhds p] f) (v : TangentSpace S p) :
    scalarDerivative S f p v = fderiv ℝ F (c p).val
      ((tangentStructure S).fiberCoordinates.equiv c hc p hp v) := by
  apply SmoothManifolds.VectorFields.tangent_action_coordinates S
    (tangentStructure S).fiberCoordinates p c hc hp v (scalarGerm S f p) F
  exact ⟨⟨U, hU, hpU, hF⟩,
    (Filter.Germ.coe_eq.mpr he).trans (ScalarCalculus.scalarGerm_val hf).symm⟩

theorem coordinateVector_coordinates (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : M) (hp : p ∈ c.val.source) (i : Fin n) :
    (tangentStructure S).fiberCoordinates.equiv c.val c.property p hp (coordinateVector c i p) =
      Pi.single i 1 := by
  have hpc : p ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  have he := (tangentRealization S).coordinates c p hp (coordinateVector c i p)
  rw [← he]
  change (tangentBundle S).fiberCoordinates c p hpc
    (((tangentBundle S).fiberCoordinates c p hpc).symm (Pi.single i 1)) = _
  exact ((tangentBundle S).fiberCoordinates c p hpc).apply_symm_apply _

theorem coordinateDerivative_ambient (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : M) (hp : p ∈ c.val.source) (i : Fin n) {f : M → ℝ}
    (hf : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val f p)
    (F : Euclidean n → ℝ) (U : Set (Euclidean n))
    (hU : IsOpen U) (hpU : (c.val p).val ∈ U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (he : (fun q => F (c.val q).val) =ᶠ[nhds p] f) :
    coordinateDerivative c i f p = fderiv ℝ F (c.val p).val (Pi.single i 1) := by
  unfold coordinateDerivative
  rw [scalarDerivative_ambient c.val c.property p hp hf F U hU hpU hF he,
    coordinateVector_coordinates c p hp i]

theorem scalarDerivative_const_mul {f : M → ℝ} {p : M}
    (hf : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val f p)
    (t : ℝ) (v : TangentSpace S p) :
    scalarDerivative S (fun q => t * f q) p v = t * scalarDerivative S f p v := by
  have htf : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q => t * f q) p := hf.postcomp (contDiff_const.mul contDiff_id)
  have hg : scalarGerm S (fun q => t * f q) p = t • scalarGerm S f p := by
    apply Subtype.ext
    rw [ScalarCalculus.scalarGerm_val htf]
    change _ = t • (scalarGerm S f p).val
    rw [ScalarCalculus.scalarGerm_val hf]
    rfl
  change v.val (scalarGerm S (fun q => t * f q) p) = t * v.val (scalarGerm S f p)
  rw [hg, map_smul, smul_eq_mul]

theorem divergence_weighted_ambient (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C) (X : Field S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : M) (hp : p ∈ c.val.source) (t : ℝ)
    (W : Euclidean n → Euclidean n) (U : Set (Euclidean n))
    (hU : IsOpen U) (hpU : (c.val p).val ∈ U)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W U)
    (he : (fun q => W (c.val q).val) =ᶠ[nhds p]
      (fun q i => t * (rho g c q * component c X i q))) :
    (∑ i : Fin n, fderiv ℝ W (c.val p).val (Pi.single i 1) i) =
      t * (rho g c p * divergence C X p) := by
  have hpc : p ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hi (i : Fin n) : fderiv ℝ W (c.val p).val (Pi.single i 1) i =
      t * coordinateDerivative c i (fun q => rho g c q * component c X i q) p := by
    have hf := ScalarCalculus.vectorSmooth_mul (ScalarCalculus.rho_smooth g c ⟨p,hpc⟩)
      (ScalarCalculus.component_smooth X c ⟨p,hpc⟩ i)
    have ht := hf.postcomp ((contDiff_const (c := t)).mul contDiff_id)
    have hei : (fun q => W (c.val q).val i) =ᶠ[nhds p]
        (fun q => t * (rho g c q * component c X i q)) :=
      he.mono (fun q hq => congrFun hq i)
    have hd := coordinateDerivative_ambient c p hp i ht (fun y => W y i)
      U hU hpU (contDiffOn_pi.mp hW i) hei
    simp only [id_eq] at hd
    rw [show coordinateDerivative c i (fun q => t * (rho g c q * component c X i q)) p =
        t * coordinateDerivative c i (fun q => rho g c q * component c X i q) p from
      scalarDerivative_const_mul hf t (coordinateVector c i p)] at hd
    rw [hd]
    rw [fderiv_apply ((hW.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))]
    rfl
  simp_rw [hi]
  rw [← Finset.mul_sum]
  congr 1
  rw [ScalarCalculus.divergence_coordinates g C hC X c ⟨p,hpc⟩]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (ScalarCalculus.rho_positive g c ⟨p,hpc⟩)), one_mul]
end P202.Geometry.GreenDivergenceCore
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
namespace P202.Geometry.GreenDivergenceCore.CoordinateForms
open SmoothManifolds hiding SmoothManifold ModelChart TangentSpace Euclidean modelSet ModelSpace sectionSupport
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData
  SmoothManifolds.ExteriorDerivativeData SmoothManifolds.LocalIntegrationData
  SmoothManifolds.ClassicalData SmoothManifolds.BundleOperationsData
  SmoothManifolds.FormPullbackData SmoothManifolds.VectorFieldData
universe u

theorem exterior_ext_of_coordinate_evaluation {V : Type u} [AddCommGroup V] [Module ℝ V]
    {n k : ℕ} (E : V ≃ₗ[ℝ] Euclidean n) (ξ η : Fiber V k)
    (h : ∀ v : Fin k → Euclidean n,
      evaluate V k ξ (fun i => E.symm (v i)) = evaluate V k η (fun i => E.symm (v i))) :
    ξ = η := by
  apply (((Pi.basisFun ℝ (Fin n)).map E.symm).dualBasis.exteriorPower k).equivFun.injective
  apply (SmoothManifolds.ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k).injective
  apply ContinuousAlternatingMap.ext
  intro v
  rw [SmoothManifolds.ExteriorDerivativeResults.coefficientAlternating_evaluate,
    SmoothManifolds.ExteriorDerivativeResults.coefficientAlternating_evaluate]
  exact h v


/-- An ambient representative of the actual coordinate flux computes its exterior derivative. -/
theorem coordinate_derivative_flux_extension {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (n+1) a M} (C : CotangentBundle S)
    (ω : ExteriorData.Field S n)
    (c : ModelChart (n+1) a M) (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (U : Set (Euclidean (n+1))) (hU : IsOpen U) (hpU : (c p.val).val ∈ U)
    (W : Euclidean (n+1) → Euclidean (n+1)) (hW : ContDiffOn ℝ 1 W U)
    (heW : ∀ q : c.source, (c q.val).val ∈ U →
      ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv (n+1) n
        (fun I => coefficients C n c hc ω q I) = fluxForm W (c q.val).val)
    (v : Fin (n+1) → Euclidean (n+1)) :
    evaluate (TangentSpace S p.val) (n+1)
      (ExteriorDerivativeData.coordinateDerivative C n c hc ω p.val p.property)
      (fun i => (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm (v i)) =
      (∑ i : Fin (n+1), fderiv ℝ W (c p.val).val (frame (n+1) i) i) *
        volume (n+1) v := by
  let e := ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv (n+1) n
  let F : Euclidean (n+1) → Index (n+1) n → ℝ := fun y => e.symm (fluxForm W y)
  have hF : ContDiffOn ℝ 1 F U := e.symm.toContinuousLinearMap.contDiff.comp_contDiffOn
    ((volume (n+1)).curryLeft.contDiff.comp_contDiffOn hW)
  have heF : ∀ q : c.source, (c q.val).val ∈ U → F (c q.val).val =
      fun I => coefficients C n c hc ω q I := by
    intro q hq
    apply e.injective
    exact (e.apply_symm_apply _).trans (heW q hq).symm
  rw [ExteriorDerivativeResults.coordinateDerivative_evaluate_extension C n c hc
    ω p.val p.property U hU hpU F hF heF v]
  have he : (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv
      (n+1) n (F z)) = fluxForm W := by
    funext z
    exact e.apply_symm_apply (fluxForm W z)
  rw [he, ← extDerivWithin_univ]
  have hWd := (hW.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num)
  have hd := SmoothManifolds.ClassicalResults.divergence_form n Set.univ W
    (c p.val).val uniqueDiffWithinAt_univ hWd.differentiableWithinAt
  rw [hd]
  simp only [divergenceWithin, partialWithin, fderivWithin_univ,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- Any top field is its top coefficient times determinant volume in coordinates. -/
theorem top_field_evaluate_coordinates {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (σ : ExteriorData.Field S n) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) (v : Fin n → Euclidean n) :
    evaluate (TangentSpace S p.val) n (σ p.val)
      (fun i => (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm (v i)) =
      topCoefficient C.tangent.fiberCoordinates c hc p.val p.property σ * volume n v := by
  let E := C.tangent.fiberCoordinates.equiv c hc p.val p.property
  let A := ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n n
    (fun I => coefficients C n c hc σ p I)
  have hA : A = topCoefficient C.tangent.fiberCoordinates c hc p.val p.property σ •
      volume n := by
    rw [ClassicalResults.topForm_eq_coefficient_volume A]
    congr 1
    unfold topCoefficient CovectorData.coordinateVector
    simpa only [A, E, coefficients, Module.Basis.equivFun_apply, topCoefficient,
      CovectorData.coordinateVector, frame] using
      (@ExteriorDerivativeResults.coefficientAlternating_evaluate.{u}
        (TangentSpace S p.val) _ _ n n E (σ p.val) (frame n))
  have hh := @ExteriorDerivativeResults.coefficientAlternating_evaluate.{u}
    (TangentSpace S p.val) _ _ n n E (σ p.val) v
  simp only [E, Module.Basis.equivFun_apply] at hh
  rw [← hh]
  change A v = _
  rw [hA]
  rfl

/-- Equality of top forms follows from their determinant-coordinate evaluations. -/
theorem coordinate_derivative_eq_smul_of_flux_extension {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold (n+1) a M}
    (C : CotangentBundle S) (ω : ExteriorData.Field S n)
    (σ : ExteriorData.Field S (n+1)) (c : ModelChart (n+1) a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (U : Set (Euclidean (n+1))) (hU : IsOpen U) (hpU : (c p.val).val ∈ U)
    (W : Euclidean (n+1) → Euclidean (n+1)) (hW : ContDiffOn ℝ 1 W U)
    (heW : ∀ q : c.source, (c q.val).val ∈ U →
      ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv (n+1) n
        (fun I => coefficients C n c hc ω q I) = fluxForm W (c q.val).val)
    (z : ℝ) (hz : (∑ i : Fin (n+1), fderiv ℝ W (c p.val).val (frame (n+1) i) i) =
      z * topCoefficient C.tangent.fiberCoordinates c hc p.val p.property σ) :
    ExteriorDerivativeData.coordinateDerivative C n c hc ω p.val p.property = z • σ p.val := by
  apply exterior_ext_of_coordinate_evaluation (V := TangentSpace S p.val)
    (n := n+1) (k := n+1) (C.tangent.fiberCoordinates.equiv c hc p.val p.property)
    (ExteriorDerivativeData.coordinateDerivative C n c hc ω p.val p.property) (z • σ p.val)
  intro v
  rw [coordinate_derivative_flux_extension C ω c hc p U hU hpU W hW heW v,
    map_smul, smul_apply, smul_eq_mul,
    top_field_evaluate_coordinates C σ c hc p v, hz]
  ring

end P202.Geometry.GreenDivergenceCore.CoordinateForms
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.GreenDivergenceCore.CoordinateForms
open SmoothManifolds hiding SmoothManifold ModelChart TangentSpace Euclidean modelSet ModelSpace sectionSupport
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.CovectorData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.OrientationData
  SmoothManifolds.LocalIntegrationData SmoothManifolds.FormPullbackData SmoothManifolds.MetricVolumeData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem fiberCoordinates_unique (K L : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    K.equiv c hc p.val p.property = L.equiv c hc p.val p.property :=
  SmoothManifolds.TangentBundle.chartCoordinates_unique
    (K.isCoordinates c hc p.val p.property) (L.isCoordinates c hc p.val p.property)

theorem realized_coordinates_eq (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (hp : p.val ∈ (tangentBundle S).baseSet ⟨c, hc⟩) :
    (tangentBundle S).fiberCoordinates ⟨c, hc⟩ p.val hp =
      K.equiv c hc p.val p.property := by
  apply LinearEquiv.ext
  intro v
  rw [SmoothVectorBundle.fiberCoordinates_apply, (tangentRealization S).coordinates]
  exact LinearEquiv.congr_fun
    (fiberCoordinates_unique (tangentStructure S).fiberCoordinates K c hc p) v

theorem gramMatrix_eq_metricMatrix (g : RiemannianMetric S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    P202.VolumeData.gramMatrix g K c hc p = metricMatrix g ⟨c, hc⟩ p.val := by
  have hp : p.val ∈ (tangentBundle S).baseSet ⟨c, hc⟩ := by
    rw [(tangentRealization S).baseSet]
    exact p.property
  have heq (i : Fin n) : P202.LeviCivitaData.coordinateVector ⟨c, hc⟩ i p.val =
      (K.equiv c hc p.val p.property).symm ((Pi.basisFun ℝ (Fin n)) i) := by
    rw [P202.LeviCivitaData.coordinateVector,
      ← SmoothVectorBundle.fiberCoordinates_symm_apply (tangentBundle S) ⟨c, hc⟩ p.val hp,
      realized_coordinates_eq K c hc p hp]
    simp
  ext i j
  simp only [P202.VolumeData.gramMatrix, Matrix.of_apply, P202.LeviCivitaData.metricMatrix, heq]

theorem coordinates_eq_components (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) (X : Field S) :
    K.equiv c hc p.val p.property (X.val p.val) =
      fun i => component ⟨c, hc⟩ X i p.val := by
  have hp : p.val ∈ (tangentBundle S).baseSet ⟨c, hc⟩ := by
    rw [(tangentRealization S).baseSet]
    exact p.property
  rw [← realized_coordinates_eq K c hc p hp, SmoothVectorBundle.fiberCoordinates_apply]
  rfl

theorem volume_topCoefficient_rho (g : RiemannianMetric S) (o : Orientation S)
    (s : SignedCharts S) (hs : RepresentsSignedCharts o.val s)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) :
    topCoefficient K c hc p.val p.property (P202.VolumeData.volumeForm g o).field =
      signValue (s.sign c hc p) * rho g ⟨c, hc⟩ p.val := by
  rw [GreenBoundaryFlux.volume_topCoefficient g o s hs K c hc p,
    (RiemannianVolume.density_coordinates g K c hc p).1,
    gramMatrix_eq_metricMatrix g K c hc p]
  rfl

end P202.Geometry.GreenDivergenceCore.CoordinateForms
namespace P202.Geometry.GreenDivergenceCore
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData SmoothManifolds.BundleData
  SmoothManifolds.OrientationData SmoothManifolds.LocalIntegrationData
  SmoothManifolds.ExteriorDerivativeData SmoothManifolds.FormPullbackData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData
open CoordinateForms
universe u
set_option maxHeartbeats 4000000 in
theorem contraction_derivative :
    P202Specs.Geometry.GreenDivergenceCore.contraction_derivativeType.{u} := by
  intro n a M _ S g C hC o X c hc p hp
  classical
  let D := P202.VolumeData.cotangentBundle S
  let K := D.tangent.fiberCoordinates
  let σ := (P202.VolumeData.volumeForm g o).field
  let ω := SmoothManifolds.CartanData.contraction D X.val (n+1) σ
  obtain ⟨s, hs, _⟩ := SmoothManifolds.LocalIntegrationResults.orientation_signs S o
  let ε := signValue (s.sign c hc ⟨p,hp⟩)
  let ci : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c,hc⟩
  let f : M → Euclidean (n+1) := fun q => if hq : q ∈ c.source then
    topCoefficient K c hc q hq σ • K.equiv c hc q hq (X.val q) else 0
  have hpc : p ∈ (tangentBundle S).baseSet ci := by
    rw [(tangentRealization S).baseSet]
    exact hp
  have hf0 : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q i => ε * (rho g ci q * component ci X i q)) p :=
    SmoothManifolds.FrameData.VectorSmoothAt.pi (fun i =>
      (ScalarCalculus.vectorSmooth_mul (ScalarCalculus.rho_smooth g ci ⟨p,hpc⟩)
        (ScalarCalculus.component_smooth X ci ⟨p,hpc⟩ i)).postcomp
          ((contDiff_const (c := ε)).mul contDiff_id))
  have hef : (fun q i => ε * (rho g ci q * component ci X i q)) =ᶠ[nhds p] f := by
    obtain ⟨A, hA, hpA, hsign⟩ := (s.locallyConstant c hc).exists_open ⟨p,hp⟩
    have hAo : IsOpen (Subtype.val '' A) := c.open_source.isOpenMap_subtype_val A hA
    filter_upwards [hAo.mem_nhds (show p ∈ Subtype.val '' A from ⟨⟨p,hp⟩,hpA,rfl⟩)] with q hq
    obtain ⟨q, hqA, rfl⟩ := hq
    dsimp only [f]
    rw [dite_eq_left q.property, volume_topCoefficient_rho g o s hs K c hc q,
      coordinates_eq_components K c hc q X, hsign q hqA]
    funext i
    change ε * (rho g ci q.val * component ci X i q.val) =
      (ε * rho g ci q.val) * component ci X i q.val
    ring
  have hf := hf0.congr hef
  obtain ⟨U, hU, hpU, W, hW, heW⟩ := hf.2 c hc hp
  obtain ⟨V, hV, hpV, W', hW', heW'⟩ :=
    SmoothManifolds.CartanResults.chart_extension_of_eventual c p hp (⊤ : ℕ∞)
      f U hU hpU W hW heW
  have he0 : (fun q => W' (c q).val) =ᶠ[nhds p]
      (fun q i => ε * (rho g ci q * component ci X i q)) := by
    have hcp : ContinuousAt (fun q => (c q).val) p :=
      continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
    filter_upwards [c.open_source.mem_nhds hp,
      hcp.preimage_mem_nhds (hV.mem_nhds hpV), hef] with q hqs hqV hqf
    exact (heW' ⟨q,hqs⟩ hqV).trans hqf.symm
  have hflux : ∀ q : c.source, (c q.val).val ∈ V →
      SmoothManifolds.ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv (n+1) n
        (fun I => SmoothManifolds.ExteriorData.coefficients D n c hc ω q I) =
      SmoothManifolds.ClassicalData.fluxForm W' (c q.val).val := by
    intro q hq
    rw [contraction_coordinates_flux D X.val σ c hc q]
    unfold SmoothManifolds.ClassicalData.fluxForm
    rw [heW' q hq]
    dsimp only [f]
    rw [dite_eq_left q.property]
    exact ((SmoothManifolds.ClassicalData.volume (n+1)).curryLeft.map_smul
      (topCoefficient K c hc q.val q.property σ)
      (K.equiv c hc q.val q.property (X.val q.val))).symm
  have hdiv := divergence_weighted_ambient g C hC X ci p hp ε W' V hV hpV hW' he0
  have htop := volume_topCoefficient_rho g o s hs K c hc ⟨p,hp⟩
  symm
  apply coordinate_derivative_eq_smul_of_flux_extension D ω σ c hc ⟨p,hp⟩ V hV hpV W'
    (hW'.of_le (by simp)) hflux (divergence C X p)
  change (∑ i : Fin (n+1), fderiv ℝ W' (c p).val (Pi.single i 1) i) =
    divergence C X p * topCoefficient K c hc p hp σ
  rw [hdiv, htop]
  change ε * (rho g ci p * divergence C X p) = divergence C X p * (ε * rho g ci p)
  ring
end P202.Geometry.GreenDivergenceCore

namespace P202.Geometry.GreenDivergenceCore
universe u

/-- The full oriented Stokes realization for the actual metric volume and flux. -/
theorem oriented_stokes :
    P202Specs.Geometry.GreenDivergenceCore.oriented_stokesType.{u} :=
  oriented_stokes_from_derivative contraction_derivative

end P202.Geometry.GreenDivergenceCore

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Topology
namespace P202.Geometry.GreenDivergenceCore.ChartModel
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.FrameData
open SmoothManifolds.LocalIntegrationData Set Filter
universe u v
variable {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A scalar or vector function transported to the relative chart model and
zero-extended at artificial chart edges. -/
def chartFunction (c : ModelChart n a M) (f : M → V) : Euclidean n → V :=
  by
    classical
    exact fun z => if hm : z ∈ modelSet n a then
      if hz : (⟨z, hm⟩ : ModelSpace n a) ∈ c.target then f (c.symm ⟨z, hm⟩) else 0
      else 0

theorem chartFunction_at (c : ModelChart n a M) (f : M → V) (p : c.source) :
    chartFunction c f (c p.val).val = f p.val := by
  simp [chartFunction, (c p.val).property,
    c.map_source p.property, c.left_inv p.property]

theorem chartFunction_nonzero (c : ModelChart n a M) (f : M → V)
    (z : Euclidean n) (hz : chartFunction c f z ≠ 0) :
    ∃ p, f p ≠ 0 ∧ p ∈ c.source ∧ (c p).val = z := by
  classical
  unfold chartFunction at hz
  split_ifs at hz with hm ht
  · exact ⟨c.symm ⟨z, hm⟩, hz, c.map_target ht,
      congrArg Subtype.val (c.right_inv ht)⟩
  · exact (hz rfl).elim
  · exact (hz rfl).elim

theorem chartFunction_compact_container (c : ModelChart n a M) (f : M → V)
    (K : Set M) (hcompact : IsCompact K) (hs : K ⊆ c.source)
    (hzero : ∀ p ∈ c.source, p ∉ K → f p = 0) :
    IsCompact ((fun p : M => (c p).val) '' K) ∧
      Function.support (chartFunction c f) ⊆ (fun p : M => (c p).val) '' K := by
  refine ⟨hcompact.image_of_continuousOn
    (continuous_subtype_val.comp_continuousOn (c.continuousOn.mono hs)), ?_⟩
  intro z hz
  obtain ⟨p, hp, hpc, he⟩ := chartFunction_nonzero c f z hz
  have hpK : p ∈ K := by
    by_contra hn
    exact hp (hzero p hpc hn)
  exact ⟨p, hpK, he⟩

theorem chartFunction_regular (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (f : M → V)
    (hf : ∀ p ∈ c.source, VectorSmoothAt S.smoothStructure.val f p)
    (K : Set M) (hcompact : IsCompact K) (hs : K ⊆ c.source)
    (hzero : ∀ p ∈ c.source, p ∉ K → f p = 0) :
    LocallyContDiffOn 1 (modelSet n a) (fun z => chartFunction c f z.val) := by
  classical
  intro z
  by_cases hz : z ∈ c.target
  · let p := c.symm z
    have hp : p ∈ c.source := c.map_target hz
    obtain ⟨U, hU, hpU, F, hF, heF⟩ := (hf p hp).2 c hc hp
    obtain ⟨W, hWeq, hW, hpW⟩ := mem_nhds_iff.mp heF
    obtain ⟨O, hO, hOT⟩ := isOpen_induced_iff.mp c.open_target
    have hzO : z.val ∈ O := by
      change z ∈ Subtype.val ⁻¹' O
      rw [hOT]
      exact hz
    have hzU : z.val ∈ U := by simpa only [p, c.right_inv hz] using hpU
    have hWmodel : IsOpen (c.target ∩ c.symm ⁻¹' W) :=
      c.continuousOn_symm.isOpen_inter_preimage c.open_target hW
    obtain ⟨A, hA, hAeq⟩ := isOpen_induced_iff.mp hWmodel
    have hzA : z.val ∈ A := by
      change z ∈ Subtype.val ⁻¹' A
      rw [hAeq]
      exact ⟨hz, hpW⟩
    refine ⟨U ∩ O ∩ A, (hU.inter hO).inter hA, ⟨⟨hzU, hzO⟩, hzA⟩,
      F, (hF.of_le (by simp)).mono (inter_subset_left.trans inter_subset_left), ?_⟩
    intro y hy
    have hyt : y ∈ c.target := by
      rw [← hOT]
      exact hy.1.2
    have hyW : c.symm y ∈ W := by
      have hh : y ∈ Subtype.val ⁻¹' A := hy.2
      rw [hAeq] at hh
      exact hh.2
    simp only [chartFunction, y.property, hyt, ↓reduceDIte]
    have hh := hWeq hyW
    change F (c (c.symm y)).val = f (c.symm y) at hh
    simpa only [c.right_inv hyt] using hh
  · obtain ⟨hK, hsub⟩ := chartFunction_compact_container c f K hcompact hs hzero
    let J := (fun p : M => (c p).val) '' K
    have hzK : z.val ∉ J := by
      rintro ⟨p, hp, he⟩
      exact hz ((Subtype.ext he : c p = z) ▸ c.map_source (hs hp))
    refine ⟨Jᶜ, hK.isClosed.isOpen_compl, hzK, fun _ => 0, contDiffOn_const, ?_⟩
    intro y hy
    symm
    by_contra hn
    exact hy (hsub hn)

theorem chartFunction_compact_support (c : ModelChart n a M) (f : M → V)
    (K : Set M) (hcompact : IsCompact K) (hs : K ⊆ c.source)
    (hzero : ∀ p ∈ c.source, p ∉ K → f p = 0) :
    HasCompactSupport (fun z : ModelSpace n a => chartFunction c f z.val) := by
  obtain ⟨hK, hsub⟩ := chartFunction_compact_container c f K hcompact hs hzero
  have hemb := (SmoothManifolds.LocalIntegrationResults.modelSet_closed n a).isClosedEmbedding_subtypeVal
  apply (hemb.isCompact_preimage hK).of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro z hz
    exact hsub hz
  · exact hK.isClosed.preimage continuous_subtype_val

theorem chartFunction_germ (c : ModelChart n a M) (f : M → V)
    (p : M) (hp : p ∈ c.source) (F : Euclidean n → V)
    (he : (fun q => F (c q).val) =ᶠ[𝓝 p] f) :
    chartFunction c f =ᶠ[𝓝[modelSet n a] (c p).val] F := by
  classical
  obtain ⟨W, hWeq, hW, hpW⟩ := mem_nhds_iff.mp he
  have hWmodel : IsOpen (c.target ∩ c.symm ⁻¹' W) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target hW
  obtain ⟨A, hA, hAeq⟩ := isOpen_induced_iff.mp hWmodel
  have hpA : (c p).val ∈ A := by
    change c p ∈ Subtype.val ⁻¹' A
    rw [hAeq]
    refine ⟨c.map_source hp, ?_⟩
    simpa only [mem_preimage, c.left_inv hp] using hpW
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hA.mem_nhds hpA)] with y hyM hyA
  let z : ModelSpace n a := ⟨y, hyM⟩
  have hzA : z ∈ Subtype.val ⁻¹' A := hyA
  rw [hAeq] at hzA
  have hh := hWeq hzA.2
  change F (c (c.symm z)).val = f (c.symm z) at hh
  have hyt : (⟨y, hyM⟩ : ModelSpace n a) ∈ c.target := hzA.1
  simpa only [chartFunction, dite_eq_left hyM, dite_eq_left hyt, z,
    c.right_inv hyt] using hh.symm

theorem chartFunction_fderivWithin (c : ModelChart n a M) (f : M → V)
    (p : M) (hp : p ∈ c.source) (F : Euclidean n → V)
    (he : (fun q => F (c q).val) =ᶠ[𝓝 p] f)
    (hF : DifferentiableAt ℝ F (c p).val) :
    fderivWithin ℝ (chartFunction c f) (modelSet n a) (c p).val =
      fderiv ℝ F (c p).val := by
  rw [(chartFunction_germ c f p hp F he).fderivWithin_eq_of_mem (c p).property]
  exact hF.fderivWithin (SmoothManifolds.uniqueDiffOn_modelSet n a _ (c p).property)

theorem chartFunction_contDiff {S : SmoothManifold n .euclidean M}
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (f : M → V) (hf : ∀ p ∈ c.source, VectorSmoothAt S.smoothStructure.val f p)
    (K : Set M) (hcompact : IsCompact K) (hs : K ⊆ c.source)
    (hzero : ∀ p ∈ c.source, p ∉ K → f p = 0) :
    ContDiff ℝ 1 (chartFunction c f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  obtain ⟨U, hU, hzU, F, hF, heF⟩ :=
    chartFunction_regular c hc f hf K hcompact hs hzero ⟨z, mem_univ z⟩
  apply (hF.contDiffAt (hU.mem_nhds hzU)).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with y hy
  exact (heF ⟨y, mem_univ y⟩ hy).symm

open MeasureTheory SmoothManifolds.LocalStokesData in
theorem chartFunction_halfSpace_divergence {n : ℕ}
    {S : SmoothManifold (n+1) .halfSpace M}
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (f : Fin (n+1) → M → ℝ)
    (hf : ∀ i p, p ∈ c.source → VectorSmoothAt S.smoothStructure.val (f i) p)
    (K : Set M) (hcompact : IsCompact K) (hs : K ⊆ c.source)
    (hzero : ∀ i p, p ∈ c.source → p ∉ K → f i p = 0) :
    (∫ x in halfSpaceSet (n+1), ∑ i,
      fderivWithin ℝ (chartFunction c (f i)) (halfSpaceSet (n+1)) x (frame (n+1) i)) =
      - ∫ y, chartFunction c (f (Fin.last n)) ((Fin.last n).insertNth 0 y) := by
  let J := (fun p : M => (c p).val) '' K
  have hJ : IsCompact J :=
    (chartFunction_compact_container c (f 0) K hcompact hs (hzero 0)).1
  have hJM : J ⊆ halfSpaceSet (n+1) := by
    rintro z ⟨p, _, rfl⟩
    exact (c p).property
  apply (SmoothManifolds.LocalStokesResults.halfSpace_divergence
    (fun i => chartFunction c (f i)) (fun i =>
      SmoothManifolds.LocalStokesResults.localExtensions_contDiffOn
        (chartFunction_regular c hc (f i) (hf i) K hcompact hs (hzero i))) J hJ hJM ?_).2.2
  intro i x hx hxJ
  by_contra hn
  exact hxJ ((chartFunction_compact_container c (f i) K hcompact hs (hzero i)).2 hn)

open MeasureTheory SmoothManifolds.LocalStokesData in
theorem chartFunction_fullSpace_divergence {S : SmoothManifold n .euclidean M}
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (f : Fin n → M → ℝ)
    (hf : ∀ i p, p ∈ c.source → VectorSmoothAt S.smoothStructure.val (f i) p)
    (K : Set M) (hcompact : IsCompact K) (hs : K ⊆ c.source)
    (hzero : ∀ i p, p ∈ c.source → p ∉ K → f i p = 0) :
    (∫ x, ∑ i, fderiv ℝ (chartFunction c (f i)) x (frame n i)) = 0 := by
  classical
  have hInt (i : Fin n) :
      Integrable (fun x => fderiv ℝ (chartFunction c (f i)) x (frame n i)) ∧
      (∫ x, fderiv ℝ (chartFunction c (f i)) x (frame n i)) = 0 := by
    apply SmoothManifolds.LocalStokesResults.integral_directional_derivative _
      (chartFunction_contDiff c hc (f i) (hf i) K hcompact hs (hzero i))
    obtain ⟨hJ, hsub⟩ := chartFunction_compact_container c (f i) K hcompact hs (hzero i)
    apply hJ.of_isClosed_subset isClosed_closure
    exact closure_minimal hsub hJ.isClosed
  rw [integral_finsetSum _ (fun i _ => (hInt i).1)]
  simp only [(hInt _).2, Finset.sum_const_zero]

end P202.Geometry.GreenDivergenceCore.ChartModel

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace P202.Geometry.GreenDivergenceCore.LocalAnalytic
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData SmoothManifolds.BundleData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

open SmoothManifolds.TangentBundleData SmoothManifolds.MetricVolumeData
  SmoothManifolds.OrientationData SmoothManifolds.DensityIntegrationData
  SmoothManifolds.LocalIntegrationData SmoothManifolds.FrameData
open ChartModel

 theorem coordinateVector_eq (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : M) (hp : p ∈ c.val.source) (i : Fin n) :
    ((tangentStructure S).fiberCoordinates.equiv c.val c.property p hp).symm (Pi.single i 1) =
      P202.LeviCivitaData.coordinateVector c i p := by
  apply ((tangentStructure S).fiberCoordinates.equiv c.val c.property p hp).injective
  rw [LinearEquiv.apply_symm_apply, coordinateVector_coordinates]

 theorem densityCoefficient_rho (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (p : M) (hp : p ∈ c.val.source) :
    densityCoefficient (tangentStructure S).fiberCoordinates c.val c.property ⟨p,hp⟩
      (P202.VolumeData.density g p) = rho g c p := by
  rw [(RiemannianVolume.density_coordinates g (tangentStructure S).fiberCoordinates
    c.val c.property ⟨p,hp⟩).1]
  unfold rho
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  ext i j
  change pairing g p _ _ = pairing g p _ _
  simp only [Pi.basisFun_apply, coordinateVector_eq]

 theorem component_coordinates (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : M) (hp : p ∈ c.val.source) (X : Field S) (i : Fin n) :
    component c X i p =
      (tangentStructure S).fiberCoordinates.equiv c.val c.property p hp (X.val p) i := by
  exact congrFun ((tangentRealization S).coordinates c p hp (X.val p)) i

 theorem chartFunction_coordinateDerivative (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : M) (hp : p ∈ c.val.source) (i : Fin n) {f : M → ℝ}
    (hf : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val f p) :
    fderivWithin ℝ (chartFunction c.val f) (modelSet n a) (c.val p).val (Pi.single i 1) =
      P202.ScalarData.coordinateDerivative c i f p := by
  obtain ⟨U,hU,hpU,F,hF,he⟩ := hf.2 c.val c.property hp
  rw [chartFunction_fderivWithin c.val f p hp F he
    ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))]
  exact (coordinateDerivative_ambient c p hp i hf F U hU hpU hF he).symm

 theorem weightedComponent_smooth (g : RiemannianMetric S) (X : Field S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (i : Fin n)
    (p : M) (hp : p ∈ c.val.source) :
    VectorSmoothAt S.smoothStructure.val (fun q => rho g c q * component c X i q) p := by
  have hpc : p ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  exact ScalarCalculus.vectorSmooth_mul (ScalarCalculus.rho_smooth g c ⟨p,hpc⟩)
    (ScalarCalculus.component_smooth X c ⟨p,hpc⟩ i)

 theorem weightedComponent_zero (g : RiemannianMetric S) (X : Field S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (i : Fin n)
    (p : M) (hp : p ∈ c.val.source) (hpx : p ∉ SmoothManifolds.sectionSupport X.val) :
    rho g c p * component c X i p = 0 := by
  have hX : X.val p = 0 := by
    by_contra hn
    exact hpx (subset_closure hn)
  rw [component_coordinates c p hp X i, hX, map_zero, Pi.zero_apply, mul_zero]

 theorem divergence_coordinateDensity_on_model (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C) (X : Field S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (hX : IsCompact (SmoothManifolds.sectionSupport X.val))
    (hs : SmoothManifolds.sectionSupport X.val ⊆ c.val.source) (z : ModelSpace n a) :
    coordinateDensity (tangentStructure S).fiberCoordinates c.val c.property
      (fun p => divergence C X p • P202.VolumeData.density g p) z.val =
    ∑ i : Fin n, fderivWithin ℝ
      (chartFunction c.val (fun p => rho g c p * component c X i p))
      (modelSet n a) z.val (Pi.single i 1) := by
  classical
  by_cases hz : z ∈ c.val.target
  · let p := c.val.symm z
    have hp : p ∈ c.val.source := c.val.map_target hz
    have hpc : p ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
    have hcoord : (c.val p).val = z.val := congrArg Subtype.val (c.val.right_inv hz)
    rw [← hcoord]
    rw [SmoothManifolds.DensityChartResults.density_at (tangentStructure S).fiberCoordinates
      c.val c.property (fun p => divergence C X p • P202.VolumeData.density g p) ⟨p,hp⟩]
    rw [map_smul, smul_eq_mul, densityCoefficient_rho]
    simp_rw [chartFunction_coordinateDerivative c p hp _ (weightedComponent_smooth g X c _ p hp)]
    rw [ScalarCalculus.divergence_coordinates g C hC X c ⟨p,hpc⟩]
    rw [mul_right_comm, inv_mul_cancel₀ (ne_of_gt (ScalarCalculus.rho_positive g c ⟨p,hpc⟩)), one_mul]
  · have hzero (i : Fin n) : fderivWithin ℝ
        (chartFunction c.val (fun p => rho g c p * component c X i p))
        (modelSet n a) z.val = 0 := by
      obtain ⟨hK,hsub⟩ := chartFunction_compact_container c.val
        (fun p => rho g c p * component c X i p) (SmoothManifolds.sectionSupport X.val)
        hX hs (weightedComponent_zero g X c i)
      have hzK : z.val ∉ ((fun p : M => (c.val p).val) '' SmoothManifolds.sectionSupport X.val) := by
        rintro ⟨p,hp,he⟩
        exact hz ((Subtype.ext he : c.val p = z) ▸ c.val.map_source (hs hp))
      exact SmoothManifolds.LocalStokesResults.fderivWithin_zero_off_compact hK
        _ (fun y hy hyK => by
          by_contra hn
          exact hyK (hsub hn)) z.property hzK
    simp_rw [hzero]
    simp only [ContinuousLinearMap.zero_apply, Finset.sum_const_zero]
    unfold coordinateDensity SmoothManifolds.LocalIntegrationData.extendModel
    simp only [dite_eq_left z.property, dite_eq_right hz]

end P202.Geometry.GreenDivergenceCore.LocalAnalytic

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open scoped Classical Topology CompactlySupported
namespace P202.Geometry.GreenDivergenceCore.LocalAnalytic
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData SmoothManifolds.BundleData
  SmoothManifolds.BoundaryData SmoothManifolds.BoundaryRegularLevelData
  SmoothManifolds.MetricVolumeData SmoothManifolds.DensityIntegrationData SmoothManifolds.LocalIntegrationData
  SmoothManifolds.LocalStokesData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData P202.GreenData
open ChartModel MeasureTheory Set
universe u

def localFluxType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .halfSpace M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (K : FiberCoordinates S) (H : FiberCoordinates b.manifold)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart n .euclidean (intrinsicBoundary S))
    (hd : d ∈ b.manifold.smoothStructure.val)
    (hface : IsFaceRestriction S c d) (X : P202.ConnectionData.Field S)
    (F : M → Euclidean (n+1))
    (hF : ∀ (p : M) (hp : p ∈ c.source), F p =
      densityCoefficient K c hc ⟨p, hp⟩ (P202.VolumeData.density g p) •
        K.equiv c hc p hp (X.val p)),
    SmoothManifolds.DensityIntegrationData.coordinateDensity H d hd
      (fun p => flux g b X p • P202.VolumeData.density b.metric p) =
    fun y => -(SmoothManifolds.LocalIntegrationData.extendModel
      (fun z : ModelSpace (n+1) .halfSpace =>
        if hz : z ∈ c.target then F (c.symm z) (Fin.last n) else 0)
      (Fin.snoc y 0))

 theorem chart_supported_divergence_from_flux
    (flux_coordinateDensity : localFluxType.{u}) :
    P202Specs.Geometry.GreenDivergenceCore.chart_supported_divergenceType.{u} := by
  intro n a M _ S g C hC b X hX c hc hs
  cases n with
  | zero => exact divergence_identity_zero_dimension g C b X hX
  | succ n =>
    let ci : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c,hc⟩
    let K := (tangentStructure S).fiberCoordinates
    let H := (tangentStructure b.manifold).fiberCoordinates
    let F := compactDivergence C X hX
    let Q := compactFlux g b X hX
    let f (i : Fin (n+1)) (p : M) := rho g ci p * component ci X i p
    have hf (i : Fin (n+1)) (p : M) (hp : p ∈ c.source) :
        SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val (f i) p :=
      weightedComponent_smooth g X ci i p hp
    have hfzero (i : Fin (n+1)) (p : M) (hp : p ∈ c.source)
        (hpx : p ∉ SmoothManifolds.sectionSupport X.val) : f i p = 0 :=
      weightedComponent_zero g X ci i p hp hpx
    have hFs : tsupport F ⊆ c.source := (divergence_support C X).trans hs
    have hFI : P202.VolumeData.integral g F =
        ∫ x, coordinateDensity K c hc
          (fun p => divergence C X p • P202.VolumeData.density g p) x := by
      exact RiemannianVolume.integral_chart g F K c hc hFs
    have hbulk (z : ModelSpace (n+1) a) :
        coordinateDensity K c hc (fun p => divergence C X p • P202.VolumeData.density g p) z.val =
        ∑ i, fderivWithin ℝ (chartFunction c (f i)) (modelSet (n+1) a) z.val (frame (n+1) i) :=
      divergence_coordinateDensity_on_model g C hC X ci hX hs z
    refine ⟨F,Q,fun _ => rfl,fun _ => rfl,?_⟩
    cases a with
    | euclidean =>
      have hQzero : Q = 0 := by
        ext p
        have hp := p.property
        change p.val ∈ SmoothManifolds.intrinsicBoundary S at hp
        rw [SmoothManifolds.intrinsicBoundary_euclidean S] at hp
        exact hp.elim
      rw [hQzero, metric_integral_zero, hFI]
      have he : (fun x => coordinateDensity K c hc
          (fun p => divergence C X p • P202.VolumeData.density g p) x) =
          (fun x => ∑ i, fderiv ℝ (chartFunction c (f i)) x (frame (n+1) i)) := by
        funext x
        simpa only [modelSet, fderivWithin_univ] using hbulk ⟨x,mem_univ x⟩
      rw [he]
      exact chartFunction_fullSpace_divergence c hc f hf
        (SmoothManifolds.sectionSupport X.val) hX hs hfzero
    | halfSpace =>
      have hFI' : P202.VolumeData.integral g F =
          ∫ x in halfSpaceSet (n+1), ∑ i,
            fderivWithin ℝ (chartFunction c (f i)) (halfSpaceSet (n+1)) x (frame (n+1) i) := by
        rw [hFI]
        have he : (∫ x in halfSpaceSet (n+1), coordinateDensity K c hc
            (fun p => divergence C X p • P202.VolumeData.density g p) x) =
            ∫ x, coordinateDensity K c hc
              (fun p => divergence C X p • P202.VolumeData.density g p) x := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          unfold coordinateDensity SmoothManifolds.LocalIntegrationData.extendModel
          exact dite_eq_right hx
        rw [← he]
        apply setIntegral_congr_fun
          (SmoothManifolds.LocalIntegrationResults.modelSet_closed (n+1) .halfSpace).measurableSet
        intro x hx
        exact hbulk ⟨x,hx⟩
      rw [hFI', chartFunction_halfSpace_divergence c hc f hf
        (SmoothManifolds.sectionSupport X.val) hX hs hfzero]
      by_cases hne : Nonempty {p : SmoothManifolds.intrinsicBoundary S // p.val ∈ c.source}
      · obtain ⟨d,hd,hface⟩ := b.natural.2 c hc hne
        have hQs : tsupport Q ⊆ d.source := by
          rw [hface.1]
          exact (flux_support g b X).trans (preimage_mono hs)
        have hQI := RiemannianVolume.integral_chart b.metric Q H d hd hQs
        change P202.VolumeData.integral b.metric Q = _ at hQI
        rw [hQI]
        have hcoord := flux_coordinateDensity g b K H c hc d hd hface X
          (fun p i => f i p) (fun p hp => ?_)
        · have he : coordinateDensity H d hd
              (fun p => flux g b X p • P202.VolumeData.density b.metric p) =
              (fun y => -chartFunction c (f (Fin.last n)) ((Fin.last n).insertNth 0 y)) := by
            rw [hcoord]
            funext y
            rw [Fin.insertNth_last']
            rfl
          change -(∫ y, chartFunction c (f (Fin.last n)) ((Fin.last n).insertNth 0 y)) =
            ∫ y, coordinateDensity H d hd
              (fun p => flux g b X p • P202.VolumeData.density b.metric p) y
          rw [he, integral_neg]
          rfl
        · ext i
          rw [Pi.smul_apply, smul_eq_mul, densityCoefficient_rho g ci p hp,
            ← component_coordinates ci p hp X i]
      · have hQzero : Q = 0 := by
          ext p
          have hpout : p.val ∉ c.source := fun hp => hne ⟨⟨p,hp⟩⟩
          have hXp : X.val p.val = 0 := by
            by_contra hn
            exact hpout (hs (subset_closure hn))
          change pairing g p.val (X.val p.val) (b.normal p) = 0
          rw [hXp, map_zero, LinearMap.zero_apply]
        rw [hQzero, metric_integral_zero]
        have htracezero : (fun y => chartFunction c (f (Fin.last n))
            ((Fin.last n).insertNth 0 y)) = 0 := by
          funext y
          let z : ModelSpace (n+1) .halfSpace :=
            SmoothManifolds.faceEmbedding .halfSpace (⟨y,mem_univ y⟩ : ModelSpace n .euclidean)
          have hzout : z ∉ c.target := by
            intro hz
            have hp : c.symm z ∈ SmoothManifolds.intrinsicBoundary S := by
              apply (SmoothManifolds.intrinsicBoundary_iff_chart S c hc _ (c.map_target hz)).mpr
              rw [c.right_inv hz]
              change Fin.snoc (α := fun _ : Fin (n+1) => ℝ) y 0 (Fin.last n) = 0
              exact Fin.snoc_last _ _
            exact hne ⟨⟨⟨c.symm z,hp⟩,c.map_target hz⟩⟩
          change chartFunction c (f (Fin.last n)) ((Fin.last n).insertNth 0 y) = 0
          rw [Fin.insertNth_last']
          change chartFunction c (f (Fin.last n)) z.val = 0
          simp only [chartFunction, dite_eq_left z.property, dite_eq_right hzout]
        rw [htracezero]
        change -(MeasureTheory.integral MeasureTheory.volume (0 : Euclidean n → ℝ)) = 0
        simp
end P202.Geometry.GreenDivergenceCore.LocalAnalytic

namespace P202.Geometry.GreenDivergenceCore.LocalDensity
open SmoothManifolds hiding SmoothManifold ModelChart TangentSpace Euclidean modelSet ModelSpace sectionSupport intrinsicBoundary IsFaceRestriction
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.OrientationData
  SmoothManifolds.BoundaryData SmoothManifolds.BoundaryRegularLevelData
  SmoothManifolds.BoundaryOrientationData SmoothManifolds.MetricVolumeData
  P202.MetricData P202.GreenData
universe u

theorem normalWedge_of_decomposition {V : Type u} {W : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {n : ℕ} (hdim : Module.finrank ℝ W = n)
    (L : W →ₗ[ℝ] V) (x v : V) (t : ℝ) (z : W) (η : ⋀[ℝ]^n W)
    (hx : x = t • v + L z) : normalWedge L x η = t • normalWedge L v η := by
  rw [hx, BoundaryOrientations.normalWedge_add, BoundaryOrientations.normalWedge_smul,
    BoundaryOrientations.normalWedge_tangent hdim, add_zero]

/-- The first coordinate vector in the normal slot need not be metric orthogonal.
Its tangential error disappears in the normal wedge. -/
theorem normalWedge_coordinates {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .halfSpace M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (K : FiberCoordinates S) (H : FiberCoordinates b.manifold)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart n .euclidean (intrinsicBoundary S))
    (hd : d ∈ b.manifold.smoothStructure.val)
    (hface : IsFaceRestriction S c d) (p : intrinsicBoundary S)
    (hp : p ∈ d.source) (hpc : p.val ∈ c.source)
    (x : TangentSpace S p.val) :
    normalWedge (differential b.manifold S Subtype.val b.natural.1 p) x
      (coordinateVector H d hd ⟨p, hp⟩) =
      (-(K.equiv c hc p.val hpc x) (Fin.last n)) •
        ((-1 : ℝ)^(n+1) • coordinateVector K c hc ⟨p.val, hpc⟩) := by
  letI := (tangent_dimension b.manifold p).1
  let E := K.equiv c hc p.val hpc
  let L := differential b.manifold S Subtype.val b.natural.1 p
  have hL := differential_spec b.manifold S Subtype.val b.natural.1 p
  let v := (-1 : ℝ) • E.symm ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n))
  let t := -(E x) (Fin.last n)
  have hz : E (x + (-t) • v) (Fin.last n) = 0 := by
    rw [E.map_add, E.map_smul]
    simp [v, t, E.map_smul, Pi.basisFun_apply]
  have hi := @SmoothManifolds.boundary_inclusion_image.{u} n M _ S b.manifold b.natural
    p c hc hpc L hL E (K.isCoordinates c hc p.val hpc)
  have hmem : x + (-t) • v ∈ LinearMap.range L := (hi.2 (x + (-t) • v)).mpr hz
  rcases hmem with ⟨z, hz⟩
  have hx : x = t • v + L z := by
    rw [hz, add_left_comm, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  let ζ : DeterminantLine b.manifold p := coordinateVector H d hd ⟨p, hp⟩
  have heq := @normalWedge_of_decomposition.{u} (TangentSpace S p.val)
    (TangentSpace b.manifold p) _ _ _ _ (tangent_dimension b.manifold p).1 n
    (tangent_dimension b.manifold p).2 L x v t z ζ hx
  have hnorm := BoundaryOrientations.normalWedge_coordinateVector S b.manifold K H c hc d hd
    hface p hp hpc L hL
  have hv : v = -(K.equiv c hc p.val hpc).symm ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n)) := by
    dsimp only [v, E]
    exact neg_one_smul ℝ ((K.equiv c hc p.val hpc).symm
      ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n)))
  rw [hv, hnorm] at heq
  exact heq


/-- A pointwise density statement with no global orientation assumption. -/
theorem boundary_density_coordinates {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .halfSpace M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (K : FiberCoordinates S) (H : FiberCoordinates b.manifold)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart n .euclidean (intrinsicBoundary S))
    (hd : d ∈ b.manifold.smoothStructure.val)
    (hface : IsFaceRestriction S c d) (p : intrinsicBoundary S)
    (hp : p ∈ d.source) (hpc : p.val ∈ c.source) :
    densityCoefficient H d hd ⟨p, hp⟩ (P202.VolumeData.density b.metric p) =
      (-(K.equiv c hc p.val hpc (b.normal p)) (Fin.last n)) *
        densityCoefficient K c hc ⟨p.val, hpc⟩ (P202.VolumeData.density g p.val) := by
  have hneg : K.equiv c hc p.val hpc (b.normal p) (Fin.last n) < 0 :=
    (BoundaryOrientations.outward_iff_coordinate S p c hc hpc _
      (K.isCoordinates c hc p.val hpc) _).mp (b.outward p)
  have he := GreenBoundaryFlux.normalWedge_norm g b p (coordinateVector H d hd ⟨p, hp⟩)
  rw [normalWedge_coordinates g b K H c hc d hd hface p hp hpc,
    MetricVolumeResults.determinantNorm_smul,
    MetricVolumeResults.determinantNorm_smul,
    abs_neg, abs_of_neg hneg, abs_pow, abs_neg, abs_one, one_pow, one_mul] at he
  exact he.symm

private theorem flux_density_algebra (a ν x ρ σ : ℝ)
    (hσ : σ = (-ν) * ρ) (hx : x = a * ν) : a * σ = -(ρ * x) := by
  rw [hσ, hx]
  ring

/-- The true outward flux, multiplied by induced boundary density, is the
negative last component of the density-weighted vector field. -/
theorem flux_density_coordinates {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .halfSpace M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (K : FiberCoordinates S) (H : FiberCoordinates b.manifold)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart n .euclidean (intrinsicBoundary S))
    (hd : d ∈ b.manifold.smoothStructure.val)
    (hface : IsFaceRestriction S c d) (p : intrinsicBoundary S)
    (hp : p ∈ d.source) (hpc : p.val ∈ c.source) (X : P202.ConnectionData.Field S) :
    flux g b X p * densityCoefficient H d hd ⟨p, hp⟩ (P202.VolumeData.density b.metric p) =
      -(densityCoefficient K c hc ⟨p.val, hpc⟩ (P202.VolumeData.density g p.val) *
        K.equiv c hc p.val hpc (X.val p.val) (Fin.last n)) := by
  let E := K.equiv c hc p.val hpc
  let L := differential b.manifold S Subtype.val b.natural.1 p
  have hL := differential_spec b.manifold S Subtype.val b.natural.1 p
  have hdec : ∃ z : TangentSpace b.manifold p,
      X.val p.val = flux g b X p • b.normal p + L z :=
    @GreenBoundaryFlux.boundary_normal_decomposition.{u}
      n .halfSpace M _ S g b p (X.val p.val)
  rcases hdec with ⟨z, hz⟩
  have ht : E (L z) (Fin.last n) = 0 := by
    have hi := @SmoothManifolds.boundary_inclusion_image.{u} n M _ S b.manifold b.natural
      p c hc hpc L hL E (K.isCoordinates c hc p.val hpc)
    have hmem : L z ∈ LinearMap.range L := ⟨z, rfl⟩
    exact (hi.2 (L z)).mp hmem
  have hx : E (X.val p.val) (Fin.last n) =
      flux g b X p * E (b.normal p) (Fin.last n) := by
    rw [hz, E.map_add, E.map_smul]
    change _ + E (L z) (Fin.last n) = _
    rw [ht, add_zero]
    rfl
  have hρ := boundary_density_coordinates g b K H c hc d hd hface p hp hpc
  exact flux_density_algebra (flux g b X p) (E (b.normal p) (Fin.last n))
    (E (X.val p.val) (Fin.last n))
    (densityCoefficient K c hc ⟨p.val, hpc⟩ (P202.VolumeData.density g p.val))
    (densityCoefficient H d hd ⟨p, hp⟩ (P202.VolumeData.density b.metric p)) hρ hx


/-- Equality of the actual unsigned boundary density integrand and the
negative last trace of the weighted bulk coordinate vector, including chart
zero extensions. -/
theorem flux_coordinateDensity {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .halfSpace M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (K : FiberCoordinates S) (H : FiberCoordinates b.manifold)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart n .euclidean (intrinsicBoundary S))
    (hd : d ∈ b.manifold.smoothStructure.val)
    (hface : IsFaceRestriction S c d) (X : P202.ConnectionData.Field S)
    (F : M → Euclidean (n+1))
    (hF : ∀ (p : M) (hp : p ∈ c.source), F p =
      densityCoefficient K c hc ⟨p, hp⟩ (P202.VolumeData.density g p) •
        K.equiv c hc p hp (X.val p)) :
    SmoothManifolds.DensityIntegrationData.coordinateDensity H d hd
      (fun p => flux g b X p • P202.VolumeData.density b.metric p) =
    fun y => -(SmoothManifolds.LocalIntegrationData.extendModel
      (fun z : ModelSpace (n+1) .halfSpace =>
        if hz : z ∈ c.target then F (c.symm z) (Fin.last n) else 0)
      (Fin.snoc y 0)) := by
  funext y
  let y' : ModelSpace n .euclidean := ⟨y, Set.mem_univ y⟩
  let z : ModelSpace (n+1) .halfSpace := SmoothManifolds.BoundaryData.faceEmbedding .halfSpace y'
  have hzval : z.val = Fin.snoc y 0 := rfl
  by_cases hy : y' ∈ d.target
  · let p : intrinsicBoundary S := d.symm y'
    have hp : p ∈ d.source := d.map_target hy
    have hpc : p.val ∈ c.source := by rwa [hface.1] at hp
    have hcz : c p.val = z := by
      apply Subtype.ext
      rw [hzval]
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hh := (intrinsicBoundary_iff_chart S c hc p.val hpc).mp p.property
        change (c p.val).val (Fin.last n) = 0 at hh
        simpa only [Fin.snoc_last] using hh
      · rw [Fin.snoc_castSucc, ← hface.2.2 p hp j]
        exact congrArg (fun v : ModelSpace n .euclidean => v.val j) (d.right_inv hy)
    have hzt : z ∈ c.target := hcz ▸ c.map_source hpc
    have he : c.symm z = p.val := by rw [← hcz, c.left_inv hpc]
    have hdpy : (d p).val = y := congrArg Subtype.val (d.right_inv hy)
    have hleft : SmoothManifolds.DensityIntegrationData.coordinateDensity H d hd
        (fun q => flux g b X q • P202.VolumeData.density b.metric q) y =
        densityCoefficient H d hd ⟨p,hp⟩ (flux g b X p • P202.VolumeData.density b.metric p) := by
      calc
        _ = SmoothManifolds.DensityIntegrationData.coordinateDensity H d hd
            (fun q => flux g b X q • P202.VolumeData.density b.metric q) (d p).val :=
          congrArg (fun w => SmoothManifolds.DensityIntegrationData.coordinateDensity H d hd
            (fun q => flux g b X q • P202.VolumeData.density b.metric q) w) hdpy.symm
        _ = _ := SmoothManifolds.DensityChartResults.density_at H d hd
          (fun q => flux g b X q • P202.VolumeData.density b.metric q) ⟨p,hp⟩
    have hright : SmoothManifolds.LocalIntegrationData.extendModel
        (fun w : ModelSpace (n+1) .halfSpace =>
          if hw : w ∈ c.target then F (c.symm w) (Fin.last n) else 0)
        (Fin.snoc y 0) = F p.val (Fin.last n) := by
      change SmoothManifolds.LocalIntegrationData.extendModel _ z.val = _
      unfold SmoothManifolds.LocalIntegrationData.extendModel
      rw [dite_eq_left z.property]
      change (if hz : z ∈ c.target then F (c.symm z) (Fin.last n) else 0) = _
      rw [dite_eq_left hzt, he]
    calc
      _ = densityCoefficient H d hd ⟨p,hp⟩
          (flux g b X p • P202.VolumeData.density b.metric p) := hleft
      _ = flux g b X p * densityCoefficient H d hd ⟨p,hp⟩
          (P202.VolumeData.density b.metric p) := map_smul _ _ _
      _ = -(densityCoefficient K c hc ⟨p.val,hpc⟩ (P202.VolumeData.density g p.val) *
          K.equiv c hc p.val hpc (X.val p.val) (Fin.last n)) :=
        flux_density_coordinates g b K H c hc d hd hface p hp hpc X
      _ = -F p.val (Fin.last n) :=
        congrArg Neg.neg (congrFun (hF p.val hpc) (Fin.last n)).symm
      _ = _ := congrArg Neg.neg hright.symm
  · have hz : z ∉ c.target := by
      intro hz
      apply hy
      rw [hface.2.1]
      exact hz
    have hleft : SmoothManifolds.DensityIntegrationData.coordinateDensity H d hd
        (fun q => flux g b X q • P202.VolumeData.density b.metric q) y = 0 := by
      apply (SmoothManifolds.DensityChartResults.density_on_model H d hd
        (fun q => flux g b X q • P202.VolumeData.density b.metric q) y').trans
      change (if hy : y' ∈ d.target then _ else 0) = 0
      exact dite_eq_right hy
    have hright : SmoothManifolds.LocalIntegrationData.extendModel
        (fun w : ModelSpace (n+1) .halfSpace =>
          if hw : w ∈ c.target then F (c.symm w) (Fin.last n) else 0)
        (Fin.snoc y 0) = 0 := by
      change SmoothManifolds.LocalIntegrationData.extendModel _ z.val = _
      unfold SmoothManifolds.LocalIntegrationData.extendModel
      rw [dite_eq_left z.property]
      change (if hz : z ∈ c.target then F (c.symm z) (Fin.last n) else 0) = _
      rw [dite_eq_right hz]
    calc
      _ = 0 := hleft
      _ = -(0 : ℝ) := neg_zero.symm
      _ = _ := congrArg Neg.neg hright.symm

end P202.Geometry.GreenDivergenceCore.LocalDensity


namespace P202.Geometry.GreenDivergenceCore
universe u

/-- The chart-supported density divergence theorem, including true faces. -/
theorem chart_supported_divergence :
    P202Specs.Geometry.GreenDivergenceCore.chart_supported_divergenceType.{u} :=
  LocalAnalytic.chart_supported_divergence_from_flux LocalDensity.flux_coordinateDensity

/-- Compact-support divergence for the actual Riemannian density on every
manifold model, with no global orientability assumption. -/
theorem divergence_theorem :
    P202Specs.Geometry.GreenDivergenceCore.divergence_theoremType.{u} :=
  divergence_from_chart_supported chart_supported_divergence

end P202.Geometry.GreenDivergenceCore
