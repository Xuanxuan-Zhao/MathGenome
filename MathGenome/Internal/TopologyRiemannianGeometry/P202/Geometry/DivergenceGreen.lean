import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.DivergenceGreen
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ScalarCalculus
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RiemannianVolume
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GreenDivergenceCore

/-! Theorem 6.7: scalar calculus, density divergence and Green identities.
The density divergence theorem and the outward-first Stokes representation are
proved upstream; the product rule below gives the first and second Green
identities, including the compact-support boundaryless case. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology CompactlySupported

namespace P202.Geometry.DivergenceGreen
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.BoundaryData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData P202.GreenData
universe u

theorem scalar_calculus : P202Specs.Geometry.DivergenceGreen.scalar_calculusType.{u} :=
  ⟨ScalarCalculus.gradient_characterization, ScalarCalculus.hessian_covariant,
    ScalarCalculus.hessian_formula, ScalarCalculus.hessian_symmetry,
    ScalarCalculus.laplacian_trace, ScalarCalculus.gradient_coordinates,
    ScalarCalculus.divergence_coordinates, ScalarCalculus.laplacian_coordinates,
    ScalarCalculus.connection_independence⟩

section Calculus
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem divergence_product_apply (C : Connection (tangentBundle S))
    (f : GlobalSmooth S) (X : Field S) (p : M) :
    divergence C (mulSection f X) p =
      scalarDerivative S f.val p (X.val p) + f.val p * divergence C X p := by
  have he : pointDerivative C (mulSection f X).val p =
      (scalarDerivative S f.val p).smulRight (X.val p) +
        f.val p • pointDerivative C X.val p := by
    apply LinearMap.ext
    intro v
    exact ConnectionForms.pointDerivative_leibniz (tangentBundle S) C X f p v
  obtain ⟨c, hc⟩ := (tangentBundle S).covers p
  let e := (tangentBundle S).fiberCoordinates c p hc
  letI : FiniteDimensional ℝ (TangentSpace S p) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  letI : Module.Free ℝ (TangentSpace S p) :=
    Module.Free.of_basis ((Pi.basisFun ℝ (Fin n)).map e.symm)
  unfold divergence
  rw [he, map_add, map_smul, smul_eq_mul]
  congr 1
  exact LinearMap.trace_smulRight (scalarDerivative S f.val p) (X.val p)

theorem first_integrand_divergence_apply (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (u v : GlobalSmooth S) (p : M) :
    divergence C (mulSection v (gradient g u)) p = firstIntegrand g C u v p := by
  rw [divergence_product_apply, ← ScalarCalculus.gradient_pairing g v]
  rw [show pairing g p ((gradient g v).val p) ((gradient g u).val p) =
    pairing g p ((gradient g u).val p) ((gradient g v).val p) from g.symmetric p _ _]
  rfl

theorem flux_product (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (f : GlobalSmooth S) (X : Field S) (p : intrinsicBoundary S) :
    flux g b (mulSection f X) p = f.val p.val * flux g b X p := by
  simp only [flux, mulSection, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem first_integrand_sub_swap (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (u v : GlobalSmooth S) (p : M) :
    firstIntegrand g C u v p - firstIntegrand g C v u p =
      secondIntegrand g C u v p := by
  unfold firstIntegrand secondIntegrand
  have hpair : pairing g p ((gradient g v).val p) ((gradient g u).val p) =
      pairing g p ((gradient g u).val p) ((gradient g v).val p) := g.symmetric p _ _
  rw [hpair]
  ring

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

/-- Pointwise metric construction, valid on the actual tangent fiber. The
covector will be the last boundary-chart coordinate differential. -/
theorem unit_normal_of_covector (g : RiemannianMetric S) (p : M)
    (φ : Module.Dual ℝ (TangentSpace S p)) (hφ : φ ≠ 0) :
    ∃ ν : TangentSpace S p,
      pairing g p ν ν = 1 ∧ φ ν < 0 ∧
        ∀ z, φ z = 0 → pairing g p ν z = 0 := by
  let w := (musical g p).symm φ
  have hw : w ≠ 0 := by
    intro hw
    apply hφ
    have he := (musical g p).apply_symm_apply φ
    change musical g p w = φ at he
    rw [hw, map_zero] at he
    exact he.symm
  have hg : 0 < pairing g p w w := g.positive p w hw
  let r := tangentNorm g p w
  have hr : 0 < r := Real.sqrt_pos.mpr hg
  have hr2 : r ^ 2 = pairing g p w w := SmoothMetrics.tangentNorm_sq g p w
  have hφw : φ w = pairing g p w w := by
    change φ w = musical g p w w
    rw [show musical g p w = φ from (musical g p).apply_symm_apply φ]
  refine ⟨(-r⁻¹) • w, ?_, ?_, ?_⟩
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← hr2]
    field_simp
  · rw [map_smul, smul_eq_mul, hφw]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr hr)) hg
  · intro z hz
    have hwz : pairing g p w z = φ z := by
      change musical g p w z = φ z
      rw [(musical g p).apply_symm_apply φ]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hwz, hz, mul_zero]

/-- The outward sign distinguishes the two unit normals to a hyperplane. -/
theorem unit_normal_unique (g : RiemannianMetric S) (p : M)
    (φ : Module.Dual ℝ (TangentSpace S p)) (ν μ : TangentSpace S p)
    (hνunit : pairing g p ν ν = 1) (hμunit : pairing g p μ μ = 1)
    (hνnegative : φ ν < 0) (hμnegative : φ μ < 0)
    (hνorth : ∀ z, φ z = 0 → pairing g p ν z = 0)
    (hμorth : ∀ z, φ z = 0 → pairing g p μ z = 0) : ν = μ := by
  let t := φ μ / φ ν
  have hνne : φ ν ≠ 0 := ne_of_lt hνnegative
  have ht : 0 < t := div_pos_of_neg_of_neg hμnegative hνnegative
  let z := μ - t • ν
  have hzφ : φ z = 0 := by
    calc
      φ z = φ μ - φ (t • ν) := φ.map_sub μ (t • ν)
      _ = φ μ - t * φ ν := by rw [φ.map_smul]; rfl
      _ = 0 := by dsimp only [t]; field_simp; ring
  have hνz := hνorth z hzφ
  have hμz := hμorth z hzφ
  have hzz : pairing g p z z = 0 := by
    change pairing g p (μ - t • ν) z = 0
    have hsub := congrArg (fun ψ : Module.Dual ℝ (TangentSpace S p) => ψ z)
      ((pairing g p).map_sub μ (t • ν))
    calc
      pairing g p (μ - t • ν) z = pairing g p μ z - pairing g p (t • ν) z := hsub
      _ = 0 := by
        rw [show pairing g p (t • ν) z = t * pairing g p ν z from
          congrArg (fun ψ : Module.Dual ℝ (TangentSpace S p) => ψ z)
            ((pairing g p).map_smul t ν), hμz, hνz, mul_zero, sub_self]
  have hz : z = 0 := by
    by_contra hne
    have hh : 0 < pairing g p z z := g.positive p z hne
    exact (ne_of_gt hh) hzz
  have hμ : μ = t • ν := sub_eq_zero.mp hz
  have hunit := hμunit
  rw [hμ] at hunit
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hνunit, mul_one] at hunit
  have htone : t = 1 := by nlinarith
  rw [htone, one_smul] at hμ
  exact hμ.symm

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

theorem divergence_product : P202Specs.Geometry.DivergenceGreen.divergence_productType.{u} :=
  divergence_product_apply

theorem first_integrand_divergence :
    P202Specs.Geometry.DivergenceGreen.first_integrand_divergenceType.{u} :=
  first_integrand_divergence_apply

section IntegralReductions
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem metric_integral_zero (g : RiemannianMetric S) :
    P202.VolumeData.integral g (0 : C_c(M, ℝ)) = 0 := by
  simpa using RiemannianVolume.integral_smul g 0 (0 : C_c(M, ℝ))

theorem metric_integral_sub (g : RiemannianMetric S) (f h : C_c(M, ℝ)) :
    P202.VolumeData.integral g (f - h) =
      P202.VolumeData.integral g f - P202.VolumeData.integral g h := by
  change RiemannianVolume.integral g (f - h) =
    RiemannianVolume.integral g f - RiemannianVolume.integral g h
  have hs : (-1 : ℝ) • h = -h := by
    ext p
    change (-1 : ℝ) * h p = -h p
    ring
  have hn : RiemannianVolume.integral g (-h) = -RiemannianVolume.integral g h := by
    simpa only [hs, neg_one_mul] using RiemannianVolume.integral_smul g (-1) h
  rw [sub_eq_add_neg, RiemannianVolume.integral_add, hn, sub_eq_add_neg]

theorem integral_identity_sub {m : ℕ} {k : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m k N} (g : RiemannianMetric S) (h : RiemannianMetric T)
    {f f' : M → ℝ} {q q' : N → ℝ}
    (hf : IntegralIdentity g h f q) (hf' : IntegralIdentity g h f' q') :
    IntegralIdentity g h (fun p => f p - f' p) (fun p => q p - q' p) := by
  obtain ⟨F, Q, hF, hQ, he⟩ := hf
  obtain ⟨F', Q', hF', hQ', he'⟩ := hf'
  refine ⟨F - F', Q - Q', fun p => ?_, fun p => ?_, ?_⟩
  · change F p - F' p = _
    rw [hF, hF']
  · change Q p - Q' p = _
    rw [hQ, hQ']
  · rw [metric_integral_sub, metric_integral_sub, he, he']

/-- The product rule turns density divergence into the first Green identity. -/
theorem green_first_of_divergence (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g)
    (hD : DivergenceIdentity g C b) (u v : GlobalSmooth S)
    (hX : IsCompact (sectionSupport (mulSection v (gradient g u)).val)) :
    IntegralIdentity g b.metric (firstIntegrand g C u v)
      (fun p => v.val p.val * flux g b (gradient g u) p) := by
  obtain ⟨F, Q, hF, hQ, he⟩ := hD (mulSection v (gradient g u)) hX
  refine ⟨F, Q, fun p => ?_, fun p => ?_, he⟩
  · rw [hF, first_integrand_divergence_apply]
  · rw [hQ, flux_product]

theorem green_second_of_divergence (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g)
    (hD : DivergenceIdentity g C b) (u v : GlobalSmooth S)
    (hX : IsCompact (sectionSupport (mulSection v (gradient g u)).val))
    (hY : IsCompact (sectionSupport (mulSection u (gradient g v)).val)) :
    IntegralIdentity g b.metric (secondIntegrand g C u v)
      (fun p => v.val p.val * flux g b (gradient g u) p -
        u.val p.val * flux g b (gradient g v) p) := by
  have h := integral_identity_sub g b.metric
    (green_first_of_divergence g C b hD u v hX)
    (green_first_of_divergence g C b hD v u hY)
  simpa only [first_integrand_sub_swap] using h

theorem divergence_boundaryless_of_divergence (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g)
    (hD : DivergenceIdentity g C b) (hB : intrinsicBoundary S = ∅)
    (X : Field S) (hX : IsCompact (sectionSupport X.val)) :
    IntegralZero g (divergence C X) := by
  obtain ⟨F, Q, hF, _, he⟩ := hD X hX
  have hQ : Q = 0 := by
    ext p
    exact False.elim (by simpa only [hB, Set.mem_empty_iff_false] using p.property)
  exact ⟨F, hF, he.trans (hQ ▸ metric_integral_zero b.metric)⟩

theorem green_first_boundaryless_of_divergence (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g)
    (hD : DivergenceIdentity g C b) (hB : intrinsicBoundary S = ∅)
    (u v : GlobalSmooth S)
    (hX : IsCompact (sectionSupport (mulSection v (gradient g u)).val)) :
    IntegralZero g (firstIntegrand g C u v) := by
  obtain ⟨F, hF, he⟩ := divergence_boundaryless_of_divergence g C b hD hB
    (mulSection v (gradient g u)) hX
  exact ⟨F, fun p => (hF p).trans (first_integrand_divergence_apply g C u v p), he⟩

/-- Canonical representatives reduce the density theorem to a numerical
identity, with continuity and compact support already proved above. -/
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

end IntegralReductions

/-! Reductions used by the unconditional final assembly below. -/
theorem divergence_compact_from_theorem
    (hD : P202Specs.Geometry.DivergenceGreen.divergence_theoremType.{u}) :
    P202Specs.Geometry.DivergenceGreen.divergence_compactType.{u} := by
  intro n a M _ _ S g C hC b X
  exact hD g C hC b X isClosed_closure.isCompact

theorem green_first_from_theorem
    (hD : P202Specs.Geometry.DivergenceGreen.divergence_theoremType.{u}) :
    P202Specs.Geometry.DivergenceGreen.green_firstType.{u} := by
  intro n a M _ _ S g C hC b u v
  exact green_first_of_divergence g C b (hD g C hC b) u v isClosed_closure.isCompact

theorem green_second_from_theorem
    (hD : P202Specs.Geometry.DivergenceGreen.divergence_theoremType.{u}) :
    P202Specs.Geometry.DivergenceGreen.green_secondType.{u} := by
  intro n a M _ _ S g C hC b u v
  exact green_second_of_divergence g C b (hD g C hC b) u v
    isClosed_closure.isCompact isClosed_closure.isCompact
section EmptyBoundary
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- An empty boundary has an empty normal field; no unit vector is selected
in any ambient tangent space. -/
theorem boundary_geometry_of_empty (g : RiemannianMetric S)
    (hB : intrinsicBoundary S = ∅) : Nonempty (BoundaryGeometry g) := by
  letI : IsEmpty (intrinsicBoundary S) := ⟨fun p => by
    simpa only [hB, Set.mem_empty_iff_false] using p.property⟩
  obtain ⟨B, hnatural, gB, _, hinduced, _, _, _⟩ :=
    RiemannianVolume.boundaryDensity_exists S g
  exact ⟨{ manifold := B
           natural := hnatural
           metric := gB
           induced := hinduced
           normal := fun p => isEmptyElim p
           unit := fun p => isEmptyElim p
           orthogonal := fun p => isEmptyElim p
           outward := fun p => isEmptyElim p
           normal_smooth := fun p => isEmptyElim p }⟩

theorem divergence_boundaryless_from_theorem
    (hD : P202Specs.Geometry.DivergenceGreen.divergence_theoremType.{u}) :
    P202Specs.Geometry.DivergenceGreen.divergence_boundarylessType.{u} := by
  intro n a M _ S g C hC hB X hX
  obtain ⟨b⟩ := boundary_geometry_of_empty g hB
  exact divergence_boundaryless_of_divergence g C b (hD g C hC b) hB X hX

theorem green_first_boundaryless_from_theorem
    (hD : P202Specs.Geometry.DivergenceGreen.divergence_theoremType.{u}) :
    P202Specs.Geometry.DivergenceGreen.green_first_boundarylessType.{u} := by
  intro n a M _ S g C hC hB u v hX
  obtain ⟨b⟩ := boundary_geometry_of_empty g hB
  exact green_first_boundaryless_of_divergence g C b (hD g C hC b) hB u v hX

end EmptyBoundary

section ZeroDimension
variable {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 0 a M}

theorem boundary_geometry_zero_dimension (g : RiemannianMetric S) :
    Nonempty (BoundaryGeometry g) :=
  boundary_geometry_of_empty g (SmoothManifolds.intrinsicBoundary_zero S)

theorem divergence_zero_dimension (C : Connection (tangentBundle S))
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
  · exact (divergence_zero_dimension C X p).symm
  · exact False.elim (by
      have h := p.property
      have he : intrinsicBoundary S = ∅ := SmoothManifolds.intrinsicBoundary_zero S
      simpa only [he, Set.mem_empty_iff_false] using h)
  · rw [metric_integral_zero, metric_integral_zero]

end ZeroDimension
/-! Full integral conclusions, using the authorized upstream geometric results.
No global orientation is required by the density theorem. -/

/-- A natural induced boundary metric and smooth outward unit normal exist;
the normal is an empty dependent function when the boundary is empty. -/
theorem boundary_geometry_exists :
    P202Specs.Geometry.DivergenceGreen.boundary_geometry_existsType.{u} :=
  GreenBoundaryFlux.boundary_geometry_exists

/-- Compact-support density divergence, valid also on nonorientable manifolds. -/
theorem divergence_theorem :
    P202Specs.Geometry.DivergenceGreen.divergence_theoremType.{u} :=
  GreenDivergenceCore.divergence_theorem

/-- Oriented Stokes with the actual contraction, exterior derivative, induced
outward-first orientation, flux and the fixed density integrals. -/
theorem oriented_stokes :
    P202Specs.Geometry.DivergenceGreen.oriented_stokesType.{u} := by
  intro n a M _ S g C hC b o X hX
  obtain ⟨q, hq, hregular, _hcompact, hrepresentation⟩ :=
    GreenDivergenceCore.oriented_stokes g C hC b o X hX
  exact ⟨q, hq, hregular, hrepresentation⟩

/-- Divergence on a compact manifold with smooth, possibly empty, boundary. -/
theorem divergence_compact :
    P202Specs.Geometry.DivergenceGreen.divergence_compactType.{u} :=
  divergence_compact_from_theorem divergence_theorem

/-- First Green identity for arbitrary smooth scalar functions on a compact
manifold with smooth boundary. -/
theorem green_first : P202Specs.Geometry.DivergenceGreen.green_firstType.{u} :=
  green_first_from_theorem divergence_theorem

/-- Second Green identity, obtained by exchanging the two functions and
subtracting the first identities. -/
theorem green_second : P202Specs.Geometry.DivergenceGreen.green_secondType.{u} :=
  green_second_from_theorem divergence_theorem

/-- Boundaryless compact-support divergence, without compactness of M. -/
theorem divergence_boundaryless :
    P202Specs.Geometry.DivergenceGreen.divergence_boundarylessType.{u} :=
  divergence_boundaryless_from_theorem divergence_theorem

/-- Boundaryless first Green identity. Only the product field v grad u is
required to have compact support. -/
theorem green_first_boundaryless :
    P202Specs.Geometry.DivergenceGreen.green_first_boundarylessType.{u} :=
  green_first_boundaryless_from_theorem divergence_theorem

end P202.Geometry.DivergenceGreen
