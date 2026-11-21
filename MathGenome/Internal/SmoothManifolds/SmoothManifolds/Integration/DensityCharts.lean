import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.DensityCharts
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.LocalSigned
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.MetricVolume

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical Topology BigOperators
namespace SmoothManifolds.DensityChartResults
open ModelData AtlasData TangentData TangentBundleData OrientationData MetricVolumeData
  DensityIntegrationData Set MeasureTheory Filter Module
open LocalIntegrationResults
universe u

/-- Coefficient on the relative model, with zero at artificial chart edges. -/
def modelDensity {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ρ : DensityField S)
    (x : ModelSpace n a) : ℝ :=
  if hx : x ∈ c.target then
    densityCoefficient K c hc ⟨c.symm x, c.map_target hx⟩ (ρ (c.symm x)) else 0

theorem density_on_model {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ρ : DensityField S) (x : ModelSpace n a) :
    coordinateDensity K c hc ρ x.val = modelDensity K c hc ρ x := by
  change LocalIntegrationData.extendModel (modelDensity K c hc ρ) x.val = _
  simp only [LocalIntegrationData.extendModel, dite_eq_left x.property]

theorem density_at {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : DensityField S) (p : c.source) :
    coordinateDensity K c hc ω (c p.val).val =
      densityCoefficient K c hc p (ω p.val) := by
  change LocalIntegrationData.extendModel (modelDensity K c hc ω) (c p.val).val = _
  simp only [LocalIntegrationData.extendModel, dite_eq_left (c p.val).property]
  change modelDensity K c hc ω (c p.val) = _
  simp only [modelDensity, dite_eq_left (c.map_source p.property)]
  let f : c.source → ℝ := fun q => densityCoefficient K c hc q (ω q.val)
  change f ⟨c.symm (c p.val), c.map_target (c.map_source p.property)⟩ = f p
  exact congrArg f (Subtype.ext (c.left_inv p.property))

/-- A nonzero zero-extended coefficient comes from a nonzero section value. -/
theorem density_nonzero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : DensityField S) (x : Euclidean n)
    (hx : coordinateDensity K c hc ω x ≠ 0) :
    ∃ p ∈ sectionSupport ω, p ∈ c.source ∧ (c p).val = x := by
  change LocalIntegrationData.extendModel (modelDensity K c hc ω) x ≠ 0 at hx
  unfold LocalIntegrationData.extendModel at hx
  split_ifs at hx with hm
  · unfold modelDensity at hx
    split_ifs at hx with ht
    · refine ⟨c.symm ⟨x, hm⟩, ?_, c.map_target ht, ?_⟩
      · apply subset_closure
        intro hz
        apply hx
        simp [densityCoefficient, hz]
      · exact congrArg Subtype.val (c.right_inv ht)
    · exact (hx rfl).elim
  · exact (hx rfl).elim

/-- Compact containment gives a compact ambient set containing all nonzero
coordinate values, even when the support meets the true boundary. -/
theorem density_compact_container {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : CompactDensity S) (hω : sectionSupport ω.field ⊆ c.source) :
    IsCompact ((fun p : M => (c p).val) '' sectionSupport ω.field) ∧
      Function.support (coordinateDensity K c hc ω.field) ⊆
        (fun p : M => (c p).val) '' sectionSupport ω.field := by
  refine ⟨ω.compact_support.image_of_continuousOn
    (continuous_subtype_val.comp_continuousOn (c.continuousOn.mono hω)), ?_⟩
  intro x hx
  obtain ⟨p, hp, hpc, heq⟩ := density_nonzero K c hc ω.field x hx
  exact ⟨p, hp, heq⟩

/-- Compact support leaves a neighborhood of every artificial edge on which
zero extension is identically zero in the entire ambient space. -/
theorem artificial_edges_proof :
    Specs.SmoothManifolds.Integration.DensityCharts.artificial_edgesType.{u} := by
  intro n a M _ S K c hc ω hω x hx
  obtain ⟨hC, hsub⟩ := density_compact_container K c hc ω hω
  refine ⟨((fun p : M => (c p).val) '' sectionSupport ω.field)ᶜ,
    hC.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨p, hp, hpx⟩
    have he : c p = x := Subtype.ext hpx
    exact hx (he ▸ c.map_source (hω hp))
  · intro y hy
    by_contra hn
    exact hy (hsub hn)

theorem modelDensity_continuous {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : CompactDensity S) (hω : sectionSupport ω.field ⊆ c.source) :
    Continuous (modelDensity K c hc ω.field) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ c.target
  · let f : c.source → ℝ := fun p =>
      densityCoefficient K c hc p (ω.field p.val)
    have hf : Continuous f :=
      ω.continuous K c hc
    have hcont : ContinuousOn (modelDensity K c hc ω.field) c.target := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      convert hf.comp c.toHomeomorphSourceTarget.symm.continuous using 1
      funext y
      simp only [Set.domRestrict_apply, modelDensity, y.property, ↓reduceDIte,
        Function.comp_apply]
      change f ⟨c.symm y.val, c.map_target y.property⟩ = f (c.toHomeomorphSourceTarget.symm y)
      congr 1

    exact hcont.continuousAt (c.open_target.mem_nhds hx)
  · obtain ⟨U, hU, hxU, hzero⟩ := artificial_edges_proof S K c hc ω hω x hx
    have he : modelDensity K c hc ω.field =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds hxU] with y hy
      have hh := hzero y.val hy
      exact (density_on_model K c hc ω.field y).symm.trans hh
    exact continuousAt_const.congr_of_eventuallyEq he

/-- Relative continuity suffices for integrability of a compactly supported
ambient extension, even when that extension jumps at the true boundary. -/
theorem integrable_extendModel_compact {n : ℕ} {a : ModelKind}
    (f : ModelSpace n a → ℝ) (hf : Continuous f) (C : Set (Euclidean n))
    (hC : IsCompact C) (hm : C ⊆ modelSet n a)
    (hs : Function.support (LocalIntegrationData.extendModel f) ⊆ C) :
    Integrable (LocalIntegrationData.extendModel f) := by
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply ContinuousOn.integrableOn_compact hC
  apply continuousOn_iff_continuous_domRestrict.mpr
  let g : C → ModelSpace n a := fun x => ⟨x.val, hm x.property⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  apply (hf.comp hg).congr
  intro x
  change f (g x) = LocalIntegrationData.extendModel f x.val
  simp only [LocalIntegrationData.extendModel, dite_eq_left (hm x.property)]
  rfl

theorem integrable_proof : Specs.SmoothManifolds.Integration.DensityCharts.integrableType.{u} := by
  intro n a M _ S K c hc ω hω
  obtain ⟨hC, hsub⟩ := density_compact_container K c hc ω hω
  apply integrable_extendModel_compact (modelDensity K c hc ω.field)
    (modelDensity_continuous K c hc ω hω) _ hC _ hsub
  rintro x ⟨p, hp, rfl⟩
  exact (c p).property

theorem model_continuous_proof :
    Specs.SmoothManifolds.Integration.DensityCharts.model_continuousType.{u} := by
  intro n a M _ S K c hc ρ hρ
  exact (modelDensity_continuous K c hc ρ hρ).congr
    (fun x => (density_on_model K c hc ρ.field x).symm)

/-- A genuine choice of intrinsic coordinates cannot alter a density coefficient. -/
theorem densityCoefficient_coordinates_eq {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K L : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (ρ : DensityLine S p.val) :
    densityCoefficient K c hc p ρ = densityCoefficient L c hc p ρ := by
  change ρ.val _ = ρ.val _
  exact congrArg ρ.val (OrientationResults.coordinateVector_independent K L c hc p)

theorem coordinateIntegral_coordinates_eq {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K L : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ρ : DensityField S) :
    DensityIntegrationData.coordinateIntegral K c hc ρ =
      DensityIntegrationData.coordinateIntegral L c hc ρ := by
  unfold DensityIntegrationData.coordinateIntegral
  congr 1
  funext x
  change LocalIntegrationData.extendModel (modelDensity K c hc ρ) x =
    LocalIntegrationData.extendModel (modelDensity L c hc ρ) x
  unfold LocalIntegrationData.extendModel
  split_ifs with hm
  · unfold modelDensity
    split_ifs with ht
    · exact densityCoefficient_coordinates_eq K L c hc _ _
    · rfl
  · rfl

theorem support_in_overlap {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S) (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : DensityField S) (hdω : sectionSupport ω ⊆ d.source) :
    Function.support (coordinateDensity K c hc ω) ⊆
      ambientDomain (c.symm.trans d).source := by
  intro x hx
  obtain ⟨p, hp, hpc, rfl⟩ := density_nonzero K c hc ω x hx
  refine ⟨c p, ⟨c.map_source hpc, ?_⟩, rfl⟩
  simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, c.left_inv hpc] using hdω hp

/-- Substitution for actual chart transitions, without choosing a global
Jacobian sign. It is valid for arbitrary sections for which the integrals
exist in the Bochner convention; compactness is not used in this identity. -/
theorem coordinateIntegral_eq
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (ω : DensityField S)
    (hcω : sectionSupport ω ⊆ c.source) (hdω : sectionSupport ω ⊆ d.source) :
    DensityIntegrationData.coordinateIntegral K c hc ω = DensityIntegrationData.coordinateIntegral K d hd ω := by
  let e := c.symm.trans d
  let U := ambientDomain e.source
  let V := ambientDomain e.target
  let ψ := ambientTransition e
  let J := fderivWithin ℝ ψ U
  let f := coordinateDensity K c hc ω
  let g := coordinateDensity K d hd ω
  have hU : MeasurableSet U := ambientDomain_measurable e.open_source
  have hJ : ∀ x ∈ U, HasFDerivWithinAt ψ (J x) U x :=
    fun x hx => (ambientTransition_differentiable e
      (S.smoothStructure.property.1.2 c hc d hd).1 x hx).hasFDerivWithinAt
  have hfg : ∀ x ∈ U, |(J x).det| * g (ψ x) = f x := by
    rintro x ⟨y, hy, rfl⟩
    have hpc : c.symm y ∈ c.source := c.map_target hy.1
    have hpd : c.symm y ∈ d.source := hy.2
    let p : ↥(c.source ∩ d.source) := ⟨c.symm y, hpc, hpd⟩
    have hcy : c p.val = y := c.right_inv hy.1
    have hψy : ψ y.val = (d p.val).val := by
      change ambientTransition e y.val = _
      rw [ambientTransition_at]
      rfl
    have hdet : (J y.val).det = transitionDeterminant K c d hc hd p := by
      rw [← hcy]
      exact ambientTransition_det OrientationResults.transition_jacobian S K c d hc hd p
    change |(J y.val).det| * coordinateDensity K d hd ω (ψ y.val) =
      coordinateDensity K c hc ω y.val
    have hleft : coordinateDensity K c hc ω y.val =
        densityCoefficient K c hc ⟨p.val, hpc⟩ (ω p.val) :=
      (congrArg (coordinateDensity K c hc ω) (congrArg Subtype.val hcy.symm)).trans
        (density_at K c hc ω ⟨p.val, hpc⟩)
    have hright : coordinateDensity K d hd ω (ψ y.val) =
        densityCoefficient K d hd ⟨p.val, hpd⟩ (ω p.val) :=
      (congrArg (coordinateDensity K d hd ω) hψy).trans
        (density_at K d hd ω ⟨p.val, hpd⟩)
    calc
      _ = |transitionDeterminant K c d hc hd p| *
          densityCoefficient K d hd ⟨p.val, hpd⟩ (ω p.val) :=
        congrArg₂ (fun t b : ℝ => |t| * b) hdet hright
      _ = densityCoefficient K c hc ⟨p.val, hpc⟩ (ω p.val) :=
        (MetricVolumeResults.density_transition K d c hd hc
          ⟨p.val, hpd, hpc⟩ (ω p.val)).symm
      _ = _ := hleft.symm
  have hsub := integral_image_eq_integral_abs_det_fderiv_smul volume hU hJ
    (ambientTransition_injective e) g
  rw [ambientTransition_image e] at hsub
  have hfU : Function.support f ⊆ U := support_in_overlap K c d hc ω hdω
  have hgV : Function.support g ⊆ V := by
    have hh := support_in_overlap K d c hd ω hcω
    have heq : e.symm = d.symm.trans c := by
      dsimp only [e]
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
    rw [← heq] at hh
    exact hh
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


theorem chart_independence_proof :
    Specs.SmoothManifolds.Integration.DensityCharts.chart_independenceType.{u} := by
  intro n a M _ S K L c d hc hd ρ hcρ hdρ
  exact (coordinateIntegral_eq S K c d hc hd ρ.field hcρ hdρ).trans
    (coordinateIntegral_coordinates_eq K L d hd ρ.field)

/-- The empty exterior product is the canonical unit of Λ⁰. -/
theorem densityCoefficient_zero {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (K : FiberCoordinates S) (c : ModelChart 0 a M)
    (hc : c ∈ S.smoothStructure.val) (ρ : DensityField S) (p : c.source) :
    densityCoefficient K c hc p (ρ p.val) = zeroCoefficient ρ p.val := by
  have hcoord : OrientationData.coordinateVector K c hc p =
      (exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1 := by
    apply (exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).injective
    simp [OrientationData.coordinateVector]
  change (ρ p.val).val _ = (ρ p.val).val _
  exact congrArg (ρ p.val).val hcoord

theorem zero_coordinate_evaluation {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (K : FiberCoordinates S)
    (c : ModelChart 0 a M) (hc : c ∈ S.smoothStructure.val) (ρ : DensityField S)
    (p : c.source) : DensityIntegrationData.coordinateIntegral K c hc ρ =
      zeroCoefficient ρ p.val := by
  change (∫ x, coordinateDensity K c hc ρ x) = _
  exact (zero_euclidean_integral _ (c p.val).val).trans
    ((density_at K c hc ρ p).trans (densityCoefficient_zero K c hc ρ p))

theorem zero_compact_finite_proof :
    Specs.SmoothManifolds.Integration.DensityCharts.zero_compact_finiteType.{u} := by
  intro a M _ S C hC
  haveI := zero_manifold_discrete S
  exact hC.finite_of_discrete

theorem zero_support_singleton {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (c : ModelChart 0 a M) (ρ : DensityField S)
    (hρ : sectionSupport ρ ⊆ c.source) (p : c.source) :
    ∀ q : M, q ≠ p.val → ρ q = 0 := by
  intro q hq
  by_contra hn
  have hqc : q ∈ c.source := hρ (subset_closure hn)
  haveI := zero_chart_subsingleton c
  exact hq (congrArg Subtype.val (Subsingleton.elim (⟨q, hqc⟩ : c.source) p))

/-- The coordinate integral is the finite unsigned sum even for an empty chart. -/
theorem zero_coordinate_proof :
    Specs.SmoothManifolds.Integration.DensityCharts.zero_coordinateType.{u} := by
  intro a M _ S K c hc ρ hρ
  let h := zero_compact_finite_proof S (sectionSupport ρ.field) ρ.compact_support
  have hsum : (∑ᶠ p, zeroCoefficient ρ.field p) =
      ∑ p ∈ h.toFinset, zeroCoefficient ρ.field p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    apply h.mem_toFinset.mpr
    apply subset_closure
    intro hz
    apply hp
    simp [zeroCoefficient, hz]
  by_cases hne : c.source.Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hsingle : (∑ᶠ q, zeroCoefficient ρ.field q) = zeroCoefficient ρ.field p := by
      apply finsum_eq_single _ p
      intro q hq
      simp [zeroCoefficient, zero_support_singleton c ρ.field hρ ⟨p, hp⟩ q hq]
    refine ⟨⟨h, ?_⟩, fun q => zero_coordinate_evaluation S K c hc ρ.field q⟩
    exact (zero_coordinate_evaluation S K c hc ρ.field ⟨p, hp⟩).trans
      (hsingle.symm.trans hsum)
  · have hzero : ∀ p, ρ.field p = 0 := by
      intro p
      by_contra hp
      exact hne ⟨p, hρ (subset_closure hp)⟩
    have hint : DensityIntegrationData.coordinateIntegral K c hc ρ.field = 0 := by
      unfold DensityIntegrationData.coordinateIntegral
      have hf : coordinateDensity K c hc ρ.field = 0 := by
        funext x
        change LocalIntegrationData.extendModel (modelDensity K c hc ρ.field) x = 0
        unfold LocalIntegrationData.extendModel
        split_ifs with hm
        · unfold modelDensity
          split_ifs with ht
          · simp only [hzero, map_zero]
          · rfl
        · rfl
      exact (congrArg (fun f : Euclidean 0 → ℝ => ∫ x, f x) hf).trans
        (integral_zero _ _)
    refine ⟨⟨h, ?_⟩, ?_⟩
    · exact hint.trans (by simp [zeroCoefficient, hzero])
    · intro p
      exact (hne ⟨p.val, p.property⟩).elim

end SmoothManifolds.DensityChartResults
