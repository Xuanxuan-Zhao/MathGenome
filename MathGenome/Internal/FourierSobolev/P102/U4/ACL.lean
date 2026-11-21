import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ACL
import MathGenome.Internal.FourierSobolev.P102.U4.RegularDerivatives
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.AbsoluteContinuityOnLines

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Topology

namespace P102.U4.ACL

/-- Euclidean coordinates as the finite product. This equivalence preserves
Lebesgue volume, although the two norms differ when d > 1. -/
abbrev coordinates (d : ℕ) : Space d ≃L[ℝ] (Fin d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

/-- The original open set, written in product coordinates. -/
def coordinateDomain {d : ℕ} (Ω : Opens (Space d)) : Opens (Fin d → ℝ) :=
  ⟨(coordinates d).symm ⁻¹' (Ω : Set (Space d)),
    Ω.isOpen.preimage (coordinates d).symm.continuous⟩

@[simp] theorem line_coordinates {d : ℕ} (j : Fin d) (z : Transverse j) (t : ℝ) :
    coordinates d (line j z t) = ExpandedFA.Sobolev.Lines.coordinateLine j z t := rfl

@[simp] theorem coordinate_fiber {d : ℕ} (Ω : Opens (Space d))
    (j : Fin d) (z : Transverse j) :
    (ExpandedFA.Sobolev.Lines.fiber (coordinateDomain Ω) j z : Set ℝ) = fiber Ω j z := rfl

set_option maxHeartbeats 800000 in
/-- The ambient a.e. representative identity holds on almost every fiber. -/
theorem ae_on_fibers {d : ℕ} {Ω : Opens (Space d)} (j : Fin d)
    {P : Space d → Prop} (hP : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), P x) :
    ∀ᵐ z : Transverse j ∂volume,
      ∀ᵐ t ∂volume.restrict (fiber Ω j z), P (line j z t) := by
  have h := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hP
  have hc := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae h
  have hcoord : ∀ᵐ x ∂volume.restrict (coordinateDomain Ω : Set (Fin d → ℝ)),
      P ((coordinates d).symm x) :=
    (ae_restrict_iff' (coordinateDomain Ω).isOpen.measurableSet).mpr hc
  have hl := ExpandedFA.Sobolev.Lines.ae_on_fibers (Ω := coordinateDomain Ω) j hcoord
  simpa only [coordinate_fiber, coordinates, PiLp.coe_symm_continuousLinearEquiv,
    line] using hl

/-- Coordinate Fubini for the canonical Euclidean volume. -/
theorem integral_lines {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (j : Fin d)
    {h : Space d → 𝕜} (hh : Integrable h volume) :
    (∫ x, h x) = ∫ z : Transverse j, ∫ t : ℝ, h (line j z t) := by
  have hp := PiLp.volume_preserving_toLp (Fin d)
  rw [← hp.integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding h]
  exact ExpandedFA.Sobolev.Lines.integral_coordinateLines j
    (hp.integrable_comp_of_integrable hh)

/-- Integrability of the pairing implies integrability on almost every line. -/
theorem integrable_lines {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (j : Fin d)
    {h : Space d → 𝕜} (hh : Integrable h volume) :
    ∀ᵐ z : Transverse j ∂volume, Integrable (fun t => h (line j z t)) volume := by
  exact ExpandedFA.Sobolev.Lines.integrable_coordinateLines j
    ((PiLp.volume_preserving_toLp (Fin d)).integrable_comp_of_integrable hh)

theorem line_contDiff {d : ℕ} (j : Fin d) (z : Transverse j) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (line j z) :=
  (coordinates d).symm.contDiff.comp
    (ExpandedFA.Sobolev.Lines.coordinateLine_contDiff j z)

theorem line_hasDerivAt {d : ℕ} (j : Fin d) (z : Transverse j) (t : ℝ) :
    HasDerivAt (line j z) (coordinateVector d j) t := by
  have he : (coordinates d).symm (ExpandedFA.Distributions.coordinateVector j) =
      coordinateVector d j := by
    ext k
    simp [coordinateVector, ExpandedFA.Distributions.coordinateVector,
      EuclideanSpace.basisFun_apply, EuclideanSpace.single, coordinates]
  change HasDerivAt (((coordinates d).symm : _ → _) ∘
    ExpandedFA.Sobolev.Lines.coordinateLine j z) (coordinateVector d j) t
  rw [← he]
  exact (coordinates d).symm.hasFDerivAt.comp_hasDerivAt t
    (ExpandedFA.Sobolev.Lines.coordinateLine_hasDerivAt j z t)

theorem line_isClosedEmbedding {d : ℕ} (j : Fin d) (z : Transverse j) :
    Topology.IsClosedEmbedding (line j z) :=
  (coordinates d).symm.toHomeomorph.isClosedEmbedding.comp
    (ExpandedFA.Sobolev.Lines.coordinateLine_isClosedEmbedding j z)

theorem fiber_isOpen {d : ℕ} (Ω : Opens (Space d)) (j : Fin d) (z : Transverse j) :
    IsOpen (fiber Ω j z) := Ω.isOpen.preimage (line_contDiff j z).continuous

/-- The test derivative used by the distribution interface is the ordinary
one-variable derivative of its restriction to a coordinate line. -/
theorem testPartial_on_line {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (φ : TestSpace 𝕜 Ω) (j : Fin d) (z : Transverse j) (t : ℝ) :
    testPartialWord Ω [j] φ (line j z t) = deriv (fun s => φ (line j z s)) t := by
  rw [testPartialWord_coe]
  exact ((φ.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (line_hasDerivAt j z t)).deriv.symm

/-- Local L¹ is enough for each compactly supported pairing; ambient values
outside Ω play no part. -/
theorem integrable_test_mul {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (φ : TestSpace 𝕜 Ω) {u : Space d → 𝕜}
    (hu : LocallyIntegrableOn u Ω volume) :
    Integrable (fun x => φ x * u x) volume :=
  φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hu

/-- The weak identity is expressed using actual smooth tests and canonical
coordinate derivatives, with the required bilinear sign convention. -/
theorem weak_iff_test_identity {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (j : Fin d) {u v : Space d → 𝕜}
    (hu : LocallyIntegrableOn u Ω volume) (hv : LocallyIntegrableOn v Ω volume) :
    distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v ↔
      ∀ φ : TestSpace 𝕜 Ω,
        (∫ x, φ x * v x) = -(∫ x, testPartialWord Ω [j] φ x * u x) := by
  have he (φ : TestSpace 𝕜 Ω) :
      distributionPartial {j} (regularDistribution Ω u) φ =
        -(∫ x, testPartialWord Ω [j] φ x * u x) := by
    simp [distributionPartial, regularDistribution,
      TestFunction.integralAgainstBilinCLM_eq_integral hu]
  have hv' (φ : TestSpace 𝕜 Ω) :
      regularDistribution Ω v φ = ∫ x, φ x * v x :=
    TestFunction.integralAgainstBilinCLM_eq_integral hv
  constructor
  · intro h φ
    exact (hv' φ).symm.trans ((congrArg (fun T : DistributionSpace 𝕜 Ω => T φ) h).symm.trans (he φ))
  · intro h
    ext φ
    exact (he φ).trans ((h φ).symm.trans (hv' φ).symm)

/-- Fiberwise integration by parts gives the converse under precisely local
integrability of u and the assembled line derivative v. -/
theorem representative_to_weak {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (j : Fin d) {u v : Space d → 𝕜}
    (hu : LocallyIntegrableOn u Ω volume) (hv : LocallyIntegrableOn v Ω volume)
    (hrep : HasRepresentative Ω j u v) :
    distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v := by
  obtain ⟨f, huf, hf⟩ := hrep
  apply (weak_iff_test_identity j hu hv).mpr
  intro φ
  have h₁ := integrable_test_mul (testPartialWord Ω [j] φ) hu
  have h₂ := integrable_test_mul φ hv
  have he : ∀ᵐ z : Transverse j ∂volume,
      (∫ t, φ (line j z t) * v (line j z t)) =
        -(∫ t, testPartialWord Ω [j] φ (line j z t) * u (line j z t)) := by
    filter_upwards [hf, ae_on_fibers j huf,
      integrable_lines j h₁, integrable_lines j h₂] with z hz hze h₁z h₂z
    let ψ : ℝ → 𝕜 := fun t => φ (line j z t)
    have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ := φ.contDiff.comp (line_contDiff j z)
    have hcψ : HasCompactSupport ψ :=
      φ.hasCompactSupport.comp_isClosedEmbedding (line_isClosedEmbedding j z)
    have hsψ : tsupport ψ ⊆ fiber Ω j z :=
      (tsupport_comp_subset_preimage φ (line_contDiff j z).continuous).trans
        (preimage_mono φ.tsupport_subset)
    have hre : (fun t => deriv ψ t * f (line j z t)) =ᵐ[volume]
        (fun t => deriv ψ t * u (line j z t)) := by
      filter_upwards [(ae_restrict_iff' (fiber_isOpen Ω j z).measurableSet).mp hze] with t ht
      by_cases htU : t ∈ fiber Ω j z
      · rw [ht htU]
      · have hdz : deriv ψ t = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => htU (tsupport_deriv_subset.trans hsψ h))
        simp [hdz]
    have hdint : Integrable (fun t => deriv ψ t * u (line j z t)) volume := by
      simpa only [testPartial_on_line] using h₁z
    have hibp := ExpandedFA.Sobolev.Lines.integral_test_mul_density_on_open
      (fiber_isOpen Ω j z) hz.1 hz.2 hψ hcψ hsψ (hdint.congr hre.symm) h₂z
    rw [integral_congr_ae hre] at hibp
    simpa only [ψ, testPartial_on_line] using hibp
  rw [integral_lines j h₂, integral_lines j h₁]
  exact (integral_congr_ae he).trans (integral_neg _)

/-- A test in product coordinates, expressed in the canonical Euclidean space. -/
def testFromCoordinates {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)}
    (φ : TestFunction (coordinateDomain Ω) 𝕜 ⊤) : TestSpace 𝕜 Ω where
  toFun x := φ (coordinates d x)
  contDiff' := φ.contDiff.comp (coordinates d).contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (coordinates d).toHomeomorph
  tsupport_subset' := by
    intro x hx
    have h := (tsupport_comp_subset_preimage φ (coordinates d).continuous) hx
    exact φ.tsupport_subset h

@[simp] theorem testFromCoordinates_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (φ : TestFunction (coordinateDomain Ω) 𝕜 ⊤) (x : Space d) :
    testFromCoordinates φ x = φ (coordinates d x) := rfl

/-- The derivative bridge checks the actual coordinate vectors, rather than
identifying the two finite-dimensional norms. -/
theorem testFromCoordinates_partial {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (φ : TestFunction (coordinateDomain Ω) 𝕜 ⊤)
    (j : Fin d) (x : Space d) :
    testPartialWord Ω [j] (testFromCoordinates φ) x =
      ExpandedFA.Distributions.testPartialCLM [j] φ (coordinates d x) := by
  have hv : coordinates d (coordinateVector d j) =
      ExpandedFA.Distributions.coordinateVector j := by
    ext k
    by_cases hk : k = j
    · subst k
      simp [coordinates, coordinateVector, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single, ExpandedFA.Distributions.coordinateVector]
    · simp [coordinates, coordinateVector, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single, ExpandedFA.Distributions.coordinateVector, hk]
  rw [testPartialWord_coe, ExpandedFA.Distributions.testPartial_single_apply]
  change fderiv ℝ (φ ∘ coordinates d) x (coordinateVector d j) = _
  rw [fderiv_comp x (φ.contDiff.differentiable (by simp) _) (coordinates d).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv]
  exact congrArg (fderiv ℝ φ (coordinates d x)) hv

/-- Pulling a local L¹ function back to product coordinates preserves local L¹. -/
theorem locallyIntegrable_coordinates {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {u : Space d → 𝕜} (hu : LocallyIntegrableOn u Ω volume) :
    LocallyIntegrableOn (u ∘ (coordinates d).symm) (coordinateDomain Ω) volume := by
  apply (locallyIntegrableOn_iff (coordinateDomain Ω).isOpen.isLocallyClosed).mpr
  intro K hK hKc
  have hcompact := hKc.image (coordinates d).symm.continuous
  have hsub : (coordinates d).symm '' K ⊆ (Ω : Set (Space d)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hK hx
  exact ((PiLp.volume_preserving_toLp (Fin d)).integrableOn_image
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding).mp
      (hu.integrableOn_compact_subset hsub hcompact)

/-- A weak derivative on the canonical Euclidean space gives the genuine
single-coordinate test identity in finite-product coordinates. This places no
requirements on derivatives in the other directions. -/
theorem weak_identity_coordinates {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (j : Fin d) {u v : Space d → 𝕜}
    (hu : LocallyIntegrableOn u Ω volume) (hv : LocallyIntegrableOn v Ω volume)
    (hweak : distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v)
    (φ : TestFunction (coordinateDomain Ω) 𝕜 ⊤) :
    (∫ x, φ x * v ((coordinates d).symm x)) =
      -(∫ x, ExpandedFA.Distributions.testPartialCLM [j] φ x * u ((coordinates d).symm x)) := by
  have he := (weak_iff_test_identity j hu hv).mp hweak (testFromCoordinates φ)
  have hm := PiLp.volume_preserving_toLp (Fin d)
  rw [← hm.integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
    (fun x => testFromCoordinates φ x * v x),
    ← hm.integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
    (fun x => testPartialWord Ω [j] (testFromCoordinates φ) x * u x)] at he
  simp only [testFromCoordinates_partial, testFromCoordinates_apply] at he
  exact he

/-- In dimension one the empty transverse product carries a Dirac probability
measure. Thus the a.e. line assertion is the assertion on its sole line. -/
theorem representative_dimensionOne_iff {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space 1)) (u v : Space 1 → 𝕜) :
    HasRepresentative Ω (0 : Fin 1) u v ↔
      ∃ f : Space 1 → 𝕜, u =ᵐ[volume.restrict (Ω : Set (Space 1))] f ∧
        LocallyAC (fun t => f (line 0 0 t)) (fiber Ω 0 0) ∧
        ∀ᵐ t ∂volume.restrict (fiber Ω 0 0),
          HasDerivAt (fun s => f (line 0 0 s)) (v (line 0 0 t)) t := by
  let : IsEmpty {j : Fin 1 // j ≠ (0 : Fin 1)} :=
    ⟨fun j => j.property (Subsingleton.elim _ _)⟩
  simp only [HasRepresentative, Measure.volume_pi_eq_dirac (0 : Transverse (0 : Fin 1)),
    ae_dirac_eq, Filter.eventually_pure]

/-- Smooth functions on Ω supply the representative themselves. This checks
that no behavior of an ambient representative off Ω is part of the definition. -/
theorem representative_of_contDiffOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (j : Fin d) {u : Space d → 𝕜}
    (hu : ContDiffOn ℝ 1 u Ω) :
    HasRepresentative Ω j u (fun x => fderiv ℝ u x (coordinateVector d j)) := by
  refine ⟨u, Filter.EventuallyEq.rfl, Filter.Eventually.of_forall fun z => ⟨?_, ?_⟩⟩
  · intro a b hab
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact hu.comp ((line_contDiff j z).of_le (by simp)).contDiffOn hab
  · apply (ae_restrict_iff' (fiber_isOpen Ω j z).measurableSet).mpr
    exact Filter.Eventually.of_forall fun t ht =>
      ((hu.contDiffAt (Ω.isOpen.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
        (line_hasDerivAt j z t)

namespace Forward
open ExpandedFA.Distributions ExpandedFA.Sobolev.Lines

/-- Completed Fubini for equality of two a.e. measurable functions. -/
theorem ae_eq_prod_of_slices {Y K : Type*} [MeasurableSpace Y] [MeasurableSpace K]
    {ν : Measure Y} {μ : Measure K} [SFinite μ] {𝕜 : Type} [RCLike 𝕜]
    {f g : Y × K → 𝕜} (hf : AEStronglyMeasurable f (ν.prod μ))
    (hg : AEStronglyMeasurable g (ν.prod μ))
    (he : ∀ᵐ y ∂ν, (fun t => f (y, t)) =ᵐ[μ] (fun t => g (y, t))) :
    f =ᵐ[ν.prod μ] g := by
  have hfm := hf.stronglyMeasurable_mk.measurable
  have hgm := hg.stronglyMeasurable_mk.measurable
  have he' : hf.mk f =ᵐ[ν.prod μ] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hfm hgm)).mpr
    filter_upwards [he, Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with y hy hfy hgy
    filter_upwards [hfy, hy, hgy] with t hft hyt hgt
    exact hft.symm.trans (hyt.trans hgt)
  exact hf.ae_eq_mk.trans (he'.trans hg.ae_eq_mk.symm)

/-- A field of continuous slice representatives is jointly a.e. equal to the
original measurable function. No measurability of the initial choice is needed. -/
theorem ae_eq_continuous_slices {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] {𝕜 : Type} [RCLike 𝕜]
    {a b : ℝ} (hab : a < b) (u : Y × ℝ → 𝕜) (f : Y → ℝ → 𝕜)
    (hu : AEStronglyMeasurable u (ν.prod (volume.restrict (Icc a b))))
    (hc : ∀ y, ContinuousOn (f y) (Icc a b))
    (he : ∀ᵐ y ∂ν, (fun t => u (y, t)) =ᵐ[volume.restrict (Icc a b)] f y) :
    u =ᵐ[ν.prod (volume.restrict (Icc a b))] (fun z => f z.1 z.2) := by
  let μ : Measure (Icc a b) := volume.comap Subtype.val
  let : IsFiniteMeasure μ := ⟨by
    change volume.comap (Subtype.val : Icc a b → ℝ) univ < ⊤
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume univ]
    simp only [image_univ, Subtype.range_val, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let : μ.IsOpenPosMeasure := intervalVolume_isOpenPosMeasure hab
  let F : Y → C(Icc a b, 𝕜) := fun y =>
    ⟨fun t => f y t, (hc y).comp_continuous continuous_subtype_val (fun t => t.property)⟩
  have hmp : MeasurePreserving (fun z : Y × Icc a b => (z.1, (z.2 : ℝ)))
      (ν.prod μ) (ν.prod (volume.restrict (Icc a b))) :=
    (MeasurePreserving.id ν).prod (measurePreserving_subtype_coe measurableSet_Icc)
  have hu' := hu.comp_measurePreserving hmp
  have he' : ∀ᵐ y ∂ν, (fun t : Icc a b => F y t) =ᵐ[μ]
      (fun t => u (y, t)) := by
    filter_upwards [he] with y hy
    exact (measurePreserving_subtype_coe measurableSet_Icc).quasiMeasurePreserving.ae hy.symm
  have hF : AEStronglyMeasurable F ν :=
    aestronglyMeasurable_continuousSlices _ hu' F he'
  have hFe : AEStronglyMeasurable (fun z : Y × Icc a b => F z.1 z.2) (ν.prod μ) := by
    exact continuous_eval.comp_aestronglyMeasurable
      ((hF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
        (measurable_snd.aestronglyMeasurable))
  have heq := ae_eq_prod_of_slices hu' hFe (he'.mono fun _ h => h.symm)
  have hem : MeasurableEmbedding (fun z : Y × Icc a b => (z.1, (z.2 : ℝ))) :=
    MeasurableEmbedding.id.prodMap (MeasurableEmbedding.subtype_coe measurableSet_Icc)
  rw [← hmp.map_eq]
  exact (hem.ae_map_iff).mpr heq

/-- Local L¹ supplies rectangle integrability in split coordinates. -/
theorem integrable_coordinate_rectangle {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U : Opens (Domain d)} {u : Domain d → 𝕜}
    (hu : LocallyIntegrableOn u U volume) (j : Fin d)
    (K : Set (ExpandedFA.Sobolev.Lines.Transverse j)) (hK : IsCompact K) (a b : ℝ)
    (hs : ∀ z ∈ K, ∀ t ∈ Icc a b, coordinateLine j z t ∈ U) :
    Integrable (fun p : ExpandedFA.Sobolev.Lines.Transverse j × ℝ =>
      u (coordinateLine j p.1 p.2))
      ((volume.restrict K).prod (volume.restrict (Icc a b))) := by
  let e := coordinateEquiv j
  let C : Set (Domain d) := e.symm '' (Icc a b ×ˢ K)
  have hC : IsCompact C := (isCompact_Icc.prod hK).image
    (Homeomorph.funSplitAt ℝ j).symm.continuous
  have hCs : C ⊆ U := by
    rintro _ ⟨⟨t,z⟩, htz, rfl⟩
    change (coordinateEquiv j).symm (t, z) ∈ (U : Set (Domain d))
    rw [coordinateEquiv_symm_apply]
    exact hs z htz.2 t htz.1
  have hi := hu.integrableOn_compact_subset hCs hC
  have hm := (coordinateEquiv_measurePreserving j).symm (coordinateEquiv j)
  have hp := (hm.integrableOn_image e.symm.measurableEmbedding).mp hi
  have hp' : IntegrableOn (fun p : ℝ × ExpandedFA.Sobolev.Lines.Transverse j =>
      u (coordinateLine j p.2 p.1)) (Icc a b ×ˢ K) volume := by
    simpa only [e, Function.comp_def, ← coordinateEquiv_symm_apply, Prod.mk.eta] using hp
  simpa only [IntegrableOn, ← Measure.prod_restrict, Function.comp_def,
    Prod.fst_swap, Prod.snd_swap] using hp'.swap

/-- A continuous choice on the good fibers is an ambient representative on
any compact interior rectangle. -/
theorem ae_eq_on_rectangle {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U : Opens (Domain d)} {u : Domain d → 𝕜}
    (hu : LocallyIntegrableOn u U volume) (j : Fin d)
    (f : ExpandedFA.Sobolev.Lines.Transverse j → ℝ → 𝕜)
    (hf : ∀ᵐ z : ExpandedFA.Sobolev.Lines.Transverse j ∂volume,
      (fun t => u (coordinateLine j z t)) =ᵐ[volume.restrict (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ)] f z ∧
      LocallyAbsolutelyContinuousOn (f z) (ExpandedFA.Sobolev.Lines.fiber U j z))
    (K : Set (ExpandedFA.Sobolev.Lines.Transverse j)) (hK : IsCompact K)
    (a b : ℝ) (hab : a < b)
    (hs : ∀ z ∈ K, ∀ t ∈ Icc a b, coordinateLine j z t ∈ U) :
    (fun p : ExpandedFA.Sobolev.Lines.Transverse j × ℝ => u (coordinateLine j p.1 p.2))
      =ᵐ[(volume.restrict K).prod (volume.restrict (Icc a b))]
        (fun p => f p.1 p.2) := by
  classical
  let Good (z : ExpandedFA.Sobolev.Lines.Transverse j) : Prop := z ∈ K ∧
    (fun t => u (coordinateLine j z t)) =ᵐ[volume.restrict (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ)] f z ∧
    LocallyAbsolutelyContinuousOn (f z) (ExpandedFA.Sobolev.Lines.fiber U j z)
  have hgood : ∀ᵐ z ∂volume.restrict K, Good z := by
    filter_upwards [ae_restrict_of_ae hf, ae_restrict_mem hK.measurableSet] with z hz hzK
    exact ⟨hzK, hz⟩
  let g : ExpandedFA.Sobolev.Lines.Transverse j → ℝ → 𝕜 := fun z =>
    if Good z then f z else 0
  have hc (z) : ContinuousOn (g z) (Icc a b) := by
    by_cases hz : Good z
    · simp only [g, ite_eq_left hz]
      have hsub : uIcc a b ⊆ (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ) := by
        rw [uIcc_of_le hab.le]
        exact fun t ht => hs z hz.1 t ht
      have hAC := hz.2.2 a b hsub
      simpa only [uIcc_of_le hab.le] using hAC.continuousOn
    · simp only [g, ite_eq_right hz]
      exact continuousOn_const
  have he : ∀ᵐ z ∂volume.restrict K,
      (fun t => u (coordinateLine j z t)) =ᵐ[volume.restrict (Icc a b)] g z := by
    filter_upwards [hgood] with z hz
    change (fun t => u (coordinateLine j z t)) =ᵐ[volume.restrict (Icc a b)]
      (if Good z then f z else 0)
    rw [ite_eq_left hz]
    exact ae_restrict_of_ae_restrict_of_subset (fun t ht => hs z hz.1 t ht) hz.2.1
  have heq := ae_eq_continuous_slices hab _ g
    (integrable_coordinate_rectangle hu j K hK a b hs).aestronglyMeasurable hc he
  apply heq.trans
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with p hp
  simp only [g, ite_eq_left hp]

/-- On a fixed compact segment, local L¹ and the weak test identity give
both slice integrability and every one-dimensional test identity on its tube. -/
theorem ae_segment_data {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U : Opens (Domain d)) (j : Fin d) (u v : Domain d → 𝕜)
    (hu : LocallyIntegrableOn u U volume) (hv : LocallyIntegrableOn v U volume)
    (hw : ∀ φ : TestFunction U 𝕜 ⊤,
      (∫ x, φ x * v x) = -(∫ x, testPartialCLM [j] φ x * u x)) (a b : ℝ) :
    ∀ᵐ z ∂volume.restrict (lineTube U j a b : Set (ExpandedFA.Sobolev.Lines.Transverse j)),
      IntegrableOn (fun t => u (coordinateLine j z t)) (Icc a b) ∧
      IntegrableOn (fun t => v (coordinateLine j z t)) (Icc a b) ∧
      ∀ ψ : CompactLineTest 𝕜 a b,
        (∫ t in Icc a b, ψ.toTest t * v (coordinateLine j z t) +
          deriv ψ.toTest t * u (coordinateLine j z t)) = 0 := by
  apply ae_on_set_of_locally_ae
  intro z hz
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp (lineTube U j a b).isOpen z hz
  let V : Opens (ExpandedFA.Sobolev.Lines.Transverse j) :=
    ⟨Metric.ball z (ε/2), Metric.isOpen_ball⟩
  have hVc : IsCompact (closure (V : Set (ExpandedFA.Sobolev.Lines.Transverse j))) :=
    (isCompact_closedBall z (ε/2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hVU : closure (V : Set (ExpandedFA.Sobolev.Lines.Transverse j)) ⊆ lineTube U j a b :=
    Metric.closure_ball_subset_closedBall.trans
      ((Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεV)
  have hl {w : Domain d → 𝕜} (hw : LocallyIntegrableOn w U volume) :
      Integrable (fun p : ExpandedFA.Sobolev.Lines.Transverse j × ℝ => w (coordinateLine j p.1 p.2))
        ((volume.restrict (V : Set (ExpandedFA.Sobolev.Lines.Transverse j))).prod
          (volume.restrict (Icc a b))) := by
    have h := integrable_coordinate_rectangle hw j _ hVc a b (fun y hy => hVU hy)
    rw [Measure.prod_restrict] at h ⊢
    exact h.mono_measure (Measure.restrict_mono (Set.prod_mono subset_closure Subset.rfl) le_rfl)
  have hu' := hl hu
  have hv' := hl hv
  refine ⟨V, Metric.mem_ball_self (by linarith), ?_⟩
  have hid := ae_line_identity_of_tensor_tests V a b
    (fun p => u (coordinateLine j p.1 p.2))
    (fun p => v (coordinateLine j p.1 p.2)) hu' hv' ?_
  · filter_upwards [hu'.prod_right_ae, hv'.prod_right_ae, hid] with y hyu hyv hyid
    exact ⟨hyu, hyv, hyid⟩
  intro ψ η hη hcη hsη
  have hsupport : ∀ y ∈ tsupport η, ∀ t ∈ tsupport ψ.toTest, coordinateLine j y t ∈ U :=
    fun y hy t ht => hVU (subset_closure (hsη hy)) t (ψ.support_subset ht)
  let φ : TestFunction U 𝕜 ⊤ :=
    tensorTest j η hη hcη ψ.toTest ψ.toTest.contDiff ψ.toTest.hasCompactSupport hsupport
  have h₁ : Integrable (fun x => φ x * v x) volume :=
    φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hv
  have h₂ : Integrable (fun x => testPartialCLM [j] φ x * u x) volume :=
    (testPartialCLM [j] φ).integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hu
  have hi := h₁.add h₂
  have he : (∫ x, φ x * v x + testPartialCLM [j] φ x * u x) = 0 := by
    rw [integral_add h₁ h₂]
    exact eq_neg_iff_add_eq_zero.mp (hw φ)
  have heLine := (integral_coordinateLines j hi).symm.trans he
  have hp : Integrable (fun p : ExpandedFA.Sobolev.Lines.Transverse j × ℝ =>
      η p.1 • (ψ.toTest p.2 * v (coordinateLine j p.1 p.2) +
        deriv ψ.toTest p.2 * u (coordinateLine j p.1 p.2))) volume := by
    simpa only [φ, tensorTest_apply, tensorTest_partial,
      transverseProjection_coordinateLine, coordinateLine_self, smul_mul_assoc, smul_add, Pi.add_apply]
      using integrable_product_coordinateLines j hi
  rw [Measure.prod_restrict]
  calc
    _ = ∫ p : ExpandedFA.Sobolev.Lines.Transverse j × ℝ,
        η p.1 • (ψ.toTest p.2 * v (coordinateLine j p.1 p.2) +
          deriv ψ.toTest p.2 * u (coordinateLine j p.1 p.2)) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      rintro ⟨y,t⟩ hyt
      by_cases hy : y ∈ (V : Set (ExpandedFA.Sobolev.Lines.Transverse j))
      · have ht : t ∉ Icc a b := fun ht => hyt ⟨hy,ht⟩
        have hψt : t ∉ tsupport ψ.toTest := fun h => ht (ψ.support_subset h)
        simp only [image_eq_zero_of_notMem_tsupport hψt, deriv_of_notMem_tsupport hψt,
          zero_mul, add_zero, smul_zero]
      · simp only [image_eq_zero_of_notMem_tsupport (fun h => hy (hsη h)), zero_smul]
    _ = 0 := by
      rw [Measure.volume_eq_prod] at hp ⊢
      rw [integral_prod _ hp]
      simpa only [φ, tensorTest_apply, tensorTest_partial,
        transverseProjection_coordinateLine, coordinateLine_self, smul_mul_assoc, smul_add, Pi.add_apply] using heLine

/-- A one-dimensional representative on the interior of a single integrable
segment. Zero extension is used only for data integrable on this segment. -/
theorem representative_on_segment {𝕜 : Type} [RCLike 𝕜]
    (a b : ℝ) (u v : ℝ → 𝕜)
    (hu : IntegrableOn u (Icc a b)) (hv : IntegrableOn v (Icc a b))
    (hw : ∀ ψ : CompactLineTest 𝕜 a b,
      (∫ t in Icc a b, ψ.toTest t * v t + deriv ψ.toTest t * u t) = 0) :
    ∃ f : ℝ → 𝕜, u =ᵐ[volume.restrict (Ioo a b)] f ∧
      LocallyAbsolutelyContinuousOn f (Ioo a b) ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (v t) t := by
  let u' := (Icc a b).indicator u
  let v' := (Icc a b).indicator v
  have hui : Integrable u' volume := (integrable_indicator_iff measurableSet_Icc).mpr hu
  have hvi : Integrable v' volume := (integrable_indicator_iff measurableSet_Icc).mpr hv
  have hw' : ∀ ψ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, ψ t • v' t) = -(∫ t, deriv ψ t • u' t) := by
    intro ψ hψ hcψ hsψ
    let ψk : ℝ → 𝕜 := fun t => (ψ t : 𝕜)
    have hk : ContDiff ℝ (↑(⊤ : ℕ∞)) ψk :=
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hψ
    have hck : HasCompactSupport ψk := hcψ.comp_left (by simp)
    have hsk : tsupport ψk ⊆ Icc a b :=
      (tsupport_comp_subset (g := fun t : ℝ => (t : 𝕜)) (by simp) ψ).trans
        (hsψ.trans Ioo_subset_Icc_self)
    let φ : CompactLineTest 𝕜 a b := ⟨⟨ψk, hk, hck, subset_univ _⟩, hsk⟩
    have hdk (t : ℝ) : deriv ψk t = ((deriv ψ t : ℝ) : 𝕜) :=
      ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt t
        (hψ.differentiable (by simp) t).hasDerivAt).deriv
    have he := hw φ
    change (∫ t in Icc a b, (ψ t : 𝕜) * v t + deriv ψk t * u t) = 0 at he
    simp_rw [hdk, ← RCLike.real_smul_eq_coe_mul] at he
    have h₁ : Integrable (fun t => ψ t • v' t) volume :=
      hvi.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hcψ
    have h₂ : Integrable (fun t => deriv ψ t • u' t) volume :=
      hui.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (hψ.continuous_deriv (by simp)) hcψ.deriv
    apply eq_neg_iff_add_eq_zero.mpr
    rw [← integral_add h₁ h₂]
    have hs : (∫ t in Icc a b, ψ t • v' t + deriv ψ t • u' t) =
        ∫ t, ψ t • v' t + deriv ψ t • u' t := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      simp only [u', v', indicator_of_notMem ht, smul_zero, add_zero]
    rw [← hs]
    calc
      _ = ∫ t in Icc a b, ψ t • v t + deriv ψ t • u t := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        simp only [u', v', indicator_of_mem ht]
      _ = 0 := he
  obtain ⟨f, hrep, hac, hd⟩ := exists_locallyAC_of_integral_deriv isOpen_Ioo
    hui.locallyIntegrable hvi.locallyIntegrable (u := u') (g := v') hw'
  refine ⟨f, ?_, hac, ?_⟩
  · filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with t ht hti
    simpa only [u', indicator_of_mem (Ioo_subset_Icc_self hti)] using ht
  · filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t ht hti
    simpa only [v', indicator_of_mem (Ioo_subset_Icc_self hti)] using ht

/-- Every compact interval in an open component fits strictly inside a rational
closed interval in that component. -/
theorem rational_enclosure {U : Set ℝ} (hU : IsOpen U) {a b : ℝ}
    (habU : uIcc a b ⊆ U) : ∃ l r : ℚ,
      (l : ℝ) < r ∧ Icc (l : ℝ) (r : ℝ) ⊆ U ∧ uIcc a b ⊆ Ioo (l : ℝ) (r : ℝ) := by
  let C := connectedComponentIn U a
  have hCo : IsOpen C := hU.connectedComponentIn
  have hCc : OrdConnected C := isPreconnected_connectedComponentIn.ordConnected
  have hKC : uIcc a b ⊆ C :=
    isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc habU
  have hCn : C.Nonempty := ⟨a, hKC left_mem_uIcc⟩
  obtain ⟨x,hx,y,hy,hKxy⟩ := ExpandedFA.Sobolev.OneDimensional.compact_interval_enclosure hCo hCc hCn
    isCompact_uIcc hKC
  obtain ⟨m,n,hxmn,hmnC⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hCo.mem_nhds hx)
  obtain ⟨l,hml,hlx⟩ := exists_rat_btwn hxmn.1
  obtain ⟨m',n',hymn,hmnC'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hCo.mem_nhds hy)
  obtain ⟨r,hyr,hrn⟩ := exists_rat_btwn hymn.2
  have hlC : (l : ℝ) ∈ C := hmnC ⟨hml, hlx.trans hxmn.2⟩
  have hrC : (r : ℝ) ∈ C := hmnC' ⟨hymn.1.trans hyr, hrn⟩
  refine ⟨l, r, ?_, (hCc.out hlC hrC).trans (connectedComponentIn_subset U a), ?_⟩
  · exact hlx.trans ((hKxy left_mem_uIcc).1.trans
      ((hKxy left_mem_uIcc).2.trans hyr))
  · intro t ht
    exact ⟨hlx.trans (hKxy ht).1, (hKxy ht).2.trans hyr⟩

/-- Rational segment identities determine a continuous representative on an
arbitrary open subset of the line. Overlap uniqueness patches the choices. -/
theorem representative_of_segment_data {𝕜 : Type} [RCLike 𝕜]
    {U : Set ℝ} (hU : IsOpen U) (u v : ℝ → 𝕜)
    (hdata : ∀ a b : ℚ, Icc (a : ℝ) (b : ℝ) ⊆ U →
      IntegrableOn u (Icc (a : ℝ) (b : ℝ)) ∧
      IntegrableOn v (Icc (a : ℝ) (b : ℝ)) ∧
      ∀ ψ : CompactLineTest 𝕜 (a : ℝ) (b : ℝ),
        (∫ t in Icc (a : ℝ) (b : ℝ), ψ.toTest t * v t + deriv ψ.toTest t * u t) = 0) :
    ∃ f : ℝ → 𝕜, u =ᵐ[volume.restrict U] f ∧
      LocallyAbsolutelyContinuousOn f U ∧
      ∀ᵐ t ∂volume.restrict U, HasDerivAt f (v t) t := by
  classical
  let ι := {q : ℚ × ℚ // (q.1 : ℝ) < q.2 ∧ Icc (q.1 : ℝ) (q.2 : ℝ) ⊆ U}
  let V (q : ι) : Set ℝ := Ioo (q.val.1 : ℝ) (q.val.2 : ℝ)
  have hsub (q : ι) : V q ⊆ U := Ioo_subset_Icc_self.trans q.property.2
  have hex (q : ι) : ∃ f : ℝ → 𝕜, u =ᵐ[volume.restrict (V q)] f ∧
      LocallyAbsolutelyContinuousOn f (V q) ∧
      ∀ᵐ t ∂volume.restrict (V q), HasDerivAt f (v t) t := by
    have hd := hdata q.val.1 q.val.2 q.property.2
    exact representative_on_segment _ _ u v hd.1 hd.2.1 hd.2.2
  choose f hrep hac hd using hex
  have hcov (x : ℝ) (hx : x ∈ U) : ∃ q : ι, x ∈ V q := by
    obtain ⟨a,b,hab,habU,hxab⟩ := rational_enclosure hU (a := x) (b := x)
      (by simpa only [uIcc_self, singleton_subset_iff] using hx)
    exact ⟨⟨(a,b),hab,habU⟩, hxab left_mem_uIcc⟩
  have hcover : U = ⋃ q : ι, V q := by
    ext x
    simp only [mem_iUnion]
    exact ⟨hcov x, fun ⟨q,hq⟩ => hsub q hq⟩
  have hpairs (q r : ι) : EqOn (f q) (f r) (V q ∩ V r) := by
    have hq : u =ᵐ[volume.restrict (V q ∩ V r)] f q :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hrep q)
    have hr : u =ᵐ[volume.restrict (V q ∩ V r)] f r :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hrep r)
    exact Measure.eqOn_open_of_ae_eq (hq.symm.trans hr) (isOpen_Ioo.inter isOpen_Ioo)
      ((hac q).continuousOn isOpen_Ioo |>.mono inter_subset_left)
      ((hac r).continuousOn isOpen_Ioo |>.mono inter_subset_right)
  let F : ℝ → 𝕜 := fun x => if hx : x ∈ U then f (Classical.choose (hcov x hx)) x else 0
  have hFeq (q : ι) : EqOn F (f q) (V q) := by
    intro x hx
    have hxU := hsub q hx
    dsimp only [F]
    rw [dite_eq_left hxU]
    exact hpairs (Classical.choose (hcov x hxU)) q
      ⟨Classical.choose_spec (hcov x hxU), hx⟩
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [hcover]
    apply (ae_restrict_iUnion_iff _ _).mpr
    intro q
    filter_upwards [hrep q, ae_restrict_mem measurableSet_Ioo] with t ht hti
    exact ht.trans (hFeq q hti).symm
  · intro a b habU
    obtain ⟨l,r,hlr,hlrU,hab⟩ := rational_enclosure hU habU
    let q : ι := ⟨(l,r), hlr, hlrU⟩
    exact (hac q a b hab).congr (fun t ht => (hFeq q (hab ht)).symm)
  · rw [hcover]
    apply (ae_restrict_iUnion_iff _ _).mpr
    intro q
    filter_upwards [hd q, ae_restrict_mem measurableSet_Ioo] with t ht hti
    apply ht.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hti] with s hs
    exact hFeq q hs

/-- Fixed-axis slicing with only local L¹ hypotheses on the open set. -/
theorem ae_line_representatives_of_weak_tests {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U : Opens (Fin d → ℝ)) (j : Fin d) (u v : (Fin d → ℝ) → 𝕜)
    (hu : LocallyIntegrableOn u U volume) (hv : LocallyIntegrableOn v U volume)
    (hw : ∀ φ : TestFunction U 𝕜 ⊤,
      (∫ x, φ x * v x) = -(∫ x, testPartialCLM [j] φ x * u x)) :
    ∀ᵐ z : ExpandedFA.Sobolev.Lines.Transverse j ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => u (coordinateLine j z t)) =ᵐ[volume.restrict
        (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ)] f ∧
      LocallyAbsolutelyContinuousOn f (ExpandedFA.Sobolev.Lines.fiber U j z) ∧
      ∀ᵐ t ∂volume.restrict (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ),
        HasDerivAt f (v (coordinateLine j z t)) t := by
  have hall : ∀ᵐ z : ExpandedFA.Sobolev.Lines.Transverse j ∂volume, ∀ a b : ℚ,
      z ∈ lineTube U j (a : ℝ) (b : ℝ) →
      IntegrableOn (fun t => u (coordinateLine j z t)) (Icc (a : ℝ) (b : ℝ)) ∧
      IntegrableOn (fun t => v (coordinateLine j z t)) (Icc (a : ℝ) (b : ℝ)) ∧
      ∀ ψ : CompactLineTest 𝕜 (a : ℝ) (b : ℝ),
        (∫ t in Icc (a : ℝ) (b : ℝ), ψ.toTest t * v (coordinateLine j z t) +
          deriv ψ.toTest t * u (coordinateLine j z t)) = 0 := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    exact (ae_restrict_iff' (lineTube U j (a : ℝ) (b : ℝ)).isOpen.measurableSet).mp
      (ae_segment_data U j u v hu hv hw a b)
  filter_upwards [hall] with z hz
  exact representative_of_segment_data (ExpandedFA.Sobolev.Lines.fiber U j z).isOpen
    (fun t => u (coordinateLine j z t)) (fun t => v (coordinateLine j z t)) hz


/-- Assemble one ambient representative from the continuous fiber choices,
using local joint a.e. measurability before applying Fubini. -/
theorem representative_of_line_representatives {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U : Opens (Fin d → ℝ)) (j : Fin d) (u v : (Fin d → ℝ) → 𝕜)
    (hu : LocallyIntegrableOn u U volume) (hv : LocallyIntegrableOn v U volume)
    (hs : ∀ᵐ z : ExpandedFA.Sobolev.Lines.Transverse j ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => u (coordinateLine j z t)) =ᵐ[volume.restrict
        (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ)] f ∧
      LocallyAbsolutelyContinuousOn f (ExpandedFA.Sobolev.Lines.fiber U j z) ∧
      ∀ᵐ t ∂volume.restrict (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ),
        HasDerivAt f (v (coordinateLine j z t)) t) :
    ∃ F : (Fin d → ℝ) → 𝕜, u =ᵐ[volume.restrict (U : Set (Fin d → ℝ))] F ∧
      ∀ᵐ z : ExpandedFA.Sobolev.Lines.Transverse j ∂volume,
        LocallyAbsolutelyContinuousOn (fun t => F (coordinateLine j z t))
          (ExpandedFA.Sobolev.Lines.fiber U j z) ∧
        ∀ᵐ t ∂volume.restrict (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ),
          HasDerivAt (fun s => F (coordinateLine j z s)) (v (coordinateLine j z t)) t := by
  classical
  let Good (z : ExpandedFA.Sobolev.Lines.Transverse j) : Prop := ∃ f : ℝ → 𝕜,
    (fun t => u (coordinateLine j z t)) =ᵐ[volume.restrict (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ)] f ∧
      LocallyAbsolutelyContinuousOn f (ExpandedFA.Sobolev.Lines.fiber U j z) ∧
      ∀ᵐ t ∂volume.restrict (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ),
        HasDerivAt f (v (coordinateLine j z t)) t
  let f (z : ExpandedFA.Sobolev.Lines.Transverse j) : ℝ → 𝕜 :=
    if hz : Good z then Classical.choose hz else 0
  have hf : ∀ᵐ z : ExpandedFA.Sobolev.Lines.Transverse j ∂volume,
      (fun t => u (coordinateLine j z t)) =ᵐ[volume.restrict (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ)] f z ∧
      LocallyAbsolutelyContinuousOn (f z) (ExpandedFA.Sobolev.Lines.fiber U j z) ∧
      ∀ᵐ t ∂volume.restrict (ExpandedFA.Sobolev.Lines.fiber U j z : Set ℝ),
        HasDerivAt (f z) (v (coordinateLine j z t)) t := by
    filter_upwards [hs] with z hz
    have hz' : Good z := hz
    dsimp only [f]
    rw [dite_eq_left hz']
    exact Classical.choose_spec hz'
  let F : Domain d → 𝕜 := fun x => f (transverseProjection j x) (x j)
  have hF (z : ExpandedFA.Sobolev.Lines.Transverse j) (t : ℝ) :
      F (coordinateLine j z t) = f z t := by
    simp only [F, transverseProjection_coordinateLine, coordinateLine_self]
  refine ⟨F, ?_, ?_⟩
  · apply ae_on_set_of_locally_ae
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
    let r := ε / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hclosed : Metric.closedBall x r ⊆ (U : Set (Domain d)) :=
      (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hεU
    let K := Metric.closedBall (transverseProjection j x) r
    let a := x j - r
    let b := x j + r
    have hab : a < b := by dsimp [a,b]; linarith
    have hrect (z) (hz : z ∈ K) (t) (ht : t ∈ Icc a b) : coordinateLine j z t ∈ U := by
      apply hclosed
      apply (coordinateLine_mem_closedBall_iff j z t x r).mpr
      exact ⟨by simpa only [Real.closedBall_eq_Icc] using ht, hz⟩
    have heq := ae_eq_on_rectangle hu j f (hf.mono fun z hz => ⟨hz.1, hz.2.1⟩)
      K (isCompact_closedBall _ _) a b hab hrect
    let e : ExpandedFA.Sobolev.Lines.Transverse j × ℝ ≃ᵐ Domain d :=
      MeasurableEquiv.prodComm.trans (coordinateEquiv j).symm
    have hem : MeasurePreserving e volume volume :=
      ((coordinateEquiv_measurePreserving j).symm (coordinateEquiv j)).comp
        Measure.measurePreserving_swap
    have heq' : ∀ᵐ p ∂volume.restrict (K ×ˢ Icc a b), u (e p) = F (e p) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      filter_upwards [heq] with p hp
      change u ((coordinateEquiv j).symm (p.2, p.1)) =
        F ((coordinateEquiv j).symm (p.2, p.1))
      rw [coordinateEquiv_symm_apply, hF]
      exact hp
    have ha := (ae_restrict_iff' ((isCompact_closedBall _ _).measurableSet.prod
      measurableSet_Icc)).mp heq'
    have hb := (hem.symm e).quasiMeasurePreserving.ae ha
    refine ⟨⟨Metric.ball x r, Metric.isOpen_ball⟩, Metric.mem_ball_self hr, ?_⟩
    apply (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
    filter_upwards [hb] with y hy' hy
    apply (e.apply_symm_apply y ▸ hy')
    have hyball : coordinateLine j (transverseProjection j y) (y j) ∈ Metric.closedBall x r := by
      have he : coordinateLine j (transverseProjection j y) (y j) = y := by
        ext k
        by_cases hk : k = j
        · subst k; exact coordinateLine_self j _ _
        · simp [coordinateLine, hk, ExpandedFA.Sobolev.Lines.transverseProjection]
      rw [he]
      exact Metric.ball_subset_closedBall hy
    have h := (coordinateLine_mem_closedBall_iff j _ _ x r).mp hyball
    change (transverseProjection j y) ∈ K ∧ y j ∈ Icc a b
    exact ⟨h.2, by simpa only [Real.closedBall_eq_Icc] using h.1⟩
  · simpa only [hF] using hf.mono (fun z hz => hz.2)


end Forward

/-- Transport the local L¹ slicing and representative assembly to Euclidean coordinates. -/
theorem weak_to_representative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (j : Fin d) {u v : Space d → 𝕜}
    (hu : LocallyIntegrableOn u Ω volume) (hv : LocallyIntegrableOn v Ω volume)
    (hw : distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v) :
    HasRepresentative Ω j u v := by
  let U := coordinateDomain Ω
  let up := u ∘ (coordinates d).symm
  let vp := v ∘ (coordinates d).symm
  have hup : LocallyIntegrableOn up U volume := locallyIntegrable_coordinates hu
  have hvp : LocallyIntegrableOn vp U volume := locallyIntegrable_coordinates hv
  have ht := Forward.ae_line_representatives_of_weak_tests U j up vp hup hvp
    (weak_identity_coordinates j hu hv hw)
  obtain ⟨F, hFrep, hF⟩ := Forward.representative_of_line_representatives U j up vp hup hvp ht
  refine ⟨fun x => F (coordinates d x), ?_, ?_⟩
  · have ha := (ae_restrict_iff' U.isOpen.measurableSet).mp hFrep
    have hb := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae ha
    exact (ae_restrict_iff' Ω.isOpen.measurableSet).mpr hb
  · exact hF

end P102.U4.ACL

namespace P102.U4

/-- The fully proved converse direction of U4-05. -/
theorem acl_converse : ACLExpected.Converse := by
  intro d _hd 𝕜 _ Ω j u v hu hv hf
  exact ACL.representative_to_weak j hu hv hf

/-- U4-05, the complete local L¹ line-representative characterization. -/
theorem acl_characterization : ACLExpected.Characterization := by
  intro d _hd 𝕜 _ Ω j u v hu hv
  exact ⟨ACL.weak_to_representative j hu hv, ACL.representative_to_weak j hu hv⟩

/-- Dimension one is a genuine no-transverse-variable specialization. -/
theorem acl_dimensionOne : ACLExpected.DimensionOne := by
  intro 𝕜 _ Ω u v hu hv
  exact (acl_characterization 1 (by decide) 𝕜 Ω 0 u v hu hv).trans
    (ACL.representative_dimensionOne_iff Ω u v)

end P102.U4

