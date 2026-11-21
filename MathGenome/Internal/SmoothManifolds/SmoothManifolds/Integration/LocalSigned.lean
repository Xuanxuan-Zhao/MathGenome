import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalSigned
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Equivalences
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.LocalIntegrationResults
open ModelData AtlasData TangentData TangentBundleData ExteriorData FormPullbackData
  OrientationData LocalIntegrationData Set MeasureTheory Filter Module
universe u

/-- The algebraic sign identity used with Lebesgue substitution. No constancy
of the signs on a connected component is needed. -/
theorem signed_coefficient_identity (sx sy : ℝ) (j b : ℝ)
    (h : sy = sx * (SignType.sign j : ℝ)) :
    sx * (b * j) = |j| * (sy * b) := by
  rw [h]
  calc
    sx * (b * j) = sx * b * ((SignType.sign j : ℝ) * |j|) := by rw [sign_mul_abs]; ring
    _ = |j| * (sx * (SignType.sign j : ℝ) * b) := by ring

/-- A signed version of Mathlib's measurable-set Lebesgue substitution theorem.
The derivative and signs can vary pointwise, and the source need not be open.
This is applicable to half-space domains with their true boundary included. -/
theorem signed_measurable_substitution {n : ℕ} {U : Set (Euclidean n)}
    (hU : MeasurableSet U) (ψ : Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (hJ : ∀ x ∈ U, HasFDerivWithinAt ψ (J x) U x) (hψ : InjOn ψ U)
    (a b sx sy : Euclidean n → ℝ)
    (hab : ∀ x ∈ U, a x = b (ψ x) * (J x).det)
    (hs : ∀ x ∈ U, sy (ψ x) = sx x * (SignType.sign (J x).det : ℝ)) :
    (∫ y in ψ '' U, sy y * b y) = ∫ x in U, sx x * a x := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU hJ hψ]
  apply setIntegral_congr_fun hU
  intro x hx
  change |(J x).det| * (sy (ψ x) * b (ψ x)) = sx x * a x
  rw [hab x hx]
  exact (signed_coefficient_identity _ _ _ _ (hs x hx)).symm

/-- Evaluation on one coordinate frame is evaluation on the other times the
signed determinant. This statement is algebraic, so includes boundary points. -/
theorem coefficient_transition_proof :
    Specs.SmoothManifolds.Integration.LocalSigned.coefficient_transitionType.{u} := by
  intro n a M _ S K c d hc hd p ω
  let B : Basis (Fin n) ℝ (TangentSpace S p.val) :=
    (Pi.basisFun ℝ (Fin n)).map (K.equiv d hd p.val p.property.2).symm
  let A := evaluate (TangentSpace S p.val) n (ω p.val)
  have hb (i : Fin n) : B i =
      CovectorData.coordinateVector K d hd p.val p.property.2 i := by
    simp [B, CovectorData.coordinateVector, Pi.basisFun_apply]
  have hdet : B.det (CovectorData.coordinateVector K c hc p.val p.property.1) =
      transitionDeterminant K c d hc hd p := by
    rw [Basis.det_apply, transitionDeterminant, ← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
    congr 1
  have hA := AlternatingMap.eq_smul_basis_det (R := ℝ) (M := TangentSpace S p.val)
    B (evaluate (TangentSpace S p.val) n (ω p.val))
  have hh := congrArg (fun f : AlternatingMap ℝ (TangentSpace S p.val) ℝ (Fin n) =>
    f (CovectorData.coordinateVector K c hc p.val p.property.1)) hA
  simpa only [smul_apply, smul_eq_mul, hdet, topCoefficient, ← funext hb]
    using hh

/-- The values at points of the chart are the original signed coefficients. -/
theorem signedCoefficient_at {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (s : SignedCharts S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S n) (p : c.source) :
    signedCoordinateCoefficient s K c hc ω (c p.val).val =
      signValue (s.sign c hc p) * topCoefficient K c hc p.val p.property ω := by
  simp [signedCoordinateCoefficient, extendModel, modelSignedCoefficient,
    (c p.val).property, c.map_source p.property, c.left_inv p.property]

/-- A nonzero zero-extended coefficient comes from a nonzero section value. -/
theorem signedCoefficient_nonzero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (s : SignedCharts S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S n) (x : Euclidean n)
    (hx : signedCoordinateCoefficient s K c hc ω x ≠ 0) :
    ∃ p ∈ sectionSupport ω, p ∈ c.source ∧ (c p).val = x := by
  unfold signedCoordinateCoefficient extendModel at hx
  split_ifs at hx with hm
  · unfold modelSignedCoefficient at hx
    split_ifs at hx with ht
    · refine ⟨c.symm ⟨x, hm⟩, ?_, c.map_target ht, ?_⟩
      · apply subset_closure
        intro hz
        apply hx
        simp [topCoefficient, hz]
      · exact congrArg Subtype.val (c.right_inv ht)
    · exact (hx rfl).elim
  · exact (hx rfl).elim

/-- Compact containment gives a compact ambient set containing all nonzero
coordinate values, even when the support meets the true boundary. -/
theorem signedCoefficient_compact_container {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (s : SignedCharts S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : CompactTopForm S) (hω : sectionSupport ω.field ⊆ c.source) :
    IsCompact ((fun p : M => (c p).val) '' sectionSupport ω.field) ∧
      Function.support (signedCoordinateCoefficient s K c hc ω.field) ⊆
        (fun p : M => (c p).val) '' sectionSupport ω.field := by
  refine ⟨ω.compact_support.image_of_continuousOn
    (continuous_subtype_val.comp_continuousOn (c.continuousOn.mono hω)), ?_⟩
  intro x hx
  obtain ⟨p, hp, hpc, heq⟩ := signedCoefficient_nonzero s K c hc ω.field x hx
  exact ⟨p, hp, heq⟩

/-- Compact support leaves a neighborhood of every artificial edge on which
zero extension is identically zero in the entire ambient space. -/
theorem artificial_edges_proof :
    Specs.SmoothManifolds.Integration.LocalSigned.artificial_edgesType.{u} := by
  intro n a M _ S s K c hc ω hω x hx
  obtain ⟨hC, hsub⟩ := signedCoefficient_compact_container s K c hc ω hω
  refine ⟨((fun p : M => (c p).val) '' sectionSupport ω.field)ᶜ,
    hC.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨p, hp, hpx⟩
    have he : c p = x := Subtype.ext hpx
    exact hx (he ▸ c.map_source (hω hp))
  · intro y hy
    by_contra hn
    exact hy (hsub hn)

/-- The ordinary constant chart-sign formula is a specialization of the
pointwise signed definition. -/
theorem coordinate_formula_proof :
    Specs.SmoothManifolds.Integration.LocalSigned.coordinate_formulaType.{u} := by
  intro n a M _ S s K c hc ω ε hε
  have hf : signedCoordinateCoefficient s K c hc ω =
      fun x => signValue ε * coordinateCoefficient K c hc ω x := by
    funext x
    unfold signedCoordinateCoefficient coordinateCoefficient extendModel
    split_ifs with hm
    · unfold modelSignedCoefficient modelCoefficient
      split_ifs with ht
      · rw [hε]
      · simp
    · simp
  rw [coordinateIntegral, hf, integral_const_mul]

/-- Nullness of the coordinate face, for the actual last-coordinate model. -/
theorem halfSpaceFace_null (n : ℕ) : volume (halfSpaceFace (n+1)) = 0 := by
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin (n+1) => volume) (Fin.last n) 0

theorem boundary_null_proof :
    Specs.SmoothManifolds.Integration.LocalSigned.boundary_nullType.{u} := by
  intro n M _ S s K c hc ω
  refine ⟨halfSpaceFace_null n, ?_⟩
  let f := signedCoordinateCoefficient s K c hc ω
  have hae : ∀ᵐ x : Euclidean (n+1), x (Fin.last n) ≠ 0 := by
    simpa only [volume_pi] using
      (MeasureTheory.Measure.ae_eval_ne (fun _ : Fin (n+1) => volume) (Fin.last n) 0)
  change ∫ x, f x = ∫ x in {x : Euclidean (n+1) | 0 < x (Fin.last n)}, f x
  rw [← integral_indicator (isOpen_lt continuous_const (continuous_apply (Fin.last n))).measurableSet]
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  by_cases hp : 0 < x (Fin.last n)
  · simp [hp]
  · have hm : x ∉ modelSet (n+1) .halfSpace := by
      change ¬ 0 ≤ x (Fin.last n)
      exact not_le.mpr (lt_of_le_of_ne (le_of_not_gt hp) hx)
    simp [f, signedCoordinateCoefficient, extendModel, hm, hp]

/-- A zero-dimensional chart domain has at most one point. -/
theorem zero_chart_subsingleton {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (c : ModelChart 0 a M) : Subsingleton c.source := by
  refine ⟨fun p q => Subtype.ext (c.injOn p.property q.property ?_)⟩
  exact Subsingleton.elim _ _

/-- Discreteness is derived from the chart cover, not assumed on a zero-manifold. -/
theorem zero_manifold_discrete {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) : DiscreteTopology M := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  have hsingle : c.source = {p} := by
    ext q
    constructor
    · intro hq
      haveI := zero_chart_subsingleton c
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val
        (Subsingleton.elim (⟨q, hq⟩ : c.source) ⟨p, hp⟩))
    · rintro rfl
      exact hp
  rw [← hsingle]
  exact c.open_source

theorem zero_finite_sum_proof :
    Specs.SmoothManifolds.Integration.LocalSigned.zero_finite_sumType.{u} := by
  intro a M _ S o ω
  haveI := zero_manifold_discrete S
  let h := ω.compact_support.finite_of_discrete
  refine ⟨h, ?_⟩
  change (∑ᶠ p, zeroSign o p * zeroCoefficient ω.field p) =
    ∑ p ∈ h.toFinset, zeroSign o p * zeroCoefficient ω.field p
  apply finsum_eq_sum_of_support_subset
  intro p hp
  apply h.mem_toFinset.mpr
  apply subset_closure
  intro hz
  apply hp
  simp [zeroCoefficient, hz]

/-- Continuity is required only in the relative model, including its boundary. -/
theorem modelSignedCoefficient_continuous {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (s : SignedCharts S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : CompactTopForm S) (hω : sectionSupport ω.field ⊆ c.source) :
    Continuous (modelSignedCoefficient s K c hc ω.field) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ c.target
  · let f : c.source → ℝ := fun p =>
      signValue (s.sign c hc p) * topCoefficient K c hc p.val p.property ω.field
    have hf : Continuous f :=
      ((s.locallyConstant c hc).comp signValue).continuous.mul (ω.continuous K c hc)
    have hcont : ContinuousOn (modelSignedCoefficient s K c hc ω.field) c.target := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      convert hf.comp c.toHomeomorphSourceTarget.symm.continuous using 1
      funext y
      simp only [Set.domRestrict_apply, modelSignedCoefficient, y.property, ↓reduceDIte,
        Function.comp_apply]
      change f ⟨c.symm y.val, c.map_target y.property⟩ = f (c.toHomeomorphSourceTarget.symm y)
      congr 1

    exact hcont.continuousAt (c.open_target.mem_nhds hx)
  · obtain ⟨U, hU, hxU, hzero⟩ := artificial_edges_proof S s K c hc ω hω x hx
    have he : modelSignedCoefficient s K c hc ω.field =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds hxU] with y hy
      have hh := hzero y.val hy
      simpa [signedCoordinateCoefficient, extendModel, y.property] using hh
    exact continuousAt_const.congr_of_eventuallyEq he

theorem integrable_proof : Specs.SmoothManifolds.Integration.LocalSigned.integrableType.{u} := by
  intro n a M _ S s K c hc ω hω
  obtain ⟨hC, hsub⟩ := signedCoefficient_compact_container s K c hc ω hω
  apply (integrableOn_iff_integrable_of_support_subset hsub).mp
  apply ContinuousOn.integrableOn_compact hC
  apply continuousOn_iff_continuous_domRestrict.mpr
  let f : ((fun p : M => (c p).val) '' sectionSupport ω.field) → ModelSpace n a :=
    fun x => ⟨x.val, by obtain ⟨p, hp, heq⟩ := x.property; rw [← heq]; exact (c p).property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hh := (modelSignedCoefficient_continuous s K c hc ω hω).comp hf
  convert hh using 1
  funext x
  change extendModel (modelSignedCoefficient s K c hc ω.field) x.val =
    modelSignedCoefficient s K c hc ω.field (f x)
  have hm : x.val ∈ modelSet n a := (f x).property
  rw [extendModel, dite_eq_left hm]

/-- Ambient coordinate domain of a relatively open model domain. -/
def ambientDomain {n : ℕ} {a : ModelKind} (U : Set (ModelSpace n a)) :
    Set (Euclidean n) := Subtype.val '' U

/-- Total ambient representative. Only its values on the source are used. -/
def ambientTransition {n : ℕ} {a : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n a)) (x : Euclidean n) :
    Euclidean n :=
  if hx : x ∈ modelSet n a then (e ⟨x, hx⟩).val else 0

theorem ambientTransition_at {n : ℕ} {a : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n a)) (x : ModelSpace n a) :
    ambientTransition e x.val = (e x).val := by
  simp [ambientTransition, x.property]

theorem modelSet_closed (n : ℕ) (a : ModelKind) : IsClosed (modelSet n a) := by
  cases a with
  | euclidean => exact isClosed_univ
  | halfSpace =>
    cases n with
    | zero => exact isClosed_univ
    | succ n => exact isClosed_le continuous_const (continuous_apply (Fin.last n))

theorem ambientDomain_measurable {n : ℕ} {a : ModelKind}
    {U : Set (ModelSpace n a)} (hU : IsOpen U) : MeasurableSet (ambientDomain U) := by
  obtain ⟨V, hV, heq⟩ := hU.image_val
  change MeasurableSet (Subtype.val '' U)
  rw [heq]
  exact hV.measurableSet.inter (modelSet_closed n a).measurableSet

theorem ambientTransition_injective {n : ℕ} {a : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n a)) :
    InjOn (ambientTransition e) (ambientDomain e.source) := by
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩ h
  rw [ambientTransition_at, ambientTransition_at] at h
  exact congrArg Subtype.val (e.injOn hp hq (Subtype.ext h))

theorem ambientTransition_image {n : ℕ} {a : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n a)) :
    ambientTransition e '' ambientDomain e.source = ambientDomain e.target := by
  ext y
  constructor
  · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    rw [ambientTransition_at]
    exact ⟨e p, e.map_source hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(e.symm q).val, ⟨e.symm q, e.map_target hq, rfl⟩, ?_⟩
    rw [ambientTransition_at, e.right_inv hq]

/-- The local ambient extension differentiates the total representative within
its actual model source, including true boundary points. -/
theorem ambientTransition_hasFDerivWithinAt {n : ℕ} {a : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n a))
    (x : ModelSpace n a) (hx : x ∈ e.source)
    (V : Set (Euclidean n)) (hV : IsOpen V) (hxV : x.val ∈ V)
    (F : Euclidean n → Euclidean n) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V)
    (heq : ∀ y ∈ e.source, y.val ∈ V → F y.val = (e y).val) :
    HasFDerivWithinAt (ambientTransition e) (fderiv ℝ F x.val)
      (ambientDomain e.source) x.val := by
  have hd := ((hF.differentiableOn (by simp) x.val hxV).differentiableAt
    (hV.mem_nhds hxV)).hasFDerivAt.hasFDerivWithinAt (s := ambientDomain e.source)
  refine hd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV)] with y hy hyV
    obtain ⟨z, hz, rfl⟩ := hy
    rw [ambientTransition_at, heq z hz hyV]
  · rw [ambientTransition_at, heq x hx hxV]

theorem ambientTransition_differentiable {n : ℕ} {a : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n a))
    (he : ContDiffOnModel (⊤ : ℕ∞) e e.source) :
    DifferentiableOn ℝ (ambientTransition e) (ambientDomain e.source) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨V, hV, hyV, F, hF, heq⟩ := he y hy
  exact (ambientTransition_hasFDerivWithinAt e y hy V hV hyV F hF heq).differentiableWithinAt

/-- The determinant in the Lebesgue substitution theorem is the determinant
of the original intrinsic tangent-coordinate transition. -/
theorem ambientTransition_det
    (hjac : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source)) :
    (fderivWithin ℝ (ambientTransition (c.symm.trans d))
      (ambientDomain (c.symm.trans d).source) (c p.val).val).det =
        transitionDeterminant K c d hc hd p := by
  let e := c.symm.trans d
  have hp : c p.val ∈ e.source := by
    exact ⟨c.map_source p.property.1, by simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, c.left_inv p.property.1] using p.property.2⟩
  have he := S.smoothStructure.property.1.2 c hc d hd
  obtain ⟨V, hV, hpV, F, hF, heq⟩ := he.1 (c p.val) hp
  have hder := ambientTransition_hasFDerivWithinAt e (c p.val) hp V hV hpV F hF heq
  have huniq := uniqueDiffOn_modelDomain e.open_source
  rw [hder.fderivWithin (huniq _ ⟨c p.val, hp, rfl⟩)]
  apply Eq.symm
  apply hjac S K c d hc hd p V F hV hpV hF
  filter_upwards [c.open_source.mem_nhds p.property.1,
    d.open_source.mem_nhds p.property.2,
    (continuous_subtype_val.continuousAt.comp (c.continuousAt p.property.1)).preimage_mem_nhds
      (hV.mem_nhds hpV)] with q hqc hqd hqV
  have hqe : c q ∈ e.source := by
    exact ⟨c.map_source hqc, by simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, c.left_inv hqc] using hqd⟩
  simpa only [OpenPartialHomeomorph.trans_apply, c.left_inv hqc] using heq (c q) hqe hqV

/-- The coefficient has support in the actual overlap whenever the original
section does. -/
theorem support_in_overlap {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (s : SignedCharts S)
    (K : FiberCoordinates S) (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S n) (hdω : sectionSupport ω ⊆ d.source) :
    Function.support (signedCoordinateCoefficient s K c hc ω) ⊆
      ambientDomain (c.symm.trans d).source := by
  intro x hx
  obtain ⟨p, hp, hpc, rfl⟩ := signedCoefficient_nonzero s K c hc ω x hx
  refine ⟨c p, ⟨c.map_source hpc, ?_⟩, rfl⟩
  simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, c.left_inv hpc] using hdω hp

/-- Substitution for actual chart transitions, without choosing a global
Jacobian sign. It is valid for arbitrary sections for which the integrals
exist in the Bochner convention; compactness is not used in this identity. -/
theorem coordinateIntegral_eq
    (hjac : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (s : SignedCharts S) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (ω : Field S n)
    (hcω : sectionSupport ω ⊆ c.source) (hdω : sectionSupport ω ⊆ d.source) :
    coordinateIntegral s K c hc ω = coordinateIntegral s K d hd ω := by
  let e := c.symm.trans d
  let U := ambientDomain e.source
  let V := ambientDomain e.target
  let ψ := ambientTransition e
  let J := fderivWithin ℝ ψ U
  let f := signedCoordinateCoefficient s K c hc ω
  let g := signedCoordinateCoefficient s K d hd ω
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
      exact ambientTransition_det hjac S K c d hc hd p
    change |(J y.val).det| * signedCoordinateCoefficient s K d hd ω (ψ y.val) =
      signedCoordinateCoefficient s K c hc ω y.val
    rw [hψy, ← hcy, signedCoefficient_at s K d hd ω ⟨p.val, hpd⟩,
      signedCoefficient_at s K c hc ω ⟨p.val, hpc⟩,
      coefficient_transition_proof S K c d hc hd p ω]
    rw [hcy, hdet]
    exact (signed_coefficient_identity _ _ _ _ (s.compatible K c d hc hd p)).symm
  have hsub := integral_image_eq_integral_abs_det_fderiv_smul volume hU hJ
    (ambientTransition_injective e) g
  rw [ambientTransition_image e] at hsub
  have hfU : Function.support f ⊆ U := support_in_overlap s K c d hc ω hdω
  have hgV : Function.support g ⊆ V := by
    have hh := support_in_overlap s K d c hd ω hcω
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

/-- Genuine tangent coordinate systems agree, so the chosen representatives
do not affect coefficient evaluation. -/
theorem topCoefficient_coordinates_eq {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K L : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ c.source) (ω : Field S n) :
    topCoefficient K c hc p hp ω = topCoefficient L c hc p hp ω := by
  have he := TangentBundle.chartCoordinates_unique (K.isCoordinates c hc p hp)
    (L.isCoordinates c hc p hp)
  unfold topCoefficient
  congr 1
  funext j
  unfold CovectorData.coordinateVector
  rw [he]

theorem coordinateIntegral_coordinates_eq {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (s : SignedCharts S)
    (K L : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S n) : coordinateIntegral s K c hc ω = coordinateIntegral s L c hc ω := by
  unfold coordinateIntegral
  congr 1
  funext x
  unfold signedCoordinateCoefficient extendModel
  split_ifs with hm
  · unfold modelSignedCoefficient
    split_ifs with ht
    · rw [topCoefficient_coordinates_eq K L]
    · rfl
  · rfl

/-- Evaluation in exterior degree zero is the canonical scalar. -/
theorem evaluate_zero (V : Type u) [AddCommGroup V] [Module ℝ V]
    (ω : Fiber V 0) (v : Fin 0 → V) :
    evaluate V 0 ω v = exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V) ω := by
  let E := exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)
  let α : Fin 0 → Module.Dual ℝ V := fun i => Fin.elim0 i
  have hω : ω = E ω • exteriorPower.ιMulti ℝ 0 α := by
    apply E.injective
    simp [E]
  calc
    evaluate V 0 ω v = evaluate V 0 (E ω • exteriorPower.ιMulti ℝ 0 α) v := by rw [← hω]
    _ = E ω := by
      rw [map_smul, smul_apply, smul_eq_mul,
        ExteriorAlgebraResults.determinant_normalization V 0 α v]
      simp

theorem topCoefficient_zero {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (K : FiberCoordinates S) (c : ModelChart 0 a M)
    (hc : c ∈ S.smoothStructure.val) (ω : Field S 0) (p : c.source) :
    topCoefficient K c hc p.val p.property ω = zeroCoefficient ω p.val :=
  evaluate_zero _ _ _

/-- A ray cannot contain both a vector and its negative. -/
theorem positive_not_neg {V : Type u} [AddCommGroup V] [Module ℝ V]
    (r : Module.Ray ℝ V) (v : V) (hp : IsPositive r v) : ¬ IsPositive r (-v) := by
  rintro ⟨hn, he⟩
  obtain ⟨hv, hvRay⟩ := hp
  apply Module.Ray.ne_neg_self r
  calc
    r = rayOfNeZero ℝ (-v) hn := he.symm
    _ = -rayOfNeZero ℝ v hv := (neg_rayOfNeZero ℝ v hv).symm
    _ = -r := congrArg Neg.neg hvRay

theorem zeroSign_eq_chartSign {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (o : Orientation S) (s : SignedCharts S)
    (hs : RepresentsSignedCharts o.val s) (K : FiberCoordinates S)
    (c : ModelChart 0 a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    zeroSign o p.val = signValue (s.sign c hc p) := by
  have hcoord : OrientationData.coordinateVector K c hc p =
      (exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1 := by
    apply (exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).injective
    simp [OrientationData.coordinateVector]
  have hp := hs K c hc p
  rw [hcoord] at hp
  cases he : s.sign c hc p with
  | true =>
    have hv : IsPositive (o.val p.val)
        ((exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1) := by
      simpa [he, signValue] using hp
    simp [zeroSign, signValue, hv]
  | false =>
    have hv : IsPositive (o.val p.val)
        (-((exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1)) := by
      rw [he] at hp
      change IsPositive (o.val p.val)
        ((-1 : ℝ) • (exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1) at hp
      have hn : ((-1 : ℝ) • (exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1 :
          DeterminantLine S p.val) = -((exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1) :=
        neg_one_smul (M := DeterminantLine S p.val) ℝ
          ((exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1)
      exact hn ▸ hp
    have hn : ¬ IsPositive (o.val p.val)
        ((exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1) := by
      intro hh
      exact positive_not_neg _ _ hh hv
    simp [zeroSign, signValue, hn]

/-- Lebesgue measure in dimension zero has mass one at its sole point. -/
theorem zero_euclidean_integral (f : Euclidean 0 → ℝ) (x : Euclidean 0) :
    (∫ y, f y) = f x := by
  rw [integral_unique]
  have hvol : (volume : Measure (Euclidean 0)) univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  simp only [measureReal_def, hvol, ENNReal.toReal_one, one_smul]
  exact congrArg f (Subsingleton.elim _ _)

/-- Coordinate integration on a nonempty zero-dimensional chart is signed
evaluation at its unique point. -/
theorem zero_coordinate_evaluation {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S) (s : SignedCharts S)
    (hs : RepresentsSignedCharts o.val s) (K : FiberCoordinates S)
    (c : ModelChart 0 a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S 0)
    (p : c.source) : coordinateIntegral s K c hc ω =
      zeroSign o p.val * zeroCoefficient ω p.val := by
  rw [coordinateIntegral, zero_euclidean_integral _ (c p.val).val,
    signedCoefficient_at, topCoefficient_zero,
    zeroSign_eq_chartSign o s hs K c hc p]

/-- A section supported in a zero-dimensional chart vanishes at every other
point. -/
theorem zero_support_singleton {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (c : ModelChart 0 a M) (ω : Field S 0)
    (hω : sectionSupport ω ⊆ c.source) (p : c.source) :
    ∀ q : M, q ≠ p.val → ω q = 0 := by
  intro q hq
  by_contra hn
  have hqc : q ∈ c.source := hω (subset_closure hn)
  haveI := zero_chart_subsingleton c
  exact hq (congrArg Subtype.val (Subsingleton.elim (⟨q, hqc⟩ : c.source) p))

theorem zero_coordinate_proof : Specs.SmoothManifolds.Integration.LocalSigned.zero_coordinateType.{u} := by
  intro a M _ S o s hs K c hc ω hω
  by_cases hne : c.source.Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hsum : zeroIntegral o ω.field = zeroSign o p * zeroCoefficient ω.field p := by
      unfold zeroIntegral
      apply finsum_eq_single _ p
      intro q hq
      simp [zeroCoefficient, zero_support_singleton c ω.field hω ⟨p, hp⟩ q hq]
    refine ⟨(zero_coordinate_evaluation S o s hs K c hc ω.field ⟨p, hp⟩).trans hsum.symm,
      fun q => zero_coordinate_evaluation S o s hs K c hc ω.field q⟩
  · have hzero : ∀ p, ω.field p = 0 := by
      intro p
      by_contra hp
      exact hne ⟨p, hω (subset_closure hp)⟩
    have hint : coordinateIntegral s K c hc ω.field = 0 := by
      unfold coordinateIntegral
      have hf : signedCoordinateCoefficient s K c hc ω.field = 0 := by
        funext x
        unfold signedCoordinateCoefficient extendModel
        split_ifs with hm
        · unfold modelSignedCoefficient
          split_ifs with ht
          · simp [topCoefficient, hzero]
          · rfl
        · rfl
      rw [hf]
      exact integral_zero _ _
    refine ⟨?_, ?_⟩
    · rw [hint]
      symm
      unfold zeroIntegral
      simp [zeroCoefficient, hzero]
    · intro p
      exact (hne ⟨p.val, p.property⟩).elim


/-- Conditional exports: all twelve frozen orientation premises occur in the
supplied order. The owner will add closed wrappers after upstream closure. -/
theorem orientation_signs_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Integration.LocalSigned.orientation_signsType.{u} := by
  intro n a M _ S o
  exact (h_signed_charts S o.val).mp o.property

theorem coefficient_transition_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Integration.LocalSigned.coefficient_transitionType.{u} := by
  exact coefficient_transition_proof

theorem coordinate_formula_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Integration.LocalSigned.coordinate_formulaType.{u} := by
  exact coordinate_formula_proof

theorem integrable_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Integration.LocalSigned.integrableType.{u} := by
  exact integrable_proof

theorem chart_independence_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Integration.LocalSigned.chart_independenceType.{u} := by
  intro n a M _ S o s hs K L c d hc hd ω hωc hωd
  exact (coordinateIntegral_eq h_transition_jacobian S s K c d hc hd ω.field hωc hωd).trans
    (coordinateIntegral_coordinates_eq s K L d hd ω.field)

theorem artificial_edges_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Integration.LocalSigned.artificial_edgesType.{u} := by
  exact artificial_edges_proof

theorem boundary_null_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Integration.LocalSigned.boundary_nullType.{u} := by
  exact boundary_null_proof

theorem zero_finite_sum_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Integration.LocalSigned.zero_finite_sumType.{u} := by
  exact zero_finite_sum_proof

theorem zero_coordinate_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Integration.LocalSigned.zero_coordinateType.{u} := by
  exact zero_coordinate_proof

end SmoothManifolds.LocalIntegrationResults

universe v8_closure_3e1e629585b23bb8_u0
theorem _root_.«SmoothManifolds».«LocalIntegrationResults».«artificial_edges» : _root_.«Specs».«SmoothManifolds».«Integration».«LocalSigned».«artificial_edgesType».{v8_closure_3e1e629585b23bb8_u0} :=
  @_root_.«SmoothManifolds».«LocalIntegrationResults».«artificial_edges_conditional».{v8_closure_3e1e629585b23bb8_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_3e1e629585b23bb8_u0})
theorem _root_.«SmoothManifolds».«LocalIntegrationResults».«boundary_null» : _root_.«Specs».«SmoothManifolds».«Integration».«LocalSigned».«boundary_nullType».{v8_closure_3e1e629585b23bb8_u0} :=
  @_root_.«SmoothManifolds».«LocalIntegrationResults».«boundary_null_conditional».{v8_closure_3e1e629585b23bb8_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_3e1e629585b23bb8_u0})
theorem _root_.«SmoothManifolds».«LocalIntegrationResults».«chart_independence» : _root_.«Specs».«SmoothManifolds».«Integration».«LocalSigned».«chart_independenceType».{v8_closure_3e1e629585b23bb8_u0} :=
  @_root_.«SmoothManifolds».«LocalIntegrationResults».«chart_independence_conditional».{v8_closure_3e1e629585b23bb8_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_3e1e629585b23bb8_u0})
theorem _root_.«SmoothManifolds».«LocalIntegrationResults».«coefficient_transition» : _root_.«Specs».«SmoothManifolds».«Integration».«LocalSigned».«coefficient_transitionType».{v8_closure_3e1e629585b23bb8_u0} :=
  @_root_.«SmoothManifolds».«LocalIntegrationResults».«coefficient_transition_conditional».{v8_closure_3e1e629585b23bb8_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_3e1e629585b23bb8_u0})
theorem _root_.«SmoothManifolds».«LocalIntegrationResults».«coordinate_formula» : _root_.«Specs».«SmoothManifolds».«Integration».«LocalSigned».«coordinate_formulaType».{v8_closure_3e1e629585b23bb8_u0} :=
  @_root_.«SmoothManifolds».«LocalIntegrationResults».«coordinate_formula_conditional».{v8_closure_3e1e629585b23bb8_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_3e1e629585b23bb8_u0})
theorem _root_.«SmoothManifolds».«LocalIntegrationResults».«integrable» : _root_.«Specs».«SmoothManifolds».«Integration».«LocalSigned».«integrableType».{v8_closure_3e1e629585b23bb8_u0} :=
  @_root_.«SmoothManifolds».«LocalIntegrationResults».«integrable_conditional».{v8_closure_3e1e629585b23bb8_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_3e1e629585b23bb8_u0})
theorem _root_.«SmoothManifolds».«LocalIntegrationResults».«orientation_signs» : _root_.«Specs».«SmoothManifolds».«Integration».«LocalSigned».«orientation_signsType».{v8_closure_3e1e629585b23bb8_u0} :=
  @_root_.«SmoothManifolds».«LocalIntegrationResults».«orientation_signs_conditional».{v8_closure_3e1e629585b23bb8_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_3e1e629585b23bb8_u0})
theorem _root_.«SmoothManifolds».«LocalIntegrationResults».«zero_coordinate» : _root_.«Specs».«SmoothManifolds».«Integration».«LocalSigned».«zero_coordinateType».{v8_closure_3e1e629585b23bb8_u0} :=
  @_root_.«SmoothManifolds».«LocalIntegrationResults».«zero_coordinate_conditional».{v8_closure_3e1e629585b23bb8_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_3e1e629585b23bb8_u0})
theorem _root_.«SmoothManifolds».«LocalIntegrationResults».«zero_finite_sum» : _root_.«Specs».«SmoothManifolds».«Integration».«LocalSigned».«zero_finite_sumType».{v8_closure_3e1e629585b23bb8_u0} :=
  @_root_.«SmoothManifolds».«LocalIntegrationResults».«zero_finite_sum_conditional».{v8_closure_3e1e629585b23bb8_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_3e1e629585b23bb8_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_3e1e629585b23bb8_u0})
