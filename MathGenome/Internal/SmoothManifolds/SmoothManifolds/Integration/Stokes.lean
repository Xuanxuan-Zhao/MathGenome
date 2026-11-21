import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Stokes
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.LocalStokes
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Boundary

/-! Abstract Stokes for compactly supported C¹ intrinsic forms (M10.04).
The proved coordinate Stokes theorem is transported through signed charts and
a finite smooth partition; all support statements use the true boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.StokesResults
open ModelData AtlasData TangentData TangentBundleData DifferentialData CovectorData
  BundleOperationsData
  ExteriorData ExteriorDerivativeData FormPullbackData LocalIntegrationData
  GlobalIntegrationData OrientationData BoundaryData BoundaryOrientationData
  PartitionData Set Filter
universe u v

/-- Coefficient continuity implies continuity in the precise top-form interface
used by the global integral; the choice of tangent coordinates is immaterial. -/
theorem continuous_top_of_coefficients {d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    (ω : Field S d) (hω : IsContinuousField C d ω) : IsContinuousTopForm ω := by
  intro K c hc
  have hcoef : Continuous (fun p : c.source => fun I => coefficients C d c hc ω p I) :=
    continuous_pi (hω c hc)
  let e := ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d d
  have hcont : Continuous (fun p : c.source =>
      e (fun I => coefficients C d c hc ω p I) (fun i => Pi.single i 1)) :=
    (e.continuous.comp hcoef).eval continuous_const
  apply hcont.congr
  intro p
  change e ((((Pi.basisFun ℝ (Fin d)).map
    (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm).dualBasis.exteriorPower d).equivFun
      (ω p.val)) (fun i => Pi.single i 1) = _
  have he := @ExteriorDerivativeResults.coefficientAlternating_evaluate.{u}
    (TangentSpace S p.val) _ _ d d (C.tangent.fiberCoordinates.equiv c hc p.val p.property)
    (ω p.val) (fun i => Pi.single i 1)
  exact he.trans (LocalIntegrationResults.topCoefficient_coordinates_eq C.tangent.fiberCoordinates K
    c hc p.val p.property ω)

/-- The C¹ derivative is uniquely determined as a compact continuous top form. -/
theorem derivative_top_form :
    Specs.SmoothManifolds.Integration.Stokes.derivative_top_formType.{u} := by
  intro n a M _ S C ω hω hcompact
  obtain ⟨η, hη, hcont⟩ := ExteriorDerivativeResults.c1_derivative_exists C n ω hω
  let ζ : CompactTopForm S :=
    ⟨η, continuous_top_of_coefficients C η hcont,
      ExteriorDerivativeResults.derivative_compact_support C n ω η hη hcompact⟩
  refine ⟨ζ, ⟨hη, ExteriorDerivativeResults.derivative_support C n ω η hη⟩, ?_⟩
  intro ξ hξ
  have he := ExteriorDerivativeResults.derivative_unique C n ω ξ.field ζ.field hξ.1 hη
  cases ξ with
  | mk ξ hcontξ hcompξ =>
    have he' : ξ = η := he
    cases he'
    rfl

/-- Restriction to the actual boundary commutes with the intrinsic C¹
derivative. The inclusion differential is the one used by the pullback. -/
theorem boundary_restriction_naturality {n k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold (n+1) a M) (C : CotangentBundle S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (A : CotangentBundle B)
    (hB : IsNaturalBoundary S B)
    (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential B S Subtype.val p (L p))
    (ω : Field S k) (η : Field S (k+1)) (hω : IsRegularField C 1 k ω)
    (hη : HasExteriorDerivative C ω η) :
    IsRegularField A 1 k (pullbackField B S Subtype.val L ω) ∧
      HasExteriorDerivative A (pullbackField B S Subtype.val L ω)
        (pullbackField B S Subtype.val L η) :=
  ExteriorDerivativeResults.c1_naturality B S A C Subtype.val hB.1 L hL k ω η hω hη

/-- Closedness of the true boundary supplies compact support of the restricted
C¹ top form. Its regularity follows from C¹ restriction naturality. -/
theorem boundary_top_form :
    Specs.SmoothManifolds.Integration.Stokes.boundary_top_formType.{u} := by
  intro n a M _ S C B A hB L hL ω hω hcompact
  let ξ := pullbackField B S Subtype.val L ω
  obtain ⟨η, hη, _⟩ := ExteriorDerivativeResults.c1_derivative_exists C n ω hω
  have hreg : IsRegularField A 1 n ξ :=
    (boundary_restriction_naturality S C B A hB L hL ω η hω hη).1
  have hs := GlobalIntegrationResults.boundary_support S B L n ω
  refine ⟨⟨ξ, continuous_top_of_coefficients A ξ
    (ExteriorDerivativeResults.regular_continuous A n 1 ξ hreg), hs.2 hcompact⟩,
    rfl, hreg, hs.1⟩

theorem compact_support :
    Specs.SmoothManifolds.Integration.Stokes.compact_supportType.{u} := by
  intro d a M _ _ S k ω
  exact isClosed_closure.isCompact

theorem empty_boundary_integral :
    Specs.SmoothManifolds.Integration.Stokes.empty_boundary_integralType.{u} := by
  intro n a M _ S B q J hJ hempty β
  have hz : β.field = 0 := by
    funext p
    exact False.elim (by simpa [hempty] using p.property)
  have h := hJ.2.1 0 β β (by rw [hz]; simp)
  simpa using h

/-- Multiplication by a smooth partition function preserves the manuscript's
local C¹ extension regularity. -/
theorem regular_weight {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    (ω : Field S k) (hω : IsRegularField C 1 k ω) (ρ : M → ℝ)
    (hρ : ScalarSmooth S.smoothStructure.val ρ) :
    IsRegularField C 1 k (fun p => ρ p • ω p) := by
  intro c hc p
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hω c hc p
  obtain ⟨_, hρext⟩ := (scalarContDiffAt_iff (⊤ : ℕ∞)
    S.smoothStructure.val ρ p.val).mp (hρ p.val)
  obtain ⟨V, hV, hpV, g, hg, heg⟩ := hρext c hc p.property
  let H : Euclidean d → Index d k → ℝ := fun z => g z • F z
  have hg' : ContDiffAt ℝ 1 g (c p.val).val :=
    (hg.contDiffAt (hV.mem_nhds hpV)).of_le (by norm_num)
  have hH : ContDiffAt ℝ 1 H (c p.val).val :=
    hg'.smul (hF.contDiffAt (hU.mem_nhds hpU))
  apply ExteriorDerivativeResults.localExtensionAt_of_germ 1 c _ p H hH
  have hcoord : ContinuousAt (fun q : M => (c q).val) p.val :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt p.property)
  filter_upwards [heg, c.open_source.mem_nhds p.property,
    hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hqg hqc hqU
  rw [FrameData.totalize_of_mem _ q hqc]
  change g (c q).val • F (c q).val = _
  rw [hqg, heF ⟨q, hqc⟩ hqU]
  funext I
  simp [coefficients, map_smul]

theorem regular_finset_sum {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    {ι : Type v} (t : Finset ι) (ω : ι → Field S k)
    (hω : ∀ i ∈ t, IsRegularField C 1 k (ω i)) :
    IsRegularField C 1 k (∑ i ∈ t, ω i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using ExteriorDerivativeResults.regularField_zero C 1 k
  | @insert i t hi ih =>
    simpa [Finset.sum_insert hi] using
      ExteriorDerivativeResults.regularField_add C k 1 (hω i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hω j (Finset.mem_insert_of_mem hj)))

/-- Finite linearity for C¹ forms, without invoking a smooth-only derivative
operator or assuming smoothness of the original form. -/
theorem derivative_finset_sum {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    {ι : Type v} (t : Finset ι) (ω : ι → Field S k) (η : ι → Field S (k+1))
    (hω : ∀ i ∈ t, IsRegularField C 1 k (ω i))
    (hη : ∀ i ∈ t, HasExteriorDerivative C (ω i) (η i)) :
    HasExteriorDerivative C (∑ i ∈ t, ω i) (∑ i ∈ t, η i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using ExteriorDerivativeResults.zero_derivative C k
  | @insert i t hi ih =>
    have hωt : ∀ j ∈ t, IsRegularField C 1 k (ω j) :=
      fun j hj => hω j (Finset.mem_insert_of_mem hj)
    have hηt : ∀ j ∈ t, HasExteriorDerivative C (ω j) (η j) :=
      fun j hj => hη j (Finset.mem_insert_of_mem hj)
    simpa [Finset.sum_insert hi] using ExteriorDerivativeResults.derivative_add C k
      (ω i) (∑ j ∈ t, ω j) (η i) (∑ j ∈ t, η j)
      (hω i (Finset.mem_insert_self _ _)) (regular_finset_sum C t ω hωt)
      (hη i (Finset.mem_insert_self _ _)) (ih hωt hηt)

/-- A compactly supported field has a single finite decomposition under any
locally finite partition. The equality is of whole fields, so it includes every
point of the boundary of the support. -/
theorem finite_weight_decomposition {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (ω : Field S k)
    (hcompact : IsCompact (sectionSupport ω)) {ι : Type v} (ρ : ι → M → ℝ)
    (hlf : LocallyFinite (fun i => sectionSupport (ρ i)))
    (hsum : ∀ p, ∑ᶠ i, ρ i p = 1) :
    ∃ t : Finset ι,
      (∀ i ∉ t, (fun p => ρ i p • ω p) = (0 : Field S k)) ∧
      ω = ∑ i ∈ t, (fun p => ρ i p • ω p) := by
  classical
  have hfin := hlf.finite_nonempty_inter_compact hcompact
  let t := hfin.toFinset
  have ht (p : M) (hp : ω p ≠ 0) : Function.support (fun i => ρ i p) ⊆ t := by
    intro i hi
    exact hfin.mem_toFinset.mpr ⟨p, subset_closure hi, subset_closure hp⟩
  refine ⟨t, ?_, ?_⟩
  · intro i hi
    funext p
    by_cases hp : ω p = 0
    · simp [hp]
    · have hz : ρ i p = 0 := by
        by_contra hz
        exact hi (ht p hp hz)
      simp [hz]
  · funext p
    simp only [Finset.sum_apply]
    by_cases hp : ω p = 0
    · simp [hp]
    · have hs : ∑ i ∈ t, ρ i p = 1 := by
        rw [← finsum_eq_sum_of_support_subset _ (ht p hp)]
        exact hsum p
      rw [← Finset.sum_smul, hs, one_smul]

/-- Differentiating the finite decomposition gives dω at all points, including
support-boundary points. This avoids differentiating a pointwise-truncated sum. -/
theorem derivative_of_partition {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    (ω : Field S k) (hω : IsRegularField C 1 k ω)
    (η : Field S (k+1)) (hη : HasExteriorDerivative C ω η)
    (hcompact : IsCompact (sectionSupport ω)) {ι : Type v} (ρ : ι → M → ℝ)
    (hρ : IsSmoothPartition S.smoothStructure.val ρ)
    (δ : ι → Field S (k+1))
    (hδ : ∀ i, HasExteriorDerivative C (fun p => ρ i p • ω p) (δ i)) :
    ∃ t : Finset ι,
      (∀ i ∉ t, (fun p => ρ i p • ω p) = (0 : Field S k)) ∧
      ω = ∑ i ∈ t, (fun p => ρ i p • ω p) ∧ η = ∑ i ∈ t, δ i := by
  obtain ⟨t, ht, he⟩ := finite_weight_decomposition ω hcompact ρ hρ.2.2.1 hρ.2.2.2
  refine ⟨t, ht, he, ?_⟩
  have hd := derivative_finset_sum C t (fun i p => ρ i p • ω p) δ
    (fun i _ => regular_weight C ω hω (ρ i) (hρ.1 i)) (fun i _ => hδ i)
  rw [← he] at hd
  exact ExteriorDerivativeResults.derivative_unique C k ω η _ hη hd

/-- The actual coordinate alternating form, zero off the chart target and off
the model. Its values outside the model are immaterial for half-space Stokes. -/
def chartForm {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (C : CotangentBundle S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k) :
    LocalStokesData.CoordinateForm d k :=
  fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k
    (fun I => ambientCoefficient C k c hc ω I z)

theorem chartForm_at {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (C : CotangentBundle S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (p : c.source) :
    chartForm C c hc ω (c p.val).val =
      ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k
        (fun I => coefficients C k c hc ω p I) := by
  simp [chartForm, ambientCoefficient, (c p.val).property,
    c.map_source p.property, c.left_inv p.property]

/-- A nonzero coordinate value comes from the original section's support. -/
theorem chartForm_nonzero {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (C : CotangentBundle S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (z : Euclidean d) (hz : chartForm C c hc ω z ≠ 0) :
    ∃ p ∈ sectionSupport ω, p ∈ c.source ∧ (c p).val = z := by
  classical
  by_cases hm : z ∈ modelSet d a
  · by_cases ht : (⟨z, hm⟩ : ModelSpace d a) ∈ c.target
    · refine ⟨c.symm ⟨z, hm⟩, ?_, c.map_target ht, congrArg Subtype.val (c.right_inv ht)⟩
      apply subset_closure
      intro hzero
      apply hz
      have hcoeff : (fun I => ambientCoefficient C k c hc ω I z) = 0 := by
        funext I
        simp only [ambientCoefficient, dif_pos hm, dif_pos ht]
        dsimp only [coefficients]
        rw [hzero]
        exact congrArg (fun f : Index d k →₀ ℝ => f I) (LinearEquiv.map_zero _)
      change (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k) _ = 0
      exact (congrArg (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k) hcoeff).trans
        (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k).map_zero
    · apply False.elim (hz ?_)
      have hcoeff : (fun I => ambientCoefficient C k c hc ω I z) = 0 := by
        funext I
        simp [ambientCoefficient, hm, ht]
      exact (congrArg (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k) hcoeff).trans
        (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k).map_zero
  · apply False.elim (hz ?_)
    have hcoeff : (fun I => ambientCoefficient C k c hc ω I z) = 0 := by
      funext I
      simp [ambientCoefficient, hm]
    exact (congrArg (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k) hcoeff).trans
      (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k).map_zero

theorem chartForm_compact_container {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (hcompact : IsCompact (sectionSupport ω)) (hs : sectionSupport ω ⊆ c.source) :
    IsCompact ((fun p : M => (c p).val) '' sectionSupport ω) ∧
      Function.support (chartForm C c hc ω) ⊆
        (fun p : M => (c p).val) '' sectionSupport ω := by
  refine ⟨hcompact.image_of_continuousOn
    (continuous_subtype_val.comp_continuousOn (c.continuousOn.mono hs)), ?_⟩
  intro z hz
  obtain ⟨p, hp, _, he⟩ := chartForm_nonzero C c hc ω z hz
  exact ⟨p, hp, he⟩

/-- The extension is zero on an entire ambient neighborhood of each artificial
edge. No such vanishing is asserted at the model's true boundary. -/
theorem chartForm_artificial_edge {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (hcompact : IsCompact (sectionSupport ω)) (hs : sectionSupport ω ⊆ c.source)
    (z : ModelSpace d a) (hz : z ∉ c.target) :
    ∃ U : Set (Euclidean d), IsOpen U ∧ z.val ∈ U ∧
      ∀ y ∈ U, chartForm C c hc ω y = 0 := by
  obtain ⟨hK, hsub⟩ := chartForm_compact_container C c hc ω hcompact hs
  refine ⟨((fun p : M => (c p).val) '' sectionSupport ω)ᶜ,
    hK.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨p, hp, he⟩
    have he' : c p = z := Subtype.ext he
    exact hz (he' ▸ c.map_source (hs hp))
  · intro y hy
    by_contra hn
    exact hy (hsub hn)

/-- Compact support is relative to the full coordinate model and may meet its
true boundary. -/
theorem chartForm_compact_support {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (hcompact : IsCompact (sectionSupport ω)) (hs : sectionSupport ω ⊆ c.source) :
    HasCompactSupport (fun z : ModelSpace d a => chartForm C c hc ω z.val) := by
  obtain ⟨hK, hsub⟩ := chartForm_compact_container C c hc ω hcompact hs
  have hemb := (LocalIntegrationResults.modelSet_closed d a).isClosedEmbedding_subtypeVal
  apply (hemb.isCompact_preimage hK).of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro z hz
    exact hsub hz
  · exact hK.isClosed.preimage continuous_subtype_val

/-- Local C¹ coefficient extensions survive extension by zero across artificial
chart edges, including for a half-space chart touching the true boundary. -/
theorem chartForm_regular {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (hω : IsRegularField C 1 k ω) (hcompact : IsCompact (sectionSupport ω))
    (hs : sectionSupport ω ⊆ c.source) :
    LocallyContDiffOn 1 (modelSet d a) (fun z => chartForm C c hc ω z.val) := by
  intro z
  by_cases hz : z ∈ c.target
  · let p : c.source := ⟨c.symm z, c.map_target hz⟩
    obtain ⟨U, hU, hpU, F, hF, heF⟩ := hω c hc p
    obtain ⟨V, hV, hVT⟩ := isOpen_induced_iff.mp c.open_target
    have hzV : z.val ∈ V := by
      change z ∈ Subtype.val ⁻¹' V
      rw [hVT]
      exact hz
    have hzU : z.val ∈ U := by simpa only [p, c.right_inv hz] using hpU
    let e := ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k
    refine ⟨U ∩ V, hU.inter hV, ⟨hzU, hzV⟩, fun y => e (F y),
      e.contDiff.comp_contDiffOn (hF.mono inter_subset_left), ?_⟩
    intro y hy
    have hyt : y ∈ c.target := by
      rw [← hVT]
      exact hy.2
    have hey := heF ⟨c.symm y, c.map_target hyt⟩
      (by simpa only [c.right_inv hyt] using hy.1)
    simp only [c.right_inv hyt] at hey
    simp only [chartForm, ambientCoefficient, y.property, hyt, ↓reduceDIte]
    exact congrArg e hey
  · obtain ⟨U, hU, hzU, hzero⟩ := chartForm_artificial_edge C c hc ω hcompact hs z hz
    exact ⟨U, hU, hzU, fun _ => 0, contDiffOn_const, fun y hy => (hzero y.val hy).symm⟩

/-- Differentiating the analytic coordinate form computes the actual intrinsic
coordinate derivative. This is an equality at true boundary points as well. -/
theorem chartForm_extDerivWithin {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (hω : IsRegularField C 1 k ω) (p : c.source) (v : Fin (k+1) → Euclidean d) :
    extDerivWithin (chartForm C c hc ω) (modelSet d a) (c p.val).val v =
      evaluate (TangentSpace S p.val) (k+1)
        (coordinateDerivative C k c hc ω p.val p.property)
        (fun i => (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm (v i)) := by
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hω c hc p
  obtain ⟨V, hV, hVT⟩ := isOpen_induced_iff.mp c.open_target
  have hpV : (c p.val).val ∈ V := by
    change c p.val ∈ Subtype.val ⁻¹' V
    rw [hVT]
    exact c.map_source p.property
  let e := ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k
  have he : chartForm C c hc ω =ᶠ[𝓝[modelSet d a] (c p.val).val] (fun y => e (F y)) := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hpU),
      nhdsWithin_le_nhds (hV.mem_nhds hpV), self_mem_nhdsWithin] with y hyU hyV hyM
    let z : ModelSpace d a := ⟨y, hyM⟩
    have hyt : z ∈ c.target := by
      rw [← hVT]
      exact hyV
    have hey := heF ⟨c.symm z, c.map_target hyt⟩
      (by simpa only [c.right_inv hyt] using hyU)
    simp only [c.right_inv hyt] at hey
    change e (fun I => ambientCoefficient C k c hc ω I y) = e (F y)
    apply congrArg e
    funext I
    have hyt' : (⟨y, hyM⟩ : ModelSpace d a) ∈ c.target := hyt
    simp only [ambientCoefficient, dif_pos hyM, dif_pos hyt']
    exact (congrFun hey I).symm
  have hd : DifferentiableAt ℝ (fun y => e (F y)) (c p.val).val :=
    e.differentiableAt.comp _ ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num))
  have hde : extDerivWithin (fun y => e (F y)) (modelSet d a) (c p.val).val =
      extDeriv (fun y => e (F y)) (c p.val).val := by
    unfold extDerivWithin extDeriv
    rw [hd.fderivWithin (uniqueDiffOn_modelSet d a _ (c p.val).property)]
  rw [he.extDerivWithin_eq_of_mem (c p.val).property, hde]
  exact (ExteriorDerivativeResults.coordinateDerivative_evaluate_extension C k c hc ω
    p.val p.property U hU hpU F hF heF v).symm

/-- The top coefficient used by the existing integral is exactly the analytic
bulk coefficient, including the zero neighborhoods at artificial chart edges. -/
theorem chartForm_bulk {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M} (C : CotangentBundle S)
    (c : ModelChart (n+1) a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n)
    (hω : IsRegularField C 1 n ω) (hcompact : IsCompact (sectionSupport ω))
    (hs : sectionSupport ω ⊆ c.source) (η : Field S (n+1))
    (hη : HasExteriorDerivative C ω η) (z : ModelSpace (n+1) a) :
    extDerivWithin (chartForm C c hc ω) (modelSet (n+1) a) z.val (LocalStokesData.frame (n+1)) =
      coordinateCoefficient C.tangent.fiberCoordinates c hc η z.val := by
  by_cases hz : z ∈ c.target
  · let p : c.source := ⟨c.symm z, c.map_target hz⟩
    have he := chartForm_extDerivWithin C c hc ω hω p (LocalStokesData.frame (n+1))
    simp only [p, c.right_inv hz] at he
    rw [he, ← hη c hc (c.symm z) (c.map_target hz)]
    simp only [coordinateCoefficient, extendModel, modelCoefficient,
      dif_pos z.property, dif_pos hz]
    rfl
  · obtain ⟨U, hU, hzU, hzero⟩ := chartForm_artificial_edge C c hc ω hcompact hs z hz
    have he : chartForm C c hc ω =ᶠ[𝓝 z.val] (fun _ => 0) := by
      filter_upwards [hU.mem_nhds hzU] with y hy
      exact hzero y hy
    rw [he.extDerivWithin_eq_nhds]
    simp only [coordinateCoefficient, extendModel, modelCoefficient,
      dif_pos z.property, dif_neg hz]
    unfold extDerivWithin
    rw [fderivWithin_const_apply]
    change ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclidean (n+1)) ℝ) 0) _ = 0
    rw [map_zero]
    rfl

/-- In a Euclidean model the zero-extended coordinate form is genuinely C¹ on
the whole ambient space. -/
theorem chartForm_contDiff {d k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d .euclidean M} (C : CotangentBundle S)
    (c : ModelChart d .euclidean M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (hω : IsRegularField C 1 k ω) (hcompact : IsCompact (sectionSupport ω))
    (hs : sectionSupport ω ⊆ c.source) : ContDiff ℝ 1 (chartForm C c hc ω) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  obtain ⟨U, hU, hzU, F, hF, heF⟩ :=
    chartForm_regular C c hc ω hω hcompact hs ⟨z, mem_univ z⟩
  apply (hF.contDiffAt (hU.mem_nhds hzU)).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with y hy
  exact (heF ⟨y, mem_univ y⟩ hy).symm

/-- The unsigned Euclidean chart integral of dω vanishes by precisely the full
local Stokes premise. Sign transport is a separate globalization step. -/
theorem fullSpace_chart_integral_zero
    (local_stokes : Specs.SmoothManifolds.Integration.LocalStokes.local_stokesType)
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .euclidean M} (C : CotangentBundle S)
    (c : ModelChart (n+1) .euclidean M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n)
    (hω : IsRegularField C 1 n ω) (hcompact : IsCompact (sectionSupport ω))
    (hs : sectionSupport ω ⊆ c.source) (η : Field S (n+1))
    (hη : HasExteriorDerivative C ω η) :
    (∫ z, coordinateCoefficient C.tangent.fiberCoordinates c hc η z) = 0 := by
  have hreg := chartForm_contDiff C c hc ω hω hcompact hs
  obtain ⟨hK, hsub⟩ := chartForm_compact_container C c hc ω hcompact hs
  have hsupport : HasCompactSupport (chartForm C c hc ω) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)
  have hlocal := (local_stokes.1 n (chartForm C c hc ω) hreg hsupport).2
  have he : LocalStokesData.bulkCoefficient (chartForm C c hc ω) =
      coordinateCoefficient C.tangent.fiberCoordinates c hc η := by
    funext z
    have hh := chartForm_bulk C c hc ω hω hcompact hs η hη ⟨z, mem_univ z⟩
    simpa only [ModelData.modelSet, extDerivWithin_univ, LocalStokesData.bulkCoefficient] using hh
  rwa [he] at hlocal

/-- Coefficient regularity is a local property of the intrinsic field. -/
theorem regular_of_local_eq {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (C : CotangentBundle S)
    (ω : Field S k)
    (hlocal : ∀ p : M, ∃ α : Field S k, IsRegularField C 1 k α ∧
      ∀ᶠ q in 𝓝 p, ω q = α q) : IsRegularField C 1 k ω := by
  intro c hc p
  obtain ⟨α, hα, heα⟩ := hlocal p.val
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hα c hc p
  apply ExteriorDerivativeResults.localExtensionAt_of_germ 1 c _ p F
    (hF.contDiffAt (hU.mem_nhds hpU))
  have hcoord : ContinuousAt (fun q : M => (c q).val) p.val :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt p.property)
  filter_upwards [heα, c.open_source.mem_nhds p.property,
    hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hqα hqc hqU
  rw [FrameData.totalize_of_mem _ q hqc, heF ⟨q, hqc⟩ hqU]
  funext I
  dsimp only [coefficients]
  rw [hqα]

/-- Vanishing holds on an open neighborhood outside a closed section support. -/
theorem zero_germ_outside_support {d k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (ω : Field S k)
    (p : M) (hp : p ∉ sectionSupport ω) : ∀ᶠ q in 𝓝 p, ω q = 0 := by
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hp] with q hq
  by_contra hn
  exact hq (subset_closure hn)

/-- Multiply by the chart orientation sign on the source, with value zero
elsewhere. Compact containment of the form's support makes this a C¹ operation
despite the arbitrary chart edge. -/
def signedField {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (s : SignedCharts S) (c : ModelChart d a M)
    (hc : c ∈ S.smoothStructure.val) (ω : Field S k) : Field S k :=
  fun p => if hp : p ∈ c.source then signValue (s.sign c hc ⟨p, hp⟩) • ω p else 0

theorem signedField_germ {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (s : SignedCharts S) (c : ModelChart d a M)
    (hc : c ∈ S.smoothStructure.val) (ω : Field S k) (p : c.source) :
    ∀ᶠ q in 𝓝 p.val, signedField s c hc ω q = signValue (s.sign c hc p) • ω q := by
  let O : Set c.source := (s.sign c hc) ⁻¹' {s.sign c hc p}
  have hO : IsOpen O := s.locallyConstant c hc _
  have hpO : p.val ∈ Subtype.val '' O := ⟨p, rfl, rfl⟩
  filter_upwards [(c.open_source.isOpenMap_subtype_val O hO).mem_nhds hpO] with q hq
  obtain ⟨r, hr, rfl⟩ := hq
  have hr' : s.sign c hc r = s.sign c hc p := hr
  simp only [signedField, dif_pos r.property, hr']

theorem signedField_support {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (s : SignedCharts S) (c : ModelChart d a M)
    (hc : c ∈ S.smoothStructure.val) (ω : Field S k) :
    sectionSupport (signedField s c hc ω) ⊆ sectionSupport ω := by
  apply closure_minimal _ isClosed_closure
  intro p hp
  apply subset_closure
  intro hzero
  apply hp
  simp [signedField, hzero]

theorem signedField_zero_germ {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (s : SignedCharts S) (c : ModelChart d a M)
    (hc : c ∈ S.smoothStructure.val) (ω : Field S k) (p : M)
    (hp : p ∉ sectionSupport ω) : ∀ᶠ q in 𝓝 p, signedField s c hc ω q = 0 := by
  filter_upwards [zero_germ_outside_support ω p hp] with q hq
  simp [signedField, hq]

theorem signedField_regular {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (C : CotangentBundle S) (s : SignedCharts S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (hω : IsRegularField C 1 k ω) (hs : sectionSupport ω ⊆ c.source) :
    IsRegularField C 1 k (signedField s c hc ω) := by
  apply regular_of_local_eq C
  intro p
  by_cases hp : p ∈ c.source
  · exact ⟨signValue (s.sign c hc ⟨p, hp⟩) • ω,
      ExteriorDerivativeResults.regularField_smul C k 1 _ hω, signedField_germ s c hc ω ⟨p, hp⟩⟩
  · exact ⟨0, ExteriorDerivativeResults.regularField_zero C 1 k,
      signedField_zero_germ s c hc ω p (fun h => hp (hs h))⟩

/-- A locally constant orientation sign commutes with d, also across chart
edges because both original fields vanish on a neighborhood there. -/
theorem signedField_derivative {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (C : CotangentBundle S) (s : SignedCharts S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (hω : IsRegularField C 1 k ω) (hs : sectionSupport ω ⊆ c.source)
    (η : Field S (k+1)) (hη : HasExteriorDerivative C ω η) :
    HasExteriorDerivative C (signedField s c hc ω) (signedField s c hc η) := by
  obtain ⟨δ, hδ, _⟩ := ExteriorDerivativeResults.c1_derivative_exists C k
    (signedField s c hc ω) (signedField_regular C s c hc ω hω hs)
  have he : δ = signedField s c hc η := by
    funext p
    by_cases hp : p ∈ c.source
    · have hd := ExteriorDerivativeResults.derivative_smul C k
        (signValue (s.sign c hc ⟨p, hp⟩)) ω η hω hη
      have heq := ExteriorDerivativeResults.derivative_locality C k
        (signedField s c hc ω) (signValue (s.sign c hc ⟨p, hp⟩) • ω) δ
        (signValue (s.sign c hc ⟨p, hp⟩) • η) hδ hd p (signedField_germ s c hc ω ⟨p, hp⟩)
      simpa only [signedField, dif_pos hp, Pi.smul_apply] using heq
    · have heq := ExteriorDerivativeResults.derivative_locality C k
        (signedField s c hc ω) 0 δ 0 hδ (ExteriorDerivativeResults.zero_derivative C k) p
        (signedField_zero_germ s c hc ω p (fun h => hp (hs h)))
      simpa only [signedField, dif_neg hp, Pi.zero_apply] using heq
  rwa [he] at hδ

theorem chartForm_outside {d k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (C : CotangentBundle S) (c : ModelChart d a M)
    (hc : c ∈ S.smoothStructure.val) (ω : Field S k) (z : ModelSpace d a)
    (hz : z ∉ c.target) : chartForm C c hc ω z.val = 0 := by
  have he : (fun I => ambientCoefficient C k c hc ω I z.val) = 0 := by
    funext I
    simp only [ambientCoefficient, dif_pos z.property, dif_neg hz, Pi.zero_apply]
  exact (congrArg (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k) he).trans
    (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv d k).map_zero

/-- In face coordinates the inclusion sends the ordered tangential basis to
the first n bulk coordinate vectors, even when n=0. -/
theorem face_coordinate_vectors {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M) (C : CotangentBundle S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (A : CotangentBundle B)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val)
    (hface : IsFaceRestriction S c b) (p : intrinsicBoundary S) (hp : p ∈ b.source)
    (hpc : p.val ∈ c.source)
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : IsDifferential B S Subtype.val p L) (j : Fin n) :
    L (CovectorData.coordinateVector A.tangent.fiberCoordinates b hb p hp j) =
      CovectorData.coordinateVector C.tangent.fiberCoordinates c hc p.val hpc j.castSucc := by
  let E := C.tangent.fiberCoordinates.equiv c hc p.val hpc
  let F := A.tangent.fiberCoordinates.equiv b hb p hp
  apply E.injective
  rw [boundary_inclusion_coordinates S B p c hc hpc b hb hface L hL E
    (C.tangent.fiberCoordinates.isCoordinates c hc p.val hpc)]
  rw [← chartCoordinates_eq B p b hb hp F (A.tangent.fiberCoordinates.isCoordinates b hb p hp)]
  change Fin.snoc (F (F.symm (Pi.single j 1))) 0 = E (E.symm (Pi.single j.castSucc 1))
  rw [F.apply_symm_apply, E.apply_symm_apply]
  ext i
  refine Fin.lastCases ?_ (fun l => ?_) i <;> simp [Pi.single_apply]

/-- The local analytic boundary coefficient is exactly the actual restricted
intrinsic form coefficient, with the outward-first factor (-1)^(n+1). -/
theorem chartForm_boundary {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M) (C : CotangentBundle S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (A : CotangentBundle B)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val)
    (hface : IsFaceRestriction S c b)
    (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential B S Subtype.val p (L p)) (ω : Field S n) :
    LocalStokesData.boundaryCoefficient (chartForm C c hc ω) =
      fun x => (-1 : ℝ)^(n+1) * coordinateCoefficient A.tangent.fiberCoordinates b hb
        (pullbackField B S Subtype.val L ω) x := by
  funext x
  let x' : ModelSpace n .euclidean := ⟨x, mem_univ x⟩
  by_cases hx : x' ∈ b.target
  · let p : intrinsicBoundary S := b.symm x'
    have hp : p ∈ b.source := b.map_target hx
    have hpc : p.val ∈ c.source := by rwa [hface.1] at hp
    have hpz : (c p.val).val = Fin.snoc x 0 := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hh := (intrinsicBoundary_iff_chart S c hc p.val hpc).mp p.property
        change (c p.val).val (Fin.last n) = 0 at hh
        simpa only [Fin.snoc_last] using hh
      · rw [Fin.snoc_castSucc, ← hface.2.2 p hp j]
        exact congrArg (fun z : ModelSpace n .euclidean => z.val j) (b.right_inv hx)
    let E := C.tangent.fiberCoordinates.equiv c hc p.val hpc
    have hchart : chartForm C c hc ω (Fin.snoc x 0)
        (fun j => LocalStokesData.frame (n+1) j.castSucc) =
        topCoefficient A.tangent.fiberCoordinates b hb p hp (pullbackField B S Subtype.val L ω) := by
      rw [← hpz, chartForm_at C c hc ω ⟨p.val, hpc⟩]
      have he := @ExteriorDerivativeResults.coefficientAlternating_evaluate.{u}
        (TangentSpace S p.val) _ _ (n+1) n E (ω p.val)
        (fun j => LocalStokesData.frame (n+1) j.castSucc)
      change (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv (n+1) n
        ((((Pi.basisFun ℝ (Fin (n+1))).map E.symm).dualBasis.exteriorPower n).equivFun (ω p.val)))
        (fun j => LocalStokesData.frame (n+1) j.castSucc) = _
      refine he.trans ?_
      have hv : (fun j => E.symm (LocalStokesData.frame (n+1) j.castSucc)) =
          (fun j => L p (CovectorData.coordinateVector A.tangent.fiberCoordinates b hb p hp j)) := by
        funext j
        exact (face_coordinate_vectors S C B A c hc b hb hface p hp hpc (L p) (hL p) j).symm
      rw [hv]
      exact (@FormPullbackResults.evaluate_fiberPullback.{u}
        (TangentSpace B p) (TangentSpace S p.val) _ _ _ _ n (L p) (ω p.val)
        (CovectorData.coordinateVector A.tangent.fiberCoordinates b hb p hp)).symm
    rw [LocalStokesData.boundaryCoefficient, Fin.insertNth_last', hchart]
    have hx' : (⟨x, mem_univ x⟩ : ModelSpace n .euclidean) ∈ b.target := hx
    unfold coordinateCoefficient extendModel
    rw [dite_eq_left (show x ∈ ModelData.modelSet n .euclidean from mem_univ x)]
    unfold modelCoefficient
    rw [dite_eq_left hx']
  · have hxc : faceEmbedding .halfSpace x' ∉ c.target := by
      intro hh
      apply hx
      rw [hface.2.1]
      exact hh
    have hz := chartForm_outside C c hc ω (faceEmbedding .halfSpace x') hxc
    change chartForm C c hc ω (Fin.snoc x 0) = 0 at hz
    rw [LocalStokesData.boundaryCoefficient, Fin.insertNth_last', hz]
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero]
    have hx' : (⟨x, mem_univ x⟩ : ModelSpace n .euclidean) ∉ b.target := hx
    unfold coordinateCoefficient extendModel
    rw [dite_eq_left (show x ∈ ModelData.modelSet n .euclidean from mem_univ x)]
    unfold modelCoefficient
    rw [dite_eq_right hx', mul_zero]

/-- Absorbing the orientation sign into the field gives exactly the signed
integrand used by global integration, including its zero extensions. -/
theorem signedCoefficient_as_unsigned {d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (s : SignedCharts S)
    (K : FiberCoordinates S) (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val)
    (η : Field S d) : signedCoordinateCoefficient s K c hc η =
      coordinateCoefficient K c hc (signedField s c hc η) := by
  funext z
  unfold signedCoordinateCoefficient coordinateCoefficient extendModel
  split_ifs with hm
  · unfold modelSignedCoefficient modelCoefficient
    split_ifs with ht
    · simp only [topCoefficient, signedField, dif_pos (c.map_target ht), map_smul,
        smul_apply, smul_eq_mul]
    · rfl
  · rfl

theorem integral_zero_field {d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} (o : Orientation S) (I : CompactTopForm S → ℝ)
    (hI : IsIntegral o I) (η : CompactTopForm S) (hη : η.field = 0) : I η = 0 := by
  have h := hI.2.1 0 η η (by rw [hη]; simp)
  simpa using h

/-- The ambient zero-extended integral agrees with the actual half-space bulk
integral in the local Stokes specification. -/
theorem halfSpace_chart_bulk_integral {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .halfSpace M} (C : CotangentBundle S)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n)
    (hω : IsRegularField C 1 n ω) (hcompact : IsCompact (sectionSupport ω))
    (hs : sectionSupport ω ⊆ c.source) (η : Field S (n+1))
    (hη : HasExteriorDerivative C ω η) :
    (∫ z, coordinateCoefficient C.tangent.fiberCoordinates c hc η z) =
      ∫ z in halfSpaceSet (n+1), LocalStokesData.halfSpaceBulkCoefficient (chartForm C c hc ω) z := by
  have hm : MeasurableSet (halfSpaceSet (n+1)) :=
    (LocalIntegrationResults.modelSet_closed (n+1) .halfSpace).measurableSet
  have he : (halfSpaceSet (n+1)).indicator (coordinateCoefficient C.tangent.fiberCoordinates c hc η) =
      coordinateCoefficient C.tangent.fiberCoordinates c hc η := by
    funext z
    by_cases hz : z ∈ halfSpaceSet (n+1)
    · simp only [indicator_of_mem hz]
    · simp only [indicator_of_notMem hz]
      unfold coordinateCoefficient extendModel
      rw [dite_eq_right (show z ∉ ModelData.modelSet (n+1) .halfSpace from hz)]
  rw [← he, MeasureTheory.integral_indicator hm]
  apply MeasureTheory.setIntegral_congr_fun hm
  intro z hz
  exact (chartForm_bulk C c hc ω hω hcompact hs η hη ⟨z, hz⟩).symm

theorem coordinateCoefficient_at {d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (K : FiberCoordinates S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (η : Field S d)
    (z : ModelSpace d a) (hz : z ∈ c.target) :
    coordinateCoefficient K c hc η z.val = topCoefficient K c hc (c.symm z) (c.map_target hz) η := by
  unfold coordinateCoefficient extendModel
  rw [dite_eq_left z.property]
  unfold modelCoefficient
  rw [dite_eq_left hz]

theorem signedCoordinateCoefficient_at {d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold d a M} (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart d a M) (hc : c ∈ S.smoothStructure.val) (η : Field S d)
    (z : ModelSpace d a) (hz : z ∈ c.target) :
    signedCoordinateCoefficient s K c hc η z.val =
      signValue (s.sign c hc ⟨c.symm z, c.map_target hz⟩) *
        topCoefficient K c hc (c.symm z) (c.map_target hz) η := by
  unfold signedCoordinateCoefficient extendModel
  rw [dite_eq_left z.property]
  unfold modelSignedCoefficient
  rw [dite_eq_left hz]

/-- The outward-first boundary chart sign converts the analytic boundary term
of the sign-weighted bulk form into the actual signed boundary integrand. -/
theorem signed_chart_boundary {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M) (C : CotangentBundle S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (A : CotangentBundle B)
    (hB : IsNaturalBoundary S B) (o : Orientation S) (q : Orientation B)
    (hq : IsInducedOrientation o q) (s : SignedCharts S) (t : SignedCharts B)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts q.val t)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val)
    (hface : IsFaceRestriction S c b)
    (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential B S Subtype.val p (L p)) (ω : Field S n) :
    LocalStokesData.boundaryCoefficient (chartForm C c hc (signedField s c hc ω)) =
      signedCoordinateCoefficient t A.tangent.fiberCoordinates b hb (pullbackField B S Subtype.val L ω) := by
  rw [chartForm_boundary S C B A c hc b hb hface L hL]
  funext x
  let z : ModelSpace n .euclidean := ⟨x, mem_univ x⟩
  by_cases hz : z ∈ b.target
  · rw [coordinateCoefficient_at A.tangent.fiberCoordinates b hb _ z hz,
      signedCoordinateCoefficient_at t A.tangent.fiberCoordinates b hb _ z hz]
    let p : intrinsicBoundary S := b.symm z
    have hp : p ∈ b.source := b.map_target hz
    have hpc : p.val ∈ c.source := by rwa [hface.1] at hp
    have hsign := BoundaryOrientations.boundary_chart_sign S B hB o q hq s t hs ht c hc b hb hface p hp hpc
    have hval : topCoefficient A.tangent.fiberCoordinates b hb p hp
        (pullbackField B S Subtype.val L (signedField s c hc ω)) =
        signValue (s.sign c hc ⟨p.val, hpc⟩) *
          topCoefficient A.tangent.fiberCoordinates b hb p hp (pullbackField B S Subtype.val L ω) := by
      simp only [topCoefficient, FormPullbackData.pullbackField, signedField, dif_pos hpc, map_smul,
        smul_apply, smul_eq_mul]
    rw [hval, hsign]
    ring
  · have hz' : (⟨x, mem_univ x⟩ : ModelSpace n .euclidean) ∉ b.target := hz
    unfold coordinateCoefficient signedCoordinateCoefficient extendModel
    rw [dite_eq_left (show x ∈ ModelData.modelSet n .euclidean from mem_univ x)]
    rw [dite_eq_left (show x ∈ ModelData.modelSet n .euclidean from mem_univ x)]
    unfold modelCoefficient modelSignedCoefficient
    rw [dite_eq_right hz', dite_eq_right hz', mul_zero]

theorem fullSpace_signed_chart_integral_zero
    (local_stokes : Specs.SmoothManifolds.Integration.LocalStokes.local_stokesType)
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .euclidean M} (C : CotangentBundle S) (s : SignedCharts S)
    (c : ModelChart (n+1) .euclidean M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n)
    (hω : IsRegularField C 1 n ω) (hcompact : IsCompact (sectionSupport ω))
    (hs : sectionSupport ω ⊆ c.source) (η : Field S (n+1))
    (hη : HasExteriorDerivative C ω η) : coordinateIntegral s C.tangent.fiberCoordinates c hc η = 0 := by
  unfold coordinateIntegral
  rw [signedCoefficient_as_unsigned]
  exact fullSpace_chart_integral_zero local_stokes C c hc (signedField s c hc ω)
    (signedField_regular C s c hc ω hω hs)
    (hcompact.of_isClosed_subset isClosed_closure (signedField_support s c hc ω))
    ((signedField_support s c hc ω).trans hs) (signedField s c hc η)
    (signedField_derivative C s c hc ω hω hs η hη)

theorem halfSpace_signed_chart_integral
    (local_stokes : Specs.SmoothManifolds.Integration.LocalStokes.local_stokesType)
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .halfSpace M} (C : CotangentBundle S) (s : SignedCharts S)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n)
    (hω : IsRegularField C 1 n ω) (hcompact : IsCompact (sectionSupport ω))
    (hs : sectionSupport ω ⊆ c.source) (η : Field S (n+1))
    (hη : HasExteriorDerivative C ω η) : coordinateIntegral s C.tangent.fiberCoordinates c hc η =
      ∫ x, LocalStokesData.boundaryCoefficient (chartForm C c hc (signedField s c hc ω)) x := by
  have hξreg := signedField_regular C s c hc ω hω hs
  have hξcomp := hcompact.of_isClosed_subset isClosed_closure (signedField_support s c hc ω)
  have hξsupp := (signedField_support s c hc ω).trans hs
  have hδ := signedField_derivative C s c hc ω hω hs η hη
  unfold coordinateIntegral
  rw [signedCoefficient_as_unsigned, halfSpace_chart_bulk_integral C c hc _ hξreg hξcomp hξsupp _ hδ]
  exact (local_stokes.2.1 n (chartForm C c hc (signedField s c hc ω))
    (chartForm_regular C c hc _ hξreg hξcomp hξsupp)
    (chartForm_compact_support C c hc _ hξcomp hξsupp)).2.2

/-- Stokes for a compact C¹ form whose closed support is contained in one
chart. The boundary integral uses the canonical outward-first orientation. -/
theorem chart_supported_stokes
    (local_stokes : Specs.SmoothManifolds.Integration.LocalStokes.local_stokesType)
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M) (C : CotangentBundle S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (A : CotangentBundle B)
    (hB : IsNaturalBoundary S B) (o : Orientation S) (q : Orientation B)
    (hq : IsInducedOrientation o q)
    (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential B S Subtype.val p (L p))
    (I : CompactTopForm S → ℝ) (J : CompactTopForm B → ℝ)
    (hI : IsIntegral o I) (hJ : IsIntegral q J)
    (ω : Field S n) (hω : IsRegularField C 1 n ω)
    (hcompact : IsCompact (sectionSupport ω))
    (c : ModelChart (n+1) a M) (hc : c ∈ S.smoothStructure.val)
    (hs : sectionSupport ω ⊆ c.source)
    (η : CompactTopForm S) (hη : HasExteriorDerivative C ω η.field)
    (β : CompactTopForm B) (hβ : β.field = pullbackField B S Subtype.val L ω) :
    I η = J β := by
  obtain ⟨s, hsigned, _⟩ := (OrientationResults.signed_charts_equivalence S o.val).mp o.property
  obtain ⟨t, ht, _⟩ := (OrientationResults.signed_charts_equivalence B q.val).mp q.property
  have hηsupp : sectionSupport η.field ⊆ c.source :=
    (ExteriorDerivativeResults.derivative_support C n ω η.field hη).trans hs
  rw [hI.2.2 s hsigned C.tangent.fiberCoordinates c hc η hηsupp]
  cases a with
  | euclidean =>
    rw [fullSpace_signed_chart_integral_zero local_stokes C s c hc ω hω hcompact hs η.field hη]
    exact (empty_boundary_integral S B q J hJ
      (intrinsicBoundary_euclidean S) β).symm
  | halfSpace =>
    rw [halfSpace_signed_chart_integral local_stokes C s c hc ω hω hcompact hs η.field hη]
    by_cases hne : Nonempty {p : intrinsicBoundary S // p.val ∈ c.source}
    · obtain ⟨b, hb, hface⟩ := hB.2 c hc hne
      rw [signed_chart_boundary S C B A hB o q hq s t hsigned ht c hc b hb hface L hL ω]
      have hβsupp : sectionSupport β.field ⊆ b.source := by
        rw [hβ, hface.1]
        exact (GlobalIntegrationResults.boundary_support S B L n ω).1.trans
          (preimage_mono hs)
      simpa only [hβ, coordinateIntegral] using (hJ.2.2 t ht A.tangent.fiberCoordinates b hb β hβsupp).symm
    · have hfaceout (x : Euclidean n) :
          faceEmbedding .halfSpace (⟨x, mem_univ x⟩ : ModelSpace n .euclidean) ∉ c.target := by
        intro hx
        let z := faceEmbedding .halfSpace (⟨x, mem_univ x⟩ : ModelSpace n .euclidean)
        have hpc : c.symm z ∈ c.source := c.map_target hx
        have hp : c.symm z ∈ intrinsicBoundary S := by
          apply (intrinsicBoundary_iff_chart S c hc _ hpc).mpr
          rw [c.right_inv hx]
          change Fin.snoc (α := fun _ : Fin (n+1) => ℝ) x 0 (Fin.last n) = 0
          exact Fin.snoc_last _ _
        exact hne ⟨⟨⟨c.symm z, hp⟩, hpc⟩⟩
      have hcoeff : LocalStokesData.boundaryCoefficient
          (chartForm C c hc (signedField s c hc ω)) = 0 := by
        funext x
        have hz := chartForm_outside C c hc (signedField s c hc ω)
          (faceEmbedding .halfSpace (⟨x, mem_univ x⟩ : ModelSpace n .euclidean)) (hfaceout x)
        change chartForm C c hc (signedField s c hc ω) (Fin.snoc x 0) = 0 at hz
        rw [LocalStokesData.boundaryCoefficient, Fin.insertNth_last', hz]
        simp
      rw [hcoeff]
      simp only [Pi.zero_apply, MeasureTheory.integral_zero]
      symm
      apply integral_zero_field q J hJ β
      funext p
      rw [hβ]
      have hpout : p.val ∉ c.source := fun hp => hne ⟨⟨p, hp⟩⟩
      have hωzero : ω p.val = 0 := by
        by_contra hz
        exact hpout (hs (subset_closure hz))
      simp [FormPullbackData.pullbackField, hωzero]

/-- A smooth partition of the full atlas, retaining smoothness for C¹
localization as well as the closed-support subordination. -/
theorem smooth_chart_partition {d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold d a M) :
    ∃ ρ : {c : ModelChart d a M // c ∈ S.smoothStructure.val} → M → ℝ,
      IsSmoothPartition S.smoothStructure.val ρ ∧
      (∀ i, sectionSupport (ρ i) ⊆ i.val.source) := by
  apply exists_smooth_partition S
    (fun i : {c : ModelChart d a M // c ∈ S.smoothStructure.val} => i.val.source)
    (fun i => i.val.open_source)
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  exact ⟨⟨c, hc⟩, hp⟩

/-- Abstract Stokes from the full local theorem. All sums are finite equalities
of whole intrinsic fields, including at points on the boundary of the support. -/
theorem stokes :
    Specs.SmoothManifolds.Integration.Stokes.stokesType.{u} := by
  have local_stokes := LocalStokesResults.local_stokes
  intro n a M _ S C B A hB o q hq L hL I J hI hJ ω hω hcompact
  classical
  obtain ⟨η, hη, _⟩ := derivative_top_form S C ω hω hcompact
  obtain ⟨β, hβ⟩ := boundary_top_form S C B A hB L hL ω hω hcompact
  refine ⟨η, β, hη.1, hη.2, hβ.1, ?_⟩
  obtain ⟨ρ, hρ, hsub⟩ := smooth_chart_partition S
  let ι := {c : ModelChart (n+1) a M // c ∈ S.smoothStructure.val}
  let w : ι → Field S n := fun i p => ρ i p • ω p
  have hw (i : ι) : IsRegularField C 1 n (w i) :=
    regular_weight C ω hω (ρ i) (hρ.1 i)
  have hcomp (i : ι) : IsCompact (sectionSupport (w i)) :=
    hcompact.of_isClosed_subset isClosed_closure
      (fun p hp => (GlobalIntegrationResults.weight_support S n ω (ρ i) hp).2)
  have hws (i : ι) : sectionSupport (w i) ⊆ i.val.source :=
    fun p hp => hsub i (GlobalIntegrationResults.weight_support S n ω (ρ i) hp).1
  have hd (i : ι) : ∃ δ : CompactTopForm S,
      HasExteriorDerivative C (w i) δ.field ∧ sectionSupport δ.field ⊆ sectionSupport (w i) :=
    (derivative_top_form S C (w i) (hw i) (hcomp i)).exists
  choose δ hδ using hd
  have hb (i : ι) : ∃ γ : CompactTopForm B,
      γ.field = pullbackField B S Subtype.val L (w i) ∧
      IsRegularField A 1 n γ.field ∧
      sectionSupport γ.field ⊆ Subtype.val ⁻¹' sectionSupport (w i) :=
    boundary_top_form S C B A hB L hL (w i) (hw i) (hcomp i)
  choose γ hγ using hb
  obtain ⟨t, _, heω, heη⟩ := derivative_of_partition C ω hω η.field hη.1 hcompact
    ρ hρ (fun i => (δ i).field) (fun i => (hδ i).1)
  have heβ : β.field = ∑ i ∈ t, (γ i).field := by
    calc
      β.field = pullbackField B S Subtype.val L ω := hβ.1
      _ = ∑ i ∈ t, pullbackField B S Subtype.val L (w i) := by
        rw [heω]
        funext p
        simp only [FormPullbackData.pullbackField, Finset.sum_apply, map_sum]
        rfl
      _ = ∑ i ∈ t, (γ i).field := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hγ i).1.symm
  rw [GlobalIntegrationResults.integral_finset_sum hI t δ η heη,
    GlobalIntegrationResults.integral_finset_sum hJ t γ β heβ]
  apply Finset.sum_congr rfl
  intro i _
  exact chart_supported_stokes local_stokes S C B A hB o q hq L hL I J hI hJ
    (w i) (hw i) (hcomp i) i.val i.property (hws i) (δ i) (hδ i).1 (γ i) (hγ i).1

end SmoothManifolds.StokesResults
