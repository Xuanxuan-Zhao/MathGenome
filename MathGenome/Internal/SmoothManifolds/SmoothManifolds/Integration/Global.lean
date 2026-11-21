import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.LocalSigned
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.GlobalConstruction
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.DiffeomorphismLocal
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.ProductsAndSigns
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.GlobalIntegrationResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  ExteriorData FormPullbackData OrientationData OrientationProductData
  LocalIntegrationData GlobalIntegrationData BoundaryData Set
universe u v

/-- Closed supports of weighted sections lie in both closed supports. -/
theorem weight_support : Specs.SmoothManifolds.Integration.Global.weight_supportType.{u} := by
  intro n a M _ S k ω ρ
  apply closure_minimal
  · intro p hp
    exact ⟨subset_closure (fun h => hp (by simp [h])),
      subset_closure (fun h => hp (by simp [h]))⟩
  · exact isClosed_closure.inter isClosed_closure

/-- Coordinate evaluation is linear in the exterior covector. -/
theorem topCoefficient_add {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (α β : Field S n) :
    topCoefficient K c hc p hp (α + β) =
      topCoefficient K c hc p hp α + topCoefficient K c hc p hp β := by
  simp [topCoefficient, map_add]

theorem topCoefficient_weight {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (ρ : M → ℝ) (α : Field S n) :
    topCoefficient K c hc p hp (fun q => ρ q • α q) =
      ρ p * topCoefficient K c hc p hp α := by
  simp [topCoefficient, map_smul]

/-- Addition in the original bundled space, with compactness of the closed
support proved using the union of the two original compact supports. -/
def addForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (α β : CompactTopForm S) : CompactTopForm S where
  field := α.field + β.field
  continuous := by
    intro K c hc
    apply Continuous.congr ((α.continuous K c hc).add (β.continuous K c hc))
    intro p
    exact (topCoefficient_add K c hc p.val p.property α.field β.field).symm
  compact_support := by
    apply (α.compact_support.union β.compact_support).of_isClosed_subset isClosed_closure
    apply closure_minimal
    · intro p hp
      by_cases hα : α.field p = 0
      · right
        apply subset_closure
        simpa [hα] using hp
      · exact Or.inl (subset_closure hα)
    · exact isClosed_closure.union isClosed_closure

/-- Continuous weights require no compactness of their own supports. -/
def weightForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (ρ : M → ℝ) (hρ : Continuous ρ)
    (α : CompactTopForm S) : CompactTopForm S where
  field := fun p => ρ p • α.field p
  continuous := by
    intro K c hc
    apply Continuous.congr ((hρ.comp continuous_subtype_val).mul (α.continuous K c hc))
    intro p
    exact (topCoefficient_weight K c hc p.val p.property ρ α.field).symm
  compact_support := α.compact_support.of_isClosed_subset isClosed_closure
    (fun _ hp => (weight_support S n α.field ρ hp).2)

theorem algebra : Specs.SmoothManifolds.Integration.Global.algebraType.{u} := by
  intro n a M _ S α β
  exact ⟨⟨addForm α β, rfl⟩, fun ρ hρ => ⟨weightForm ρ hρ α, rfl⟩⟩

/-- Local finiteness and compactness give one finite set for the whole support. -/
theorem finite_localizers :
    Specs.SmoothManifolds.Integration.Global.finite_localizersType.{u, v} := by
  intro n a M _ S ι ρ hρ ω
  exact hρ.finite_nonempty_inter_compact ω.compact_support

/-- Outside the inverse image of the closed support the fiber map takes zero to
zero on a neighborhood. No properness hypothesis is used for this inclusion. -/
theorem pullback_support : Specs.SmoothManifolds.Integration.Global.pullback_supportType.{u} := by
  intro n m a b M N _ _ S T f hf L k ω
  apply closure_minimal
  · intro p hp
    apply subset_closure
    intro hz
    exact hp (by simp [pullbackField, hz])
  · exact isClosed_closure.preimage hf

/-- Diffeomorphisms are proper via their actual underlying homeomorphisms. -/
theorem diffeomorphism_support :
    Specs.SmoothManifolds.Integration.Global.diffeomorphism_supportType.{u} := by
  intro n m a b M N _ _ S T F L k ω hω
  exact (F.toHomeomorph.isCompact_preimage.mpr hω).of_isClosed_subset
    isClosed_closure (pullback_support S T F.toEquiv F.toHomeomorph.continuous L k ω)

/-- Closed embedded restrictions preserve compact support. -/
theorem closed_embedding_support :
    Specs.SmoothManifolds.Integration.Global.closed_embedding_supportType.{u} := by
  intro n m a b M N _ _ S T i hi L k ω
  have hs := pullback_support S T i hi.continuous L k ω
  exact ⟨hs, fun hω => (hi.isCompact_preimage hω).of_isClosed_subset isClosed_closure hs⟩

/-- The intrinsic boundary is closed in the original manifold topology. -/
theorem boundary_support : Specs.SmoothManifolds.Integration.Global.boundary_supportType.{u} := by
  intro n a M _ S B L k ω
  exact closed_embedding_support B S Subtype.val
    (isClosed_intrinsicBoundary S).isClosedEmbedding_subtypeVal L k ω

/-- One finite set decomposes the whole section, not merely its values at one
point. Terms outside this set vanish identically. -/
theorem localization_decomposition {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v}
    (c : ι → ModelChart n a M) (ρ : ι → M → ℝ) (ω : CompactTopForm S)
    (hρ : IsLocalization c ρ ω) :
    ∃ t : Finset ι,
      (∀ i ∉ t, (fun p => ρ i p • ω.field p) = (0 : Field S n)) ∧
      ω.field = ∑ i ∈ t, (fun p => ρ i p • ω.field p) := by
  classical
  have hfin := finite_localizers S ρ hρ.2.1 ω
  let t := hfin.toFinset
  have ht (p : M) (hp : ω.field p ≠ 0) :
      Function.support (fun i => ρ i p) ⊆ t := by
    intro i hi
    exact hfin.mem_toFinset.mpr ⟨p, subset_closure hi, subset_closure hp⟩
  refine ⟨t, ?_, ?_⟩
  · intro i hi
    funext p
    by_cases hp : ω.field p = 0
    · simp [hp]
    · have hz : ρ i p = 0 := by
        by_contra hz
        exact hi (ht p hp hz)
      simp [hz]
  · funext p
    simp only [Finset.sum_apply]
    by_cases hp : ω.field p = 0
    · simp [hp]
    · obtain ⟨V, _, hV, hsum⟩ := hρ.2.2.2
      have hsum' : ∑ i ∈ t, ρ i p = 1 := by
        rw [← finsum_eq_sum_of_support_subset _ (ht p hp)]
        exact hsum p (hV (subset_closure hp))
      rw [← Finset.sum_smul, hsum', one_smul]

/-- The zero section in the original bundled space. -/
def zeroForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : CompactTopForm S where
  field := 0
  continuous := by
    intro K c hc
    simpa [topCoefficient] using (continuous_const : Continuous (fun _ : c.source => (0 : ℝ)))
  compact_support := by simp

/-- Finite sums exist without adding a parallel type of top forms. -/
theorem exists_sumForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} (t : Finset ι) (ω : ι → CompactTopForm S) :
    ∃ ζ : CompactTopForm S, ζ.field = ∑ i ∈ t, (ω i).field := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨zeroForm S, by simp [zeroForm]⟩
  | @insert i t hi ih =>
    obtain ⟨ζ, hζ⟩ := ih
    exact ⟨addForm (ω i) ζ, by simp [addForm, hζ, hi]⟩

/-- The explicit linearity clauses imply the usual finite-sum formula. -/
theorem integral_finset_sum {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {o : Orientation S} {I : CompactTopForm S → ℝ}
    (hI : IsIntegral o I) {ι : Type v} (t : Finset ι) (ω : ι → CompactTopForm S)
    (ζ : CompactTopForm S) (hζ : ζ.field = ∑ i ∈ t, (ω i).field) :
    I ζ = ∑ i ∈ t, I (ω i) := by
  classical
  induction t using Finset.induction_on generalizing ζ with
  | empty =>
    have hz : ζ.field = 0 := by simpa using hζ
    have hh := hI.2.1 0 ζ ζ (by rw [hz]; simp)
    simpa using hh
  | @insert i t hi ih =>
    obtain ⟨β, hβ⟩ := exists_sumForm t ω
    have hζ' : ζ.field = (ω i).field + β.field := by simpa [hi, hβ] using hζ
    rw [hI.1 (ω i) β ζ hζ', ih β hβ, Finset.sum_insert hi]

/-- Localization follows for every linear coordinate-compatible integral, and
uses a single finite set containing all terms that can meet the support. -/
theorem localization : Specs.SmoothManifolds.Integration.Global.localizationType.{u, v} := by
  intro n a M _ S o I hI s hs K ι c hc ρ ω hρ
  obtain ⟨t, ht, hω⟩ := localization_decomposition c ρ ω hρ
  let ζ : ι → CompactTopForm S := fun i => weightForm (ρ i) (hρ.1 i) ω
  have hζ (i : ι) : sectionSupport (ζ i).field ⊆ (c i).source :=
    fun p hp => hρ.2.2.1 i (weight_support S n ω.field (ρ i) hp).1
  have hsum : I ω = ∑ i ∈ t, I (ζ i) := integral_finset_sum hI t ζ ω hω
  rw [hsum]
  have heq (i : ι) : I (ζ i) = coordinateIntegral s K (c i) (hc i) (ζ i).field :=
    hI.2.2 s hs K (c i) (hc i) (ζ i) (hζ i)
  simp_rw [heq]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hit
  apply hi
  change coordinateIntegral s K (c i) (hc i) (ζ i).field = 0
  rw [show (ζ i).field = 0 from ht i hit]
  simp [coordinateIntegral, signedCoordinateCoefficient, extendModel,
    modelSignedCoefficient, topCoefficient]

/-- A global diffeomorphism supplies the local diffeomorphism interface, including
at a true boundary point. -/
theorem diffeomorphism_isLocal {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val) :
    IsLocalDiffeomorphism S T F.toEquiv := by
  intro p
  exact ⟨F.toHomeomorph.toOpenPartialHomeomorph, Set.mem_univ p,
    fun _ _ => rfl, fun x _ => F.contDiff_toFun x, fun y _ => F.contDiff_invFun y⟩

theorem component_sign : Specs.SmoothManifolds.Integration.Global.component_signType.{u} := by
  intro n a b M N _ _ S T F o q E hE
  have h := (OrientationProducts.local_sign S T F.toEquiv
    (diffeomorphism_isLocal S T F) o q E hE).1
  exact ⟨h, fun p x hx =>
    h.apply_eq_of_isPreconnected isPreconnected_connectedComponent hx mem_connectedComponent⟩

/-- A genuine smooth subordinate chart partition is in particular an admissible
continuous localization, even on an empty manifold. -/
theorem exists_chart_localization {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (ω : CompactTopForm S) :
    ∃ ρ : {c : ModelChart n a M // c ∈ S.smoothStructure.val} → M → ℝ,
      IsLocalization (fun c => c.val) ρ ω := by
  let U : {c : ModelChart n a M // c ∈ S.smoothStructure.val} → Set M := fun c => c.val.source
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition S U (fun c => c.val.open_source) (by
    intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    exact ⟨⟨c, hc⟩, hp⟩)
  refine ⟨ρ, ?_, hρ.2.2.1, hsub, univ, isOpen_univ, subset_univ _, fun p _ => hρ.2.2.2 p⟩
  intro i
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ((scalarContDiffAt_iff (⊤ : ℕ∞) S.smoothStructure.val (ρ i) p).mp (hρ.1 i p)).1

/-- The linear coordinate-compatible functional, if it exists, is unique. -/
theorem integral_unique {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S)
    (I J : CompactTopForm S → ℝ) (hI : IsIntegral o I) (hJ : IsIntegral o J) : I = J := by
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  funext ω
  obtain ⟨ρ, hρ⟩ := exists_chart_localization S ω
  rw [localization S o I hI s hs K (fun c => c.val) (fun c => c.property) ρ ω hρ,
    localization S o J hJ s hs K (fun c => c.val) (fun c => c.property) ρ ω hρ]

/-- Signed evaluation has finite support on every compactly supported zero-form. -/
theorem zero_integrand_finite {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (o : Orientation S) (ω : CompactTopForm S) :
    Function.HasFiniteSupport (fun p => zeroSign o p * zeroCoefficient ω.field p) := by
  haveI := LocalIntegrationResults.zero_manifold_discrete S
  apply ω.compact_support.finite_of_discrete.subset
  intro p hp
  apply subset_closure
  intro hz
  exact hp (by simp [zeroCoefficient, hz])

/-- The finite signed sum itself satisfies the global integral axioms in dimension
zero; no global existence theorem is needed for this check. -/
theorem zero_integral_axioms {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S) :
    IsIntegral o (fun ω => zeroIntegral o ω.field) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α β γ hγ
    unfold zeroIntegral
    calc
      (∑ᶠ p, zeroSign o p * zeroCoefficient γ.field p) =
          ∑ᶠ p, (zeroSign o p * zeroCoefficient α.field p +
            zeroSign o p * zeroCoefficient β.field p) := by
        apply finsum_congr
        intro p
        simp [zeroCoefficient, hγ, mul_add]
      _ = _ := finsum_add_distrib (zero_integrand_finite o α) (zero_integrand_finite o β)
  · intro r α β hβ
    unfold zeroIntegral
    rw [mul_finsum]
    apply finsum_congr
    intro p
    simp only [zeroCoefficient, hβ, Pi.smul_apply, map_smul, smul_eq_mul]
    ring
  · intro s hs K c hc ω hω
    exact (LocalIntegrationResults.zero_coordinate S o s hs K c hc ω hω).1.symm

theorem zero_dimension : Specs.SmoothManifolds.Integration.Global.zero_dimensionType.{u} := by
  intro a M _ S o I hI ω
  exact congrFun (integral_unique S o I (fun α => zeroIntegral o α.field) hI
    (zero_integral_axioms S o)) ω

/-- Opposite determinant rays assign opposite signs to every actual coordinate
frame, also in degree zero. -/
theorem opposite_chart_signs {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (o q : Orientation S)
    (hopp : ∀ p, q.val p = -o.val p) (s t : SignedCharts S)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts q.val t)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) : signValue (t.sign c hc p) = -signValue (s.sign c hc p) := by
  have hne : s.sign c hc p ≠ t.sign c hc p := by
    intro heq
    obtain ⟨hv, hr⟩ := hs K c hc p
    have ht' := ht K c hc p
    rw [← heq] at ht'
    obtain ⟨hw, hq⟩ := ht'
    exact Module.Ray.ne_neg_self (o.val p.val) (hr.symm.trans (hq.trans (hopp p.val)))
  cases h₁ : s.sign c hc p <;> cases h₂ : t.sign c hc p <;>
    simp_all [signValue]

theorem opposite_coordinate_integrals {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (o q : Orientation S)
    (hopp : ∀ p, q.val p = -o.val p) (s t : SignedCharts S)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts q.val t)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S n) : coordinateIntegral t K c hc ω = -coordinateIntegral s K c hc ω := by
  have heq : signedCoordinateCoefficient t K c hc ω =
      fun x => -signedCoordinateCoefficient s K c hc ω x := by
    funext x
    unfold signedCoordinateCoefficient extendModel modelSignedCoefficient
    split_ifs with hm hx
    · rw [opposite_chart_signs o q hopp s t hs ht K c hc]
      exact neg_mul _ _
    · simp
    · simp
  simp only [coordinateIntegral, heq, MeasureTheory.integral_neg]

theorem reversal : Specs.SmoothManifolds.Integration.Global.reversalType.{u} := by
  intro n a M _ S o q hopp I J hI hJ ω
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨t, ht, _⟩ := LocalIntegrationResults.orientation_signs S q
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨ρ, hρ⟩ := exists_chart_localization S ω
  rw [localization S q J hJ t ht K (fun c => c.val) (fun c => c.property) ρ ω hρ,
    localization S o I hI s hs K (fun c => c.val) (fun c => c.property) ρ ω hρ]
  simp_rw [opposite_coordinate_integrals o q hopp s t hs ht K]
  exact finsum_neg_distrib _

/-- The upstream construction and uniqueness give the full existence statement. -/
theorem exists_integral : Specs.SmoothManifolds.Integration.Global.exists_integralType.{u} := by
  intro n a M _ S o
  obtain ⟨I, hI⟩ := GlobalConstructionResults.exists_integral S o
  exact ⟨I, hI, fun J hJ => integral_unique S o J I hJ hI⟩

/-- Pullback of the original compact continuous top form. -/
def pullbackForm {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p))
    (hE : ∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap)
    (η : CompactTopForm T) : CompactTopForm S where
  field := pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η.field
  continuous := DiffeomorphismLocalResults.continuous_pullback S T F E hE η
  compact_support := diffeomorphism_support S T F (fun p => (E p).toLinearMap)
    n η.field η.compact_support

theorem diffeomorphism_form : Specs.SmoothManifolds.Integration.Global.diffeomorphism_formType.{u} := by
  intro n a b M N _ _ S T F E hE η
  exact ⟨pullbackForm S T F E hE η, rfl⟩

/-- The differential witnesses in substitution are supplied by the original
smooth diffeomorphism, in every dimension and for both model kinds. -/
theorem diffeomorphism_differential {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val) :
    ∃! E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p),
      ∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap :=
  OrientationProducts.local_differential S T F.toEquiv (diffeomorphism_isLocal S T F)

/-- A continuous partition subordinate to an arbitrary open cover. -/
theorem continuous_partition {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) {ι : Type v}
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ p, ∃ i, p ∈ U i) :
    ∃ ρ : ι → M → ℝ, (∀ i, Continuous (ρ i)) ∧
      LocallyFinite (fun i => sectionSupport (ρ i)) ∧
      (∀ i, sectionSupport (ρ i) ⊆ U i) ∧ ∀ p, ∑ᶠ i, ρ i p = 1 := by
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition S U hU hcover
  refine ⟨ρ, ?_, hρ.2.2.1, hsub, hρ.2.2.2⟩
  intro i
  exact continuous_iff_continuousAt.mpr (fun p =>
    ((scalarContDiffAt_iff (⊤ : ℕ∞) S.smoothStructure.val (ρ i) p).mp (hρ.1 i p)).1)

/-- Localize in intersections of target charts and images of source charts.
The same finite decomposition then works on both manifolds, even when their
model kinds differ, and retains the sign inside the target integral. -/
theorem substitution : Specs.SmoothManifolds.Integration.Global.substitutionType.{u} := by
  intro n a b M N _ _ S T F o q E hE I J hI hJ η ξ hξ
  let r : N → ℝ := fun y => signValue (orientationSign o q E (F.toEquiv.symm y))
  have hr : Continuous r :=
    (((component_sign S T F o q E hE).1.comp signValue).continuous).comp
      F.toHomeomorph.symm.continuous
  let θ := weightForm r hr η
  refine ⟨θ, rfl, ?_⟩
  let ι := {c : ModelChart n a M // c ∈ S.smoothStructure.val} ×
    {d : ModelChart n b N // d ∈ T.smoothStructure.val}
  let c : ι → ModelChart n a M := fun i => i.1.val
  let d : ι → ModelChart n b N := fun i => i.2.val
  let U : ι → Set N := fun i => (F.toEquiv.symm ⁻¹' (c i).source) ∩ (d i).source
  have hU : ∀ i, IsOpen (U i) := fun i =>
    ((c i).open_source.preimage F.toHomeomorph.symm.continuous).inter (d i).open_source
  have hcover : ∀ y, ∃ i, y ∈ U i := by
    intro y
    obtain ⟨c', hc', hp⟩ := S.smoothStructure.property.1.1 (F.toEquiv.symm y)
    obtain ⟨d', hd', hy⟩ := T.smoothStructure.property.1.1 y
    exact ⟨(⟨c', hc'⟩, ⟨d', hd'⟩), hp, hy⟩
  obtain ⟨ρ, hcont, hlf, hsub, hone⟩ := continuous_partition T U hU hcover
  have hloc : IsLocalization d ρ η :=
    ⟨hcont, hlf, fun i y hy => (hsub i hy).2,
      univ, isOpen_univ, subset_univ _, fun y _ => hone y⟩
  obtain ⟨t, _, hsum⟩ := localization_decomposition d ρ η hloc
  let ζ : ι → CompactTopForm T := fun i => weightForm (ρ i) (hcont i) η
  let χ : ι → CompactTopForm S := fun i => pullbackForm S T F E hE (ζ i)
  let τ : ι → CompactTopForm T := fun i => weightForm r hr (ζ i)
  have hζ (i : ι) : sectionSupport (ζ i).field ⊆ U i :=
    fun y hy => hsub i (weight_support T n η.field (ρ i) hy).1
  have hχ (i : ι) : sectionSupport (χ i).field ⊆ (c i).source := by
    intro p hp
    have hpre := pullback_support S T F.toEquiv F.toHomeomorph.continuous
      (fun p => (E p).toLinearMap) n (ζ i).field hp
    simpa only [mem_preimage, Equiv.symm_apply_apply] using (hζ i hpre).1
  have hτ (i : ι) : sectionSupport (τ i).field ⊆ (d i).source :=
    fun y hy => (hζ i (weight_support T n (ζ i).field r hy).2).2
  have hξsum : ξ.field = ∑ i ∈ t, (χ i).field := by
    rw [hξ]
    rw [hsum]
    funext p
    simp only [pullbackField, Finset.sum_apply, map_sum]
    rfl
  have hθsum : θ.field = ∑ i ∈ t, (τ i).field := by
    change (fun y => r y • η.field y) = _
    rw [hsum]
    funext y
    simp only [Finset.sum_apply, Finset.smul_sum]
    rfl
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨s', hs', _⟩ := LocalIntegrationResults.orientation_signs T q
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨L⟩ := TangentBundle.fiberCoordinates_exists T
  rw [integral_finset_sum hI t χ ξ hξsum, integral_finset_sum hJ t τ θ hθsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hI.2.2 s hs K (c i) i.1.property (χ i) (hχ i),
    hJ.2.2 s' hs' L (d i) i.2.property (τ i) (hτ i)]
  exact DiffeomorphismLocalResults.coordinate_naturality S T F E hE (ζ i) o q s s'
    hs hs' K L (c i) (d i) i.1.property i.2.property (hχ i)
      (fun y hy => (hζ i hy).2)

/-- Constant preservation or reversal sign specializes componentwise substitution. -/
theorem constant_sign_substitution :
    Specs.SmoothManifolds.Integration.Global.constant_sign_substitutionType.{u} := by
  intro n a b M N _ _ S T F o q E hE ε hε I J hI hJ η ξ hξ
  obtain ⟨θ, hθ, heq⟩ := substitution S T F o q E hE I J hI hJ η ξ hξ
  rw [heq]
  apply hJ.2.1 (signValue ε) η θ
  rw [hθ]
  funext y
  simp only [hε, Pi.smul_apply]

/-- The zero-dimensional integral is literally a finite sum over its support. -/
theorem zero_finite_sum : Specs.SmoothManifolds.Integration.Global.zero_finite_sumType.{u} := by
  intro a M _ S o I hI ω
  obtain ⟨h, hh⟩ := LocalIntegrationResults.zero_finite_sum S o ω
  exact ⟨h, (zero_dimension S o I hI ω).trans hh⟩

end SmoothManifolds.GlobalIntegrationResults
