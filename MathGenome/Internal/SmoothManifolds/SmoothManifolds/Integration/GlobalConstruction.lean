import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.GlobalConstruction
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.LocalSigned
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped Classical Topology BigOperators
namespace SmoothManifolds.GlobalConstructionResults
open ModelData AtlasData TangentData TangentBundleData ExteriorData FormPullbackData
  OrientationData LocalIntegrationData Set MeasureTheory
universe u v

theorem weight_support {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (ω : Field S n) (ρ : M → ℝ) :
    sectionSupport (fun p => ρ p • ω p) ⊆ sectionSupport ρ ∩ sectionSupport ω := by
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
    (fun _ hp => (weight_support α.field ρ hp).2)

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

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Evaluation, including zero extension and variable chart signs, is linear. -/
def signedCoefficientLinear (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (x : Euclidean n) :
    Field S n →ₗ[ℝ] ℝ where
  toFun ω := signedCoordinateCoefficient s K c hc ω x
  map_add' α β := by
    unfold signedCoordinateCoefficient extendModel modelSignedCoefficient
    split_ifs <;> simp [topCoefficient, map_add, mul_add]
  map_smul' r α := by
    unfold signedCoordinateCoefficient extendModel modelSignedCoefficient
    split_ifs <;> simp [topCoefficient, map_smul] <;> ring

theorem coordinate_zero (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    coordinateIntegral s K c hc (0 : Field S n) = 0 := by
  have h : signedCoordinateCoefficient s K c hc (0 : Field S n) = 0 :=
    funext (fun x => (signedCoefficientLinear s K c hc x).map_zero)
  simp [coordinateIntegral, h]

theorem coordinate_add (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (α β : CompactTopForm S)
    (hα : sectionSupport α.field ⊆ c.source) (hβ : sectionSupport β.field ⊆ c.source) :
    coordinateIntegral s K c hc (α.field + β.field) =
      coordinateIntegral s K c hc α.field + coordinateIntegral s K c hc β.field := by
  have h : signedCoordinateCoefficient s K c hc (α.field + β.field) =
      fun x => signedCoordinateCoefficient s K c hc α.field x +
        signedCoordinateCoefficient s K c hc β.field x :=
    funext (fun x => (signedCoefficientLinear s K c hc x).map_add _ _)
  exact (congrArg (fun f => ∫ x, f x) h).trans
    (integral_add (LocalIntegrationResults.integrable S s K c hc α hα)
      (LocalIntegrationResults.integrable S s K c hc β hβ))

theorem coordinate_smul (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (r : ℝ) (α : Field S n) :
    coordinateIntegral s K c hc (r • α) = r * coordinateIntegral s K c hc α := by
  have h : signedCoordinateCoefficient s K c hc (r • α) =
      fun x => r * signedCoordinateCoefficient s K c hc α x :=
    funext (fun x => (signedCoefficientLinear s K c hc x).map_smul r α)
  exact (congrArg (fun f => ∫ x, f x) h).trans (integral_const_mul r _)

theorem coordinate_sum (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    {ι : Type v} (t : Finset ι) (ω : ι → CompactTopForm S)
    (hω : ∀ i ∈ t, sectionSupport (ω i).field ⊆ c.source) :
    coordinateIntegral s K c hc (∑ i ∈ t, (ω i).field) =
      ∑ i ∈ t, coordinateIntegral s K c hc (ω i).field := by
  have h : signedCoordinateCoefficient s K c hc (∑ i ∈ t, (ω i).field) =
      fun x => ∑ i ∈ t, signedCoordinateCoefficient s K c hc (ω i).field x :=
    funext (fun x => map_sum (signedCoefficientLinear s K c hc x) _ t)
  exact (congrArg (fun f => ∫ x, f x) h).trans
    (integral_finsetSum t (fun i hi => LocalIntegrationResults.integrable S s K c hc (ω i) (hω i hi)))

/-- A fixed subordinate partition exists without any nonemptiness assumption. -/
theorem chart_partition (S : SmoothManifold n a M) :
    ∃ ρ : {c : ModelChart n a M // c ∈ S.smoothStructure.val} → M → ℝ,
      (∀ i, Continuous (ρ i)) ∧ LocallyFinite (fun i => sectionSupport (ρ i)) ∧
      (∀ i, sectionSupport (ρ i) ⊆ i.val.source) ∧ ∀ p, ∑ᶠ i, ρ i p = 1 := by
  let U : {c : ModelChart n a M // c ∈ S.smoothStructure.val} → Set M := fun c => c.val.source
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition S U (fun c => c.val.open_source) (by
    intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    exact ⟨⟨c, hc⟩, hp⟩)
  refine ⟨ρ, ?_, hρ.2.2.1, hsub, hρ.2.2.2⟩
  intro i
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ((scalarContDiffAt_iff (⊤ : ℕ∞) S.smoothStructure.val (ρ i) p).mp (hρ.1 i p)).1

section FixedPartition
variable {ι : Type v} (c : ι → ModelChart n a M)
  (hc : ∀ i, c i ∈ S.smoothStructure.val) (ρ : ι → M → ℝ)
  (hcont : ∀ i, Continuous (ρ i))
  (hlf : LocallyFinite (fun i => sectionSupport (ρ i)))
  (hsub : ∀ i, sectionSupport (ρ i) ⊆ (c i).source)
  (hone : ∀ p, ∑ᶠ i, ρ i p = 1)

include hlf hone in
/-- One finite index set controls a compact form on the entire manifold. -/
theorem finite_decomposition (ω : CompactTopForm S) :
    ∃ t : Finset ι,
      (∀ i ∉ t, (weightForm (ρ i) (hcont i) ω).field = 0) ∧
      ω.field = ∑ i ∈ t, (weightForm (ρ i) (hcont i) ω).field := by
  classical
  have hfin := hlf.finite_nonempty_inter_compact ω.compact_support
  let t := hfin.toFinset
  have ht (p : M) (hp : ω.field p ≠ 0) :
      Function.support (fun i => ρ i p) ⊆ t := by
    intro i hi
    exact hfin.mem_toFinset.mpr ⟨p, subset_closure hi, subset_closure hp⟩
  refine ⟨t, ?_, ?_⟩
  · intro i hi
    funext p
    by_cases hp : ω.field p = 0
    · simp [weightForm, hp]
    · have hz : ρ i p = 0 := by
        by_contra hz
        exact hi (ht p hp hz)
      simp [weightForm, hz]
  · funext p
    simp only [Finset.sum_apply, weightForm]
    by_cases hp : ω.field p = 0
    · simp [hp]
    · have hsum : ∑ i ∈ t, ρ i p = 1 := by
        rw [← finsum_eq_sum_of_support_subset _ (ht p hp)]
        exact hone p
      rw [← Finset.sum_smul, hsum, one_smul]

def partitionIntegral (s : SignedCharts S) (K : FiberCoordinates S)
    (ω : CompactTopForm S) : ℝ :=
  ∑ᶠ i, coordinateIntegral s K (c i) (hc i) (weightForm (ρ i) (hcont i) ω).field

 include hlf hone in
theorem partition_terms_finite (s : SignedCharts S) (K : FiberCoordinates S)
    (ω : CompactTopForm S) :
    Function.HasFiniteSupport (fun i =>
      coordinateIntegral s K (c i) (hc i) (weightForm (ρ i) (hcont i) ω).field) := by
  obtain ⟨t, ht, _⟩ := finite_decomposition ρ hcont hlf hone ω
  apply t.finite_toSet.subset
  intro i hi
  by_contra hit
  exact hi (by
    change coordinateIntegral s K (c i) (hc i) (weightForm (ρ i) (hcont i) ω).field = 0
    rw [ht i hit, coordinate_zero])

include hsub in
theorem weighted_chart_support (ω : CompactTopForm S) (i : ι) :
    sectionSupport (weightForm (ρ i) (hcont i) ω).field ⊆ (c i).source :=
  fun _ hp => hsub i (weight_support ω.field (ρ i) hp).1

include hlf hsub hone in
theorem partition_add (s : SignedCharts S) (K : FiberCoordinates S)
    (α β γ : CompactTopForm S) (hγ : γ.field = α.field + β.field) :
    partitionIntegral c hc ρ hcont s K γ =
      partitionIntegral c hc ρ hcont s K α + partitionIntegral c hc ρ hcont s K β := by
  unfold partitionIntegral
  have heq (i : ι) :
      (weightForm (ρ i) (hcont i) γ).field =
        (weightForm (ρ i) (hcont i) α).field + (weightForm (ρ i) (hcont i) β).field := by
    funext p
    simp [weightForm, hγ, smul_add]
  simp_rw [heq, coordinate_add s K _ _ _ _
    (weighted_chart_support c ρ hcont hsub α _) (weighted_chart_support c ρ hcont hsub β _)]
  exact finsum_add_distrib (partition_terms_finite c hc ρ hcont hlf hone s K α)
    (partition_terms_finite c hc ρ hcont hlf hone s K β)

theorem partition_smul (s : SignedCharts S) (K : FiberCoordinates S)
    (r : ℝ) (α β : CompactTopForm S) (hβ : β.field = r • α.field) :
    partitionIntegral c hc ρ hcont s K β = r * partitionIntegral c hc ρ hcont s K α := by
  unfold partitionIntegral
  have heq (i : ι) : (weightForm (ρ i) (hcont i) β).field =
      r • (weightForm (ρ i) (hcont i) α).field := by
    funext p
    simp only [weightForm, hβ, Pi.smul_apply]
    exact smul_comm _ _ _
  simp_rw [heq, coordinate_smul]
  exact (mul_finsum _ r).symm

include hlf hsub hone in
/-- A form supported in any one chart is recovered by its finitely many
partition terms; local chart independence transports each term into that chart. -/
theorem partition_coordinate (o : Orientation S) (s : SignedCharts S)
    (hs : RepresentsSignedCharts o.val s) (K L : FiberCoordinates S)
    (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (ω : CompactTopForm S) (hω : sectionSupport ω.field ⊆ d.source) :
    partitionIntegral c hc ρ hcont s K ω = coordinateIntegral s L d hd ω.field := by
  obtain ⟨t, ht, hsum⟩ := finite_decomposition ρ hcont hlf hone ω
  have hωd (i : ι) : sectionSupport (weightForm (ρ i) (hcont i) ω).field ⊆ d.source :=
    fun _ hp => hω (weight_support ω.field (ρ i) hp).2
  unfold partitionIntegral
  rw [finsum_eq_sum_of_support_subset _ (s := t) (by
    intro i hi
    by_contra hit
    exact hi (by
      change coordinateIntegral s K (c i) (hc i) (weightForm (ρ i) (hcont i) ω).field = 0
      rw [ht i hit, coordinate_zero]))]
  calc
    (∑ i ∈ t, coordinateIntegral s K (c i) (hc i) (weightForm (ρ i) (hcont i) ω).field) =
        ∑ i ∈ t, coordinateIntegral s L d hd (weightForm (ρ i) (hcont i) ω).field := by
      apply Finset.sum_congr rfl
      intro i _
      exact LocalIntegrationResults.chart_independence S o s hs K L (c i) d (hc i) hd
        (weightForm (ρ i) (hcont i) ω) (weighted_chart_support c ρ hcont hsub ω i) (hωd i)
    _ = coordinateIntegral s L d hd (∑ i ∈ t, (weightForm (ρ i) (hcont i) ω).field) :=
      (coordinate_sum s L d hd t _ (fun i _ => hωd i)).symm
    _ = coordinateIntegral s L d hd ω.field := by rw [← hsum]

end FixedPartition

/-- Existence of the integral, with no extra partition or coordinate hypotheses. -/
theorem exists_integral : Specs.SmoothManifolds.Integration.GlobalConstruction.exists_integralType.{u} := by
  intro n a M _ S o
  obtain ⟨s, hs, huniq⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨ρ, hcont, hlf, hsub, hone⟩ := chart_partition S
  let c : {c : ModelChart n a M // c ∈ S.smoothStructure.val} → ModelChart n a M := Subtype.val
  have hc : ∀ i, c i ∈ S.smoothStructure.val := fun i => i.property
  refine ⟨partitionIntegral c hc ρ hcont s K, ?_, ?_, ?_⟩
  · exact partition_add c hc ρ hcont hlf hsub hone s K
  · exact partition_smul c hc ρ hcont s K
  · intro t ht L d hd ω hω
    have heq : t = s := huniq t ht
    subst t
    exact partition_coordinate c hc ρ hcont hlf hsub hone o s hs K L d hd ω hω

end SmoothManifolds.GlobalConstructionResults
