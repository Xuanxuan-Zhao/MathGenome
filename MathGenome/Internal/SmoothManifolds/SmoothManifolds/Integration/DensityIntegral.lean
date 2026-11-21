import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.DensityIntegral
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.DensityCharts
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Tensors

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Topology BigOperators
namespace SmoothManifolds.DensityIntegralResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  OrientationData MetricVolumeData DensityIntegrationData Set MeasureTheory
universe u v
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- The topology of the base is the manifold's given Hausdorff topology. -/
private theorem baseT2 (S : SmoothManifold n a M) : T2Space M :=
  S.topologicalManifold.hausdorff

 theorem support_add_subset (ρ σ : DensityField S) :
    sectionSupport (ρ + σ) ⊆ sectionSupport ρ ∪ sectionSupport σ := by
  apply closure_minimal
  · intro p hp
    by_contra hn
    have hr : ρ p = 0 := not_not.mp (fun h => hn (Or.inl (subset_closure h)))
    have hs : σ p = 0 := not_not.mp (fun h => hn (Or.inr (subset_closure h)))
    exact hp (by simp [hr, hs])
  · exact isClosed_closure.union isClosed_closure

 theorem support_weight_subset (f : M → ℝ) (ρ : DensityField S) :
    sectionSupport (fun p => f p • ρ p) ⊆ sectionSupport f ∩ sectionSupport ρ := by
  apply closure_minimal
  · intro p hp
    exact ⟨subset_closure (fun h => hp (by simp [h])),
      subset_closure (fun h => hp (by simp [h]))⟩
  · exact isClosed_closure.inter isClosed_closure

 def compactZero (S : SmoothManifold n a M) : CompactDensity S where
  field := 0
  continuous := by
    intro K c hc
    simpa using (continuous_const : Continuous (fun _ : c.source => (0 : ℝ)))
  compact_support := by simpa [sectionSupport] using isCompact_empty (X := M)

 def compactAdd (ρ σ : CompactDensity S) : CompactDensity S where
  field := ρ.field + σ.field
  continuous := by
    intro K c hc
    exact ((ρ.continuous K c hc).add (σ.continuous K c hc)).congr
      (fun p => (map_add (densityCoefficient K c hc p) _ _).symm)
  compact_support := (ρ.compact_support.union σ.compact_support).of_isClosed_subset
    isClosed_closure (support_add_subset ρ.field σ.field)

 def compactWeight (f : M → ℝ) (hf : Continuous f) (ρ : CompactDensity S) :
    CompactDensity S where
  field := fun p => f p • ρ.field p
  continuous := by
    intro K c hc
    exact ((hf.comp continuous_subtype_val).mul (ρ.continuous K c hc)).congr
      (fun p => (map_smul (densityCoefficient K c hc p) _ _).symm)
  compact_support := ρ.compact_support.of_isClosed_subset isClosed_closure
    (fun p hp => (support_weight_subset f ρ.field hp).2)

 theorem compact_closure :
    Specs.SmoothManifolds.Integration.DensityIntegral.compact_closureType.{u} := by
  intro n a M _ S
  exact ⟨⟨compactZero S, rfl⟩, (fun ρ σ => ⟨compactAdd ρ σ, rfl⟩),
    (fun f hf ρ => ⟨compactWeight f hf ρ, rfl⟩)⟩

 theorem compactDensity_ext {ρ σ : CompactDensity S} (h : ρ.field = σ.field) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

 theorem exists_compactSum {ι : Type v} (s : Finset ι) (ρ : ι → CompactDensity S) :
    ∃ σ : CompactDensity S, σ.field = ∑ i ∈ s, (ρ i).field := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨compactZero S, by simp [compactZero]⟩
  | @insert i s hi ih =>
    obtain ⟨σ, hσ⟩ := ih
    exact ⟨compactAdd (ρ i) σ, by simp [compactAdd, hσ, Finset.sum_insert hi]⟩

 def compactSum {ι : Type v} (s : Finset ι) (ρ : ι → CompactDensity S) :
    CompactDensity S := (exists_compactSum s ρ).choose

 theorem compactSum_field {ι : Type v} (s : Finset ι) (ρ : ι → CompactDensity S) :
    (compactSum s ρ).field = ∑ i ∈ s, (ρ i).field := (exists_compactSum s ρ).choose_spec

 theorem integral_zero {I : CompactDensity S → ℝ} (hI : IsDensityIntegral I)
    (ρ : CompactDensity S) (hρ : ρ.field = 0) : I ρ = 0 := by
  have h := hI.2.1 0 ρ ρ (by simp [hρ])
  simpa using h

 theorem integral_sum {ι : Type v} {I : CompactDensity S → ℝ} (hI : IsDensityIntegral I)
    (s : Finset ι) (ρ : ι → CompactDensity S) (σ : CompactDensity S)
    (hσ : σ.field = ∑ i ∈ s, (ρ i).field) : I σ = ∑ i ∈ s, I (ρ i) := by
  classical
  induction s using Finset.induction_on generalizing σ with
  | empty => exact (integral_zero hI σ (by simpa using hσ)).trans (by simp)
  | @insert i s hi ih =>
    have hf : σ.field = (ρ i).field + (compactSum s ρ).field := by
      rw [compactSum_field, hσ, Finset.sum_insert hi]
    rw [hI.1 (ρ i) (compactSum s ρ) σ hf,
      ih (compactSum s ρ) (compactSum_field s ρ), Finset.sum_insert hi]

 theorem finite_localization :
    Specs.SmoothManifolds.Integration.DensityIntegral.finite_localizationType.{u} := by
  intro n a M _ S I hI k ρ σ K c hc hsupport hsum
  have h := integral_sum hI Finset.univ σ ρ (by simpa using hsum)
  simpa only [Finset.sum_congr rfl (fun i _ => hI.2.2 K (c i) (hc i) (σ i) (hsupport i))]
    using h

 theorem field_zero_off_support (ρ : DensityField S) {p : M}
    (hp : p ∉ sectionSupport ρ) : ρ p = 0 :=
  not_not.mp (fun h => hp (subset_closure h))

/-- Compactness, rather than finiteness of the atlas, makes localization finite. -/
 theorem finite_weighted_decomposition {ι : Type v} (ρ : CompactDensity S)
    (f : ι → M → ℝ) (hf : ∀ i, Continuous (f i))
    (hlf : LocallyFinite (fun i => sectionSupport (f i)))
    (hsum : ∀ p ∈ sectionSupport ρ.field, ∑ᶠ i, f i p = 1) :
    ∃ s : Finset ι,
      (∀ i ∉ s, (compactWeight (f i) (hf i) ρ).field = 0) ∧
      ρ.field = ∑ i ∈ s, (compactWeight (f i) (hf i) ρ).field := by
  classical
  let hfin := hlf.finite_nonempty_inter_compact ρ.compact_support
  let s := hfin.toFinset
  have hz (i : ι) (hi : i ∉ s) : (compactWeight (f i) (hf i) ρ).field = 0 := by
    funext p
    by_cases hr : ρ.field p = 0
    · simp [compactWeight, hr]
    · have hp : p ∈ sectionSupport ρ.field := subset_closure hr
      have ht : f i p = 0 := by
        by_contra ht
        exact hi (hfin.mem_toFinset.mpr ⟨p, subset_closure ht, hp⟩)
      simp [compactWeight, ht]
  refine ⟨s, hz, ?_⟩
  funext p
  simp only [Finset.sum_apply, compactWeight]
  by_cases hp : p ∈ sectionSupport ρ.field
  · have hs : ∑ i ∈ s, f i p = 1 := by
      rw [← finsum_eq_finsetSum_of_support_subset (f := fun i => f i p)]
      · exact hsum p hp
      · intro i hi
        exact hfin.mem_toFinset.mpr ⟨p, subset_closure hi, hp⟩
    rw [← Finset.sum_smul, hs, one_smul]
  · simp [field_zero_off_support ρ.field hp]

/-- A coordinate integrand is genuinely linear in the underlying field. -/
 def coordinateDensityLinear (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    DensityField S →ₗ[ℝ] (Euclidean n → ℝ) where
  toFun := coordinateDensity K c hc
  map_add' ρ σ := by
    funext x
    change coordinateDensity K c hc (ρ + σ) x =
      coordinateDensity K c hc ρ x + coordinateDensity K c hc σ x
    by_cases hx : x ∈ modelSet n a
    · by_cases ht : (⟨x, hx⟩ : ModelSpace n a) ∈ c.target
      · simp [coordinateDensity, LocalIntegrationData.extendModel, hx, ht]
      · simp [coordinateDensity, LocalIntegrationData.extendModel, hx, ht]
    · simp [coordinateDensity, LocalIntegrationData.extendModel, hx]
  map_smul' t ρ := by
    funext x
    change coordinateDensity K c hc (t • ρ) x = t • coordinateDensity K c hc ρ x
    by_cases hx : x ∈ modelSet n a
    · by_cases ht : (⟨x, hx⟩ : ModelSpace n a) ∈ c.target
      · simp [coordinateDensity, LocalIntegrationData.extendModel, hx, ht]
      · simp [coordinateDensity, LocalIntegrationData.extendModel, hx, ht]
    · simp [coordinateDensity, LocalIntegrationData.extendModel, hx]

 theorem coordinateIntegral_zero (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) : coordinateIntegral K c hc (0 : DensityField S) = 0 := by
  change (∫ x, coordinateDensityLinear K c hc 0 x) = 0
  rw [map_zero]
  simp

 theorem coordinateIntegral_sum {ι : Type v} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (s : Finset ι)
    (ρ : ι → CompactDensity S)
    (hs : ∀ i ∈ s, sectionSupport (ρ i).field ⊆ c.source) :
    coordinateIntegral K c hc (∑ i ∈ s, (ρ i).field) =
      ∑ i ∈ s, coordinateIntegral K c hc (ρ i).field := by
  change (∫ x, coordinateDensityLinear K c hc (∑ i ∈ s, (ρ i).field) x) = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  exact integral_finsetSum s (fun i hi => DensityChartResults.integrable_proof S K c hc (ρ i) (hs i hi))

/-- Chart localization for any integral satisfying the defining field laws. -/
 theorem locally_finite_localization :
    Specs.SmoothManifolds.Integration.DensityIntegral.locally_finite_localizationType.{u,v} := by
  intro n a M _ S I hI ι ρ f K c hc hf hlf hsub hnear
  obtain ⟨U, hU, hρU, hsum⟩ := hnear
  obtain ⟨s, hz, hdecomp⟩ := finite_weighted_decomposition ρ f hf hlf
    (fun p hp => hsum p (hρU hp))
  let σ : ι → CompactDensity S := fun i => compactWeight (f i) (hf i) ρ
  have hs (i : ι) : sectionSupport (σ i).field ⊆ (c i).source :=
    fun p hp => hsub i (support_weight_subset (f i) ρ.field hp).1
  have hval : I ρ = ∑ i ∈ s, coordinateIntegral K (c i) (hc i) (σ i).field := by
    rw [integral_sum hI s σ ρ hdecomp]
    exact Finset.sum_congr rfl (fun i _ => hI.2.2 K (c i) (hc i) (σ i) (hs i))
  refine ⟨σ, s, (fun _ => rfl), hz, hs, hdecomp, hval, ?_⟩
  rw [finsum_eq_finsetSum_of_support_subset, ← hval]
  intro i hi
  by_contra hn
  apply hi
  change coordinateIntegral K (c i) (hc i) (compactWeight (f i) (hf i) ρ).field = 0
  rw [hz i hn, coordinateIntegral_zero]
/-- A partition is constructed below, rather than added to manifold data. -/
structure IntegrationPartition (S : SmoothManifold n a M) where
  weight : {c // c ∈ S.smoothStructure.val} → M → ℝ
  continuous : ∀ c, Continuous (weight c)
  locallyFinite : LocallyFinite (fun c => sectionSupport (weight c))
  subordinate : ∀ c, sectionSupport (weight c) ⊆ c.val.source
  sum_one : ∀ p, ∑ᶠ c, weight c p = 1

 theorem integrationPartition_exists (S : SmoothManifold n a M) :
    Nonempty (IntegrationPartition S) := by
  obtain ⟨f, hf, hsub⟩ := exists_smooth_partition S
    (fun c : {c // c ∈ S.smoothStructure.val} => c.val.source)
    (fun c => c.val.open_source) (fun p => by
      obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
      exact ⟨⟨c, hc⟩, hp⟩)
  exact ⟨⟨f, (fun c => continuous_iff_continuousAt.mpr (fun p =>
    ((scalarContDiffAt_iff _ _ _ _).mp (hf.1 c p)).1)), hf.2.2.1, hsub, hf.2.2.2⟩⟩

 def partitionTerm (P : IntegrationPartition S)
    (c : {c // c ∈ S.smoothStructure.val}) (ρ : CompactDensity S) : CompactDensity S :=
  compactWeight (P.weight c) (P.continuous c) ρ

 theorem partitionTerm_support (P : IntegrationPartition S)
    (c : {c // c ∈ S.smoothStructure.val}) (ρ : CompactDensity S) :
    sectionSupport (partitionTerm P c ρ).field ⊆ c.val.source :=
  fun p hp => P.subordinate c (support_weight_subset _ _ hp).1

 theorem partition_decomposition (P : IntegrationPartition S) (ρ : CompactDensity S) :
    ∃ s : Finset {c // c ∈ S.smoothStructure.val},
      (∀ c ∉ s, (partitionTerm P c ρ).field = 0) ∧
      ρ.field = ∑ c ∈ s, (partitionTerm P c ρ).field :=
  finite_weighted_decomposition ρ P.weight P.continuous P.locallyFinite
    (fun p _ => P.sum_one p)

 def localTermIntegral (K : FiberCoordinates S) (P : IntegrationPartition S)
    (ρ : CompactDensity S) (c : {c // c ∈ S.smoothStructure.val}) : ℝ :=
  coordinateIntegral K c.val c.property (partitionTerm P c ρ).field

 theorem localTermIntegral_finite (K : FiberCoordinates S) (P : IntegrationPartition S)
    (ρ : CompactDensity S) : (Function.support (localTermIntegral K P ρ)).Finite := by
  obtain ⟨s, hz, _⟩ := partition_decomposition P ρ
  apply s.finite_toSet.subset
  intro c hc
  by_contra hn
  exact hc (by simp only [localTermIntegral, hz c hn, coordinateIntegral_zero])

 def integralWith (K : FiberCoordinates S) (P : IntegrationPartition S)
    (ρ : CompactDensity S) : ℝ := ∑ᶠ c, localTermIntegral K P ρ c

 theorem integralWith_normalize (K : FiberCoordinates S) (P : IntegrationPartition S)
    (L : FiberCoordinates S) (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (ρ : CompactDensity S) (hρ : sectionSupport ρ.field ⊆ d.source) :
    integralWith K P ρ = coordinateIntegral L d hd ρ.field := by
  obtain ⟨s, hz, hdecomp⟩ := partition_decomposition P ρ
  have hds (c : {c // c ∈ S.smoothStructure.val}) :
      sectionSupport (partitionTerm P c ρ).field ⊆ d.source :=
    fun p hp => hρ (support_weight_subset _ _ hp).2
  have hfinite : integralWith K P ρ = ∑ c ∈ s, localTermIntegral K P ρ c := by
    apply finsum_eq_finsetSum_of_support_subset
    intro c hc
    by_contra hn
    exact hc (by simp only [localTermIntegral, hz c hn, coordinateIntegral_zero])
  rw [hfinite]
  calc
    _ = ∑ c ∈ s, coordinateIntegral L d hd (partitionTerm P c ρ).field := by
      apply Finset.sum_congr rfl
      intro c _
      exact DensityChartResults.chart_independence_proof S K L c.val d c.property hd
        (partitionTerm P c ρ) (partitionTerm_support P c ρ) (hds c)
    _ = coordinateIntegral L d hd (∑ c ∈ s, (partitionTerm P c ρ).field) :=
      (coordinateIntegral_sum L d hd s (fun c => partitionTerm P c ρ) (fun c _ => hds c)).symm
    _ = _ := congrArg (coordinateIntegral L d hd) hdecomp.symm

 theorem coordinateIntegral_add (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (ρ σ : CompactDensity S)
    (hρ : sectionSupport ρ.field ⊆ c.source)
    (hσ : sectionSupport σ.field ⊆ c.source) :
    coordinateIntegral K c hc (ρ.field + σ.field) =
      coordinateIntegral K c hc ρ.field + coordinateIntegral K c hc σ.field := by
  change (∫ x, coordinateDensityLinear K c hc (ρ.field + σ.field) x) = _
  rw [map_add]
  exact integral_add (DensityChartResults.integrable_proof S K c hc ρ hρ)
    (DensityChartResults.integrable_proof S K c hc σ hσ)

 theorem coordinateIntegral_smul (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (t : ℝ) (ρ : DensityField S) :
    coordinateIntegral K c hc (t • ρ) = t * coordinateIntegral K c hc ρ := by
  change (∫ x, coordinateDensityLinear K c hc (t • ρ) x) = _
  rw [map_smul]
  exact integral_const_mul t _

 theorem integralWith_laws (K : FiberCoordinates S) (P : IntegrationPartition S) :
    IsDensityIntegral (integralWith K P) := by
  refine ⟨?_, ?_, integralWith_normalize K P⟩
  · intro ρ σ τ hτ
    have hterms : localTermIntegral K P τ = fun c =>
        localTermIntegral K P ρ c + localTermIntegral K P σ c := by
      funext c
      have he : (partitionTerm P c τ).field =
          (partitionTerm P c ρ).field + (partitionTerm P c σ).field := by
        funext p
        simp only [partitionTerm, compactWeight, hτ, Pi.add_apply, smul_add]
      unfold localTermIntegral
      rw [he]
      exact coordinateIntegral_add K c.val c.property _ _
        (partitionTerm_support P c ρ) (partitionTerm_support P c σ)
    unfold integralWith
    rw [hterms]
    exact finsum_add_distrib (localTermIntegral_finite K P ρ) (localTermIntegral_finite K P σ)
  · intro t ρ σ hσ
    have hterms : localTermIntegral K P σ = fun c => t • localTermIntegral K P ρ c := by
      funext c
      have he : (partitionTerm P c σ).field = t • (partitionTerm P c ρ).field := by
        funext p
        simp only [partitionTerm, compactWeight, hσ, Pi.smul_apply]
        exact smul_comm _ _ _
      unfold localTermIntegral
      rw [he, coordinateIntegral_smul]
      rfl
    unfold integralWith
    rw [hterms]
    exact (smul_finsum t (localTermIntegral K P ρ)).symm

 theorem integral_unique (K : FiberCoordinates S) (P : IntegrationPartition S)
    {I : CompactDensity S → ℝ} (hI : IsDensityIntegral I) : I = integralWith K P := by
  funext ρ
  obtain ⟨s, hz, hdecomp⟩ := partition_decomposition P ρ
  rw [integral_sum hI s (fun c => partitionTerm P c ρ) ρ hdecomp]
  have he : integralWith K P ρ = ∑ c ∈ s, localTermIntegral K P ρ c := by
    apply finsum_eq_finsetSum_of_support_subset
    intro c hc
    by_contra hn
    exact hc (by simp only [localTermIntegral, hz c hn, coordinateIntegral_zero])
  rw [he]
  exact Finset.sum_congr rfl (fun c _ => hI.2.2 K c.val c.property
    (partitionTerm P c ρ) (partitionTerm_support P c ρ))

 theorem integral_exists_unique :
    Specs.SmoothManifolds.Integration.DensityIntegral.integral_exists_uniqueType.{u} := by
  intro n a M _ S
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨P⟩ := integrationPartition_exists S
  exact ⟨integralWith K P, integralWith_laws K P,
    fun I hI => integral_unique K P hI⟩
 def zeroCoefficientLinear {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (p : M) : DensityField S →ₗ[ℝ] ℝ where
  toFun ρ := zeroCoefficient ρ p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem zero_coordinate_on_container {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (K : FiberCoordinates S)
    (c : ModelChart 0 a M) (hc : c ∈ S.smoothStructure.val)
    (ρ : CompactDensity S) (hρ : sectionSupport ρ.field ⊆ c.source)
    (C : Set M) (hC : C.Finite) (hρC : sectionSupport ρ.field ⊆ C) :
    coordinateIntegral K c hc ρ.field = ∑ p ∈ hC.toFinset, zeroCoefficient ρ.field p := by
  classical
  obtain ⟨⟨h, he⟩, _⟩ := DensityChartResults.zero_coordinate_proof S K c hc ρ hρ
  rw [he]
  apply Finset.sum_subset
  · intro p hp
    exact hC.mem_toFinset.mpr (hρC (h.mem_toFinset.mp hp))
  · intro p _ hp
    have hz : ρ.field p = 0 := field_zero_off_support _ (fun hm => hp (h.mem_toFinset.mpr hm))
    simp [zeroCoefficient, hz]

 theorem zero_finite_sum :
    Specs.SmoothManifolds.Integration.DensityIntegral.zero_finite_sumType.{u} := by
  intro a M _ S I hI ρ
  classical
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨P⟩ := integrationPartition_exists S
  obtain ⟨s, _, hdecomp⟩ := partition_decomposition P ρ
  let hC := DensityChartResults.zero_compact_finite_proof S
    (sectionSupport ρ.field) ρ.compact_support
  refine ⟨hC, ?_⟩
  rw [integral_sum hI s (fun c => partitionTerm P c ρ) ρ hdecomp]
  calc
    _ = ∑ c ∈ s, ∑ p ∈ hC.toFinset, zeroCoefficient (partitionTerm P c ρ).field p := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hI.2.2 K c.val c.property (partitionTerm P c ρ) (partitionTerm_support P c ρ)]
      exact zero_coordinate_on_container S K c.val c.property _
        (partitionTerm_support P c ρ) _ hC (fun p hp => (support_weight_subset _ _ hp).2)
    _ = ∑ p ∈ hC.toFinset, ∑ c ∈ s, zeroCoefficient (partitionTerm P c ρ).field p :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      change ∑ c ∈ s, zeroCoefficientLinear S p (partitionTerm P c ρ).field =
        zeroCoefficientLinear S p ρ.field
      rw [← map_sum, ← hdecomp]
 theorem fiberPullback_basis {n : ℕ} {V W : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) (b : Module.Basis (Fin n) ℝ V) (c : Module.Basis (Fin n) ℝ W)
    (ρ : densitySubmodule (⋀[ℝ]^n W)) :
    tupleEvaluation (DensityIntegrationData.fiberPullback L ρ) b =
      |c.det (L ∘ b)| * tupleEvaluation ρ c := by
  unfold tupleEvaluation
  change ρ.val (exteriorPower.map n L (exteriorPower.ιMulti ℝ n b)) = _
  rw [exteriorPower.map_apply_ιMulti, MetricVolumeResults.wedge_basis_expansion c, ρ.property]

section Diffeomorphisms
open Module MetricVolumeResults FrameData FiniteRegularityData Filter
variable {b : ModelKind} {N : Type u} [TopologicalSpace N]
  {T : SmoothManifold n b N}

 theorem pullback_coefficient (f : M → N)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (K : FiberCoordinates S) (J : FiberCoordinates T)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart n b N) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hq : f p ∈ d.source) (ρ : DensityField T) :
    densityCoefficient K c hc ⟨p, hp⟩ (pullbackField S T f L ρ p) =
      densityCoefficient J d hd ⟨f p, hq⟩ (ρ (f p)) *
        |(Matrix.of (fun i j => J.equiv d hd (f p) hq
          (L p ((K.equiv c hc p hp).symm ((Pi.basisFun ℝ (Fin n)) j))) i)).det| := by
  let bs := coordinateBasis K c hc ⟨p, hp⟩
  let bt := coordinateBasis J d hd ⟨f p, hq⟩
  have he := fiberPullback_basis (V := TangentSpace S p) (W := TangentSpace T (f p))
    (L p) bs bt (ρ (f p))
  have hdet : bt.det (L p ∘ bs) =
      (Matrix.of (fun i j => J.equiv d hd (f p) hq
        (L p ((K.equiv c hc p hp).symm ((Pi.basisFun ℝ (Fin n)) j))) i)).det := by
    rw [Basis.det_apply]
    congr 1
  rw [hdet, mul_comm] at he
  simpa only [bs, bt, coordinateBasis, tupleEvaluation, Basis.coe_map,
    Function.comp_def, densityCoefficient, OrientationData.coordinateVector,
    DensityIntegrationData.pullbackField, LinearMap.coe_mk, AddHom.coe_mk] using he

 def chartJacobianDet (c : ModelChart n a M) (d : ModelChart n b N)
    (f : M → N) (p : M) : ℝ :=
  (Matrix.of (fun i j => chartDerivative c d f p (Pi.single j 1) i)).det

 theorem pullback_chart_coefficient (f : M → N) (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p)) (K : FiberCoordinates S)
    (J : FiberCoordinates T) (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hfp : f p ∈ d.source) (ρ : DensityField T) :
    densityCoefficient K c hc ⟨p, hp⟩ (pullbackField S T f L ρ p) =
      densityCoefficient J d hd ⟨f p, hfp⟩ (ρ (f p)) * |chartJacobianDet c d f p| := by
  rw [pullback_coefficient f L K J c hc d hd p hp hfp ρ]
  congr 2
  congr 1
  ext i j
  have hj := FiniteRegularity.smooth_jacobian_coordinateDerivative S T f hf p (L p)
    (hL p) c d hc hd hp hfp (K.equiv c hc p hp) (J.equiv d hd (f p) hfp)
    (K.isCoordinates c hc p hp) (J.isCoordinates d hd (f p) hfp)
    ((K.equiv c hc p hp).symm ((Pi.basisFun ℝ (Fin n)) j))
  simpa only [Matrix.of_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
    using congrFun hj i

 theorem pullback_continuous (f : M → N) (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (ρ : DensityField T) (hρ : IsContinuousDensity ρ) :
    IsContinuousDensity (pullbackField S T f L ρ) := by
  intro K c hc
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p.val)
  obtain ⟨J⟩ := TangentBundle.fiberCoordinates_exists T
  let bc : d.source → ℝ := fun q => densityCoefficient J d hd q (ρ q.val)
  have hb : ContinuousAt (FrameData.totalize bc) (f p.val) := by
    apply (d.open_source.isOpenEmbedding_subtypeVal.continuousAt_iff
      (x := (⟨f p.val, hfp⟩ : d.source))).mp
    simpa only [Function.comp_def, FrameData.totalize_of_mem bc _ (Subtype.property _)]
      using (hρ J d hd).continuousAt (x := ⟨f p.val, hfp⟩)
  have heval : ContDiff ℝ (⊤ : ℕ∞)
      (fun D : Euclidean n →L[ℝ] Euclidean n => fun i j => D (Pi.single j 1) i) := by
    fun_prop
  have hj : VectorSmoothAt S.smoothStructure.val (chartJacobianDet c d f) p.val :=
    ((Tensors.chartDerivative_smoothAt S T f hf c d hc hd p.val p.property hfp).postcomp
      heval).postcomp (matrix_det_smooth n)
  have hh : ContinuousAt (fun y : M => FrameData.totalize bc (f y) *
      |chartJacobianDet c d f y|) p.val :=
    (hb.comp (f := f) (x := p.val) (hf p.val).1).mul hj.1.abs
  have he : (fun y : c.source => FrameData.totalize bc (f y.val) *
      |chartJacobianDet c d f y.val|) =ᶠ[𝓝 p]
      (fun y : c.source => densityCoefficient K c hc y
        (pullbackField S T f L ρ y.val)) := by
    filter_upwards [((hf p.val).1.comp continuousAt_subtype_val).preimage_mem_nhds
      (d.open_source.mem_nhds hfp)] with y hy
    change f y.val ∈ d.source at hy
    simp only [FrameData.totalize, dif_pos hy]
    exact (pullback_chart_coefficient f hf L hL K J c d hc hd y.val y.property hy ρ).symm
  exact (hh.comp continuousAt_subtype_val).congr he

 theorem pullback_support (f : M → N) (hf : Continuous f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) (ρ : DensityField T) :
    sectionSupport (pullbackField S T f L ρ) ⊆ f ⁻¹' sectionSupport ρ := by
  apply closure_minimal
  · intro p hp
    apply subset_closure
    intro hz
    apply hp
    change DensityIntegrationData.fiberPullback
      (V := TangentSpace S p) (W := TangentSpace T (f p)) (L p) (ρ (f p)) = 0
    rw [hz, map_zero]
  · exact isClosed_closure.preimage hf

 def compactPullback (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (F.toEquiv p))
    (hL : ∀ p, IsDifferential S T F.toEquiv p (L p)) (ρ : CompactDensity T) :
    CompactDensity S where
  field := pullbackField S T F.toEquiv L ρ.field
  continuous := pullback_continuous F.toEquiv F.contDiff_toFun L hL ρ.field ρ.continuous
  compact_support := by
    apply (ρ.compact_support.image F.toHomeomorph.symm.continuous).of_isClosed_subset isClosed_closure
    intro p hp
    have hh := pullback_support F.toEquiv F.toHomeomorph.continuous L ρ.field hp
    exact ⟨F.toEquiv p, hh, F.toEquiv.symm_apply_apply p⟩

/-- The coordinate change of a diffeomorphism may join different model kinds. -/
 def coordinateChange (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (c : ModelChart n a M) (d : ModelChart n b N) :
    OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b) :=
  c.symm.trans (F.toHomeomorph.toOpenPartialHomeomorph.trans d)

 theorem coordinateChange_source (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (c : ModelChart n a M) (d : ModelChart n b N) (x : ModelSpace n a) :
    x ∈ (coordinateChange F c d).source ↔
      x ∈ c.target ∧ F.toEquiv (c.symm x) ∈ d.source := by
  simp [coordinateChange, OpenPartialHomeomorph.trans_source]
  intro _
  rfl

 theorem coordinateChange_apply (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (c : ModelChart n a M) (d : ModelChart n b N) (x : ModelSpace n a) :
    coordinateChange F c d x = d (F.toEquiv (c.symm x)) := rfl

 def ambientMap {n : ℕ} {a b : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b)) (x : Euclidean n) :
    Euclidean n := if hx : x ∈ modelSet n a then (e ⟨x, hx⟩).val else 0

 theorem ambientMap_at {n : ℕ} {a b : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b)) (x : ModelSpace n a) :
    ambientMap e x.val = (e x).val := by simp [ambientMap, x.property]

 theorem ambientMap_injective {n : ℕ} {a b : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b)) :
    InjOn (ambientMap e) (LocalIntegrationResults.ambientDomain e.source) := by
  rintro x ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩ he
  rw [ambientMap_at, ambientMap_at] at he
  exact congrArg Subtype.val (e.injOn hy hw (Subtype.ext he))

 theorem ambientMap_image {n : ℕ} {a b : ModelKind}
    (e : OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b)) :
    ambientMap e '' LocalIntegrationResults.ambientDomain e.source =
      LocalIntegrationResults.ambientDomain e.target := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨e z, e.map_source hz, (ambientMap_at e z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(e.symm z).val, ⟨e.symm z, e.map_target hz, rfl⟩, ?_⟩
    rw [ambientMap_at, e.right_inv hz]

/-- Actual ambient derivatives, also at a half-space face. -/
 theorem ambientMap_hasDeriv
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (x : ModelSpace n a) (hx : x ∈ (coordinateChange F c d).source) :
    HasFDerivWithinAt (ambientMap (coordinateChange F c d))
      (chartDerivative c d F.toEquiv (c.symm x))
      (LocalIntegrationResults.ambientDomain (coordinateChange F c d).source) x.val := by
  let e := coordinateChange F c d
  let U := LocalIntegrationResults.ambientDomain e.source
  have hx' := (coordinateChange_source F c d x).mp hx
  have hp : c.symm x ∈ c.source := c.map_target hx'.1
  have hcx : c (c.symm x) = x := c.right_inv hx'.1
  obtain ⟨H, hH, heq⟩ := FiniteRegularity.chartDerivative_exists (⊤ : ℕ∞) (by simp)
    c d F.toEquiv (c.symm x) ((F.contDiff_toFun _).2 c hc d hd hp hx'.2)
  rw [hcx] at hH
  let j : U → c.target := fun z =>
    ⟨⟨z.val, by obtain ⟨y, hy, he⟩ := z.property; exact he ▸ y.property⟩,
      by obtain ⟨y, hy, he⟩ := z.property
         have hh := (coordinateChange_source F c d y).mp hy
         convert hh.1 using 1 <;> congr 1 <;> exact he.symm⟩
  have hj : Continuous j := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _
  let g : U → M := fun z => (c.toHomeomorphSourceTarget.symm (j z)).val
  have hg : Continuous g := continuous_subtype_val.comp
    (c.toHomeomorphSourceTarget.symm.continuous.comp hj)
  let q : U := ⟨x.val, x, hx, rfl⟩
  have hgq : g q = c.symm x := rfl
  have hevent : ∀ᶠ z : U in 𝓝 q,
      H z.val = ambientMap e z.val := by
    have hh := (hg.continuousAt (x := q)).tendsto.eventually (hgq ▸ heq)
    filter_upwards [hh] with z hz
    have hcz : (c (g z)).val = z.val := congrArg Subtype.val (c.right_inv (j z).property)
    rw [hcz] at hz
    rw [ambientMap_at e (j z).val, coordinateChange_apply]
    exact hz
  have hevent' : ambientMap e =ᶠ[𝓝[U] x.val] H := by
    rw [← map_nhds_subtype_val q]
    exact Filter.eventually_map.mpr (hevent.mono (fun z hz => hz.symm))
  exact hH.hasFDerivWithinAt.congr_of_eventuallyEq hevent'
    (mem_of_mem_nhds hevent).symm

 theorem chartJacobianDet_eq_det (c : ModelChart n a M) (d : ModelChart n b N)
    (f : M → N) (p : M) : chartJacobianDet c d f p = (chartDerivative c d f p).det := by
  change chartJacobianDet c d f p = LinearMap.det (chartDerivative c d f p).toLinearMap
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
  unfold chartJacobianDet
  congr 1

 theorem diffeomorphism_coordinate_integral
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (F.toEquiv p))
    (hL : ∀ p, IsDifferential S T F.toEquiv p (L p))
    (K : FiberCoordinates S) (J : FiberCoordinates T)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (ρ : CompactDensity T) (hρd : sectionSupport ρ.field ⊆ d.source)
    (hρc : sectionSupport ρ.field ⊆ F.toEquiv '' c.source) :
    coordinateIntegral K c hc (compactPullback F L hL ρ).field =
      coordinateIntegral J d hd ρ.field := by
  let e := coordinateChange F c d
  let U := LocalIntegrationResults.ambientDomain e.source
  let V := LocalIntegrationResults.ambientDomain e.target
  let ψ := ambientMap e
  let D := fderivWithin ℝ ψ U
  let f := coordinateDensity K c hc (compactPullback F L hL ρ).field
  let g := coordinateDensity J d hd ρ.field
  have hU : MeasurableSet U := LocalIntegrationResults.ambientDomain_measurable e.open_source
  have hD : ∀ x ∈ U, HasFDerivWithinAt ψ (D x) U x := by
    rintro x ⟨y, hy, rfl⟩
    exact (ambientMap_hasDeriv F c d hc hd y hy).differentiableWithinAt.hasFDerivWithinAt
  have hfg : ∀ x ∈ U, |(D x).det| * g (ψ x) = f x := by
    rintro x ⟨y, hy, rfl⟩
    have hy' := (coordinateChange_source F c d y).mp hy
    let p := c.symm y
    have hp : p ∈ c.source := c.map_target hy'.1
    have hfp : F.toEquiv p ∈ d.source := hy'.2
    have hcy : c p = y := c.right_inv hy'.1
    have hψ : ψ y.val = (d (F.toEquiv p)).val := ambientMap_at e y
    have hdet : (D y.val).det = chartJacobianDet c d F.toEquiv p := by
      have huniq := uniqueDiffOn_modelDomain e.open_source
      change (fderivWithin ℝ (ambientMap e) U y.val).det = _
      rw [(ambientMap_hasDeriv F c d hc hd y hy).fderivWithin
        (huniq _ ⟨y, hy, rfl⟩)]
      exact (chartJacobianDet_eq_det c d F.toEquiv p).symm
    have heval : f y.val = densityCoefficient K c hc ⟨p, hp⟩
        (pullbackField S T F.toEquiv L ρ.field p) := by
      change coordinateDensity K c hc _ y.val = _
      rw [← hcy]
      exact DensityChartResults.density_at K c hc _ ⟨p, hp⟩
    have hright : g (ψ y.val) =
        densityCoefficient J d hd ⟨F.toEquiv p, hfp⟩ (ρ.field (F.toEquiv p)) :=
      (congrArg g hψ).trans (DensityChartResults.density_at J d hd ρ.field ⟨F.toEquiv p, hfp⟩)
    have hcoef := pullback_chart_coefficient F.toEquiv F.contDiff_toFun L hL
      K J c d hc hd p hp hfp ρ.field
    calc
      _ = |chartJacobianDet c d F.toEquiv p| *
          densityCoefficient J d hd ⟨F.toEquiv p, hfp⟩ (ρ.field (F.toEquiv p)) :=
        congrArg₂ (fun t r : ℝ => |t| * r) hdet hright
      _ = densityCoefficient K c hc ⟨p, hp⟩
          (pullbackField S T F.toEquiv L ρ.field p) := (mul_comm _ _).trans hcoef.symm
      _ = _ := heval.symm
  have hfU : Function.support f ⊆ U := by
    intro x hx
    obtain ⟨p, hp, hpc, heq⟩ := DensityChartResults.density_nonzero K c hc _ x hx
    have hfp : F.toEquiv p ∈ sectionSupport ρ.field :=
      pullback_support F.toEquiv F.toHomeomorph.continuous L ρ.field hp
    exact ⟨c p, (coordinateChange_source F c d (c p)).mpr
      ⟨c.map_source hpc, by simpa only [c.left_inv hpc] using hρd hfp⟩, heq⟩
  have hgV : Function.support g ⊆ V := by
    intro x hx
    obtain ⟨q, hq, hqd, heq⟩ := DensityChartResults.density_nonzero J d hd ρ.field x hx
    obtain ⟨p, hpc, hpq⟩ := hρc hq
    have hp : c p ∈ e.source := (coordinateChange_source F c d (c p)).mpr
      ⟨c.map_source hpc, by simpa only [c.left_inv hpc, hpq] using hqd⟩
    have he : e (c p) = d q := by rw [coordinateChange_apply, c.left_inv hpc, hpq]
    exact ⟨d q, he ▸ e.map_source hp, heq⟩
  have hsub := integral_image_eq_integral_abs_det_fderiv_smul volume hU hD
    (ambientMap_injective e) g
  rw [ambientMap_image e] at hsub
  have hfint : (∫ x in U, f x) = ∫ x, f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => not_not.mp (fun hn => hx (hfU hn)))
  have hgint : (∫ x in V, g x) = ∫ x, g x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => not_not.mp (fun hn => hx (hgV hn)))
  change ∫ x, f x = ∫ x, g x
  calc
    _ = ∫ x in U, f x := hfint.symm
    _ = ∫ x in U, |(D x).det| • g (ψ x) :=
      setIntegral_congr_fun hU (fun x hx => (hfg x hx).symm)
    _ = ∫ x in V, g x := hsub.symm
    _ = _ := hgint

 def pullbackLinear (f : M → N)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) :
    DensityField T →ₗ[ℝ] DensityField S where
  toFun := pullbackField S T f L
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem diffeomorphism :
    Specs.SmoothManifolds.Integration.DensityIntegral.diffeomorphismType.{u} := by
  intro n a b M N _ _ S T F I J hI hJ L hL ρ
  classical
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨Q⟩ := TangentBundle.fiberCoordinates_exists T
  let ι := {c // c ∈ S.smoothStructure.val} × {d // d ∈ T.smoothStructure.val}
  let U : ι → Set N := fun i => i.2.val.source ∩ F.toEquiv '' i.1.val.source
  have hU (i : ι) : IsOpen (U i) :=
    i.2.val.open_source.inter (F.toHomeomorph.isOpenMap _ i.1.val.open_source)
  have hcover (q : N) : ∃ i, q ∈ U i := by
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 (F.toEquiv.symm q)
    obtain ⟨d, hd, hq⟩ := T.smoothStructure.property.1.1 q
    exact ⟨(⟨c, hc⟩, ⟨d, hd⟩), hq, F.toEquiv.symm q, hp, F.toEquiv.apply_symm_apply q⟩
  obtain ⟨f, hf, hsub⟩ := exists_smooth_partition T U hU hcover
  have hfc (i : ι) : Continuous (f i) := continuous_iff_continuousAt.mpr
    (fun p => ((scalarContDiffAt_iff _ _ _ _).mp (hf.1 i p)).1)
  let τ : ι → CompactDensity T := fun i => compactWeight (f i) (hfc i) ρ
  let σ : ι → CompactDensity S := fun i => compactPullback F L hL (τ i)
  let σ₀ := compactPullback F L hL ρ
  have hτU (i : ι) : sectionSupport (τ i).field ⊆ U i :=
    fun q hq => hsub i (support_weight_subset _ _ hq).1
  have hσc (i : ι) : sectionSupport (σ i).field ⊆ i.1.val.source := by
    intro p hp
    have hq := pullback_support F.toEquiv F.toHomeomorph.continuous L (τ i).field hp
    obtain ⟨q, hqc, he⟩ := (hτU i hq).2
    exact F.toEquiv.injective he ▸ hqc
  obtain ⟨s, _, hdecomp⟩ := finite_weighted_decomposition ρ f hfc hf.2.2.1
    (fun p _ => hf.2.2.2 p)
  have hσsum : σ₀.field = ∑ i ∈ s, (σ i).field := by
    change pullbackLinear F.toEquiv L ρ.field = ∑ i ∈ s, pullbackLinear F.toEquiv L (τ i).field
    rw [hdecomp, map_sum]
  refine ⟨σ₀, rfl, ?_⟩
  rw [integral_sum hI s σ σ₀ hσsum, integral_sum hJ s τ ρ hdecomp]
  apply Finset.sum_congr rfl
  intro i _
  rw [hI.2.2 K i.1.val i.1.property (σ i) (hσc i),
    hJ.2.2 Q i.2.val i.2.property (τ i) (fun q hq => (hτU i hq).1)]
  exact diffeomorphism_coordinate_integral F L hL K Q i.1.val i.2.val
    i.1.property i.2.property (τ i) (fun q hq => (hτU i hq).1)
    (fun q hq => (hτU i hq).2)

end Diffeomorphisms

end SmoothManifolds.DensityIntegralResults
