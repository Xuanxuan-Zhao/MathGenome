import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.CountableImmersedAtlas

noncomputable section
open Set Function TopologicalSpace
open scoped ContDiff Manifold
namespace D13Unified.Ch20.CountableImmersedAtlas
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ∞} (D : Data S E k)

instance : Nonempty (Point D) := by
  obtain ⟨x, hx⟩ := D.nonempty
  exact ⟨⟨x, hx⟩⟩

/-- A total extension of the parametrization into the union; values off U are irrelevant. -/
def parametrization (m : ℕ) (ξ : S) : Point D := by
  classical
  exact if h : ξ ∈ D.U m then ⟨D.f m ξ, m, ξ, h, rfl⟩ else Classical.choice inferInstance

@[simp] lemma parametrization_val (m : ℕ) {ξ : S} (h : ξ ∈ D.U m) :
    (parametrization D m ξ).val = D.f m ξ := by simp [parametrization, h]

lemma parametrization_injective (m : ℕ) : InjOn (parametrization D m) (D.U m) := by
  intro x hx y hy h
  apply D.injective m hx hy
  simpa only [parametrization_val D m hx, parametrization_val D m hy] using congrArg Subtype.val h

/-- The raw chart, prior to the construction of any topology on the union. -/
def rawChart (m : ℕ) : PartialEquiv (Point D) S :=
  (Set.InjOn.toPartialEquiv (parametrization D m) (D.U m)
    (parametrization_injective D m)).symm

@[simp] lemma rawChart_target (m : ℕ) : (rawChart D m).target = D.U m := rfl
@[simp] lemma rawChart_symm (m : ℕ) : (rawChart D m).symm =
    Set.InjOn.toPartialEquiv (parametrization D m) (D.U m)
      (parametrization_injective D m) := rfl

lemma rawChart_source (m : ℕ) :
    (rawChart D m).source = {x | x.val ∈ D.f m '' D.U m} := by
  ext x
  change (x ∈ parametrization D m '' D.U m) ↔ _
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨ξ, hξ, (parametrization_val D m hξ).symm⟩
  · rintro ⟨ξ, hξ, h⟩
    exact ⟨ξ, hξ, Subtype.ext ((parametrization_val D m hξ).trans h)⟩

lemma rawChart_inverse_val (m : ℕ) {ξ : S} (hξ : ξ ∈ D.U m) :
    ((rawChart D m).symm ξ).val = D.f m ξ := parametrization_val D m hξ

lemma rawChart_cover (x : Point D) : ∃ m, x ∈ (rawChart D m).source := by
  obtain ⟨m, ξ, hξ, hx⟩ := x.property
  exact ⟨m, (rawChart_source D m).symm ▸ ⟨ξ, hξ, hx⟩⟩

lemma rawChart_apply_val (m : ℕ) {x : Point D} (hx : x ∈ (rawChart D m).source) :
    D.f m (rawChart D m x) = x.val := by
  have h := congrArg Subtype.val ((rawChart D m).left_inv hx)
  rw [rawChart_inverse_val D m ((rawChart D m).map_source hx)] at h
  exact h

/-- Coherence is a consequence of pointwise injectivity, not an extra hypothesis. -/
lemma change_coherent (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) {ξ : S}
    (hξ : ξ ∈ D.U a) :
    D.change b c hbc (D.change a b hab ξ) = D.change a c (hab.trans hbc) ξ := by
  have habξ : D.change a b hab ξ ∈ D.U b :=
    D.change_target a b hab ((D.change a b hab).map_source (D.change_source a b hab ▸ hξ))
  apply D.injective c
    (D.change_target b c hbc ((D.change b c hbc).map_source
      (D.change_source b c hbc ▸ habξ)))
    (D.change_target a c (hab.trans hbc) ((D.change a c (hab.trans hbc)).map_source
      (D.change_source a c (hab.trans hbc) ▸ hξ)))
  rw [D.intertwine b c hbc _ habξ, D.intertwine a b hab _ hξ,
    D.intertwine a c (hab.trans hbc) _ hξ]

/-- An overlap expressed in a common later stage. -/
def overlap (m n : ℕ) : OpenPartialHomeomorph S S :=
  (D.change m (max m n) (le_max_left _ _)).trans
    (D.change n (max m n) (le_max_right _ _)).symm

lemma raw_transition_source (m n : ℕ) :
    ((rawChart D m).symm.trans (rawChart D n)).source = (overlap D m n).source := by
  let r := max m n
  let a := D.change m r (le_max_left _ _)
  let b := D.change n r (le_max_right _ _)
  have ha : a.source = D.U m := D.change_source _ _ _
  have hb : b.source = D.U n := D.change_source _ _ _
  ext ξ
  change (ξ ∈ D.U m ∧ (rawChart D m).symm ξ ∈ (rawChart D n).source) ↔
    (ξ ∈ a.source ∧ a ξ ∈ b.target)
  constructor
  · rintro ⟨hξ, hx⟩
    have hη := (rawChart D n).map_source hx
    rw [rawChart_target] at hη
    have hval : D.f n (rawChart D n ((rawChart D m).symm ξ)) = D.f m ξ := by
      rw [rawChart_apply_val D n hx, rawChart_inverse_val D m hξ]
    have heq : b (rawChart D n ((rawChart D m).symm ξ)) = a ξ := by
      apply D.injective r
        (D.change_target _ _ _ (b.map_source (hb ▸ hη)))
        (D.change_target _ _ _ (a.map_source (ha ▸ hξ)))
      exact (D.intertwine n r (le_max_right _ _) _ hη).trans
        (hval.trans (D.intertwine m r (le_max_left _ _) _ hξ).symm)
    exact ⟨ha ▸ hξ, heq ▸ b.map_source (hb ▸ hη)⟩
  · rintro ⟨hξ, ht⟩
    have hξ' : ξ ∈ D.U m := ha ▸ hξ
    refine ⟨hξ', ?_⟩
    rw [rawChart_source]
    refine ⟨b.symm (a ξ), hb ▸ b.map_target ht, ?_⟩
    have heq := D.intertwine n r (le_max_right _ _) (b.symm (a ξ)) (hb ▸ b.map_target ht)
    change D.f r (b (b.symm (a ξ))) = _ at heq
    rw [b.right_inv ht, D.intertwine m r (le_max_left _ _) ξ hξ'] at heq
    exact heq.symm.trans (rawChart_inverse_val D m hξ').symm

lemma raw_transition_eqOn (m n : ℕ) :
    EqOn ((rawChart D m).symm.trans (rawChart D n)) (overlap D m n)
      ((rawChart D m).symm.trans (rawChart D n)).source := by
  let r := max m n
  let a := D.change m r (le_max_left _ _)
  let b := D.change n r (le_max_right _ _)
  intro ξ hξ
  have hξ' : ξ ∈ (overlap D m n).source := raw_transition_source D m n ▸ hξ
  change ξ ∈ D.U m ∧ (rawChart D m).symm ξ ∈ (rawChart D n).source at hξ
  have hη := (rawChart D n).map_source hξ.2
  rw [rawChart_target] at hη
  have hval : D.f n (rawChart D n ((rawChart D m).symm ξ)) = D.f m ξ := by
    rw [rawChart_apply_val D n hξ.2, rawChart_inverse_val D m hξ.1]
  have heq : b (rawChart D n ((rawChart D m).symm ξ)) = a ξ := by
    apply D.injective r
      (D.change_target _ _ _ (b.map_source (D.change_source _ _ _ ▸ hη)))
      (D.change_target _ _ _ (a.map_source (D.change_source _ _ _ ▸ hξ.1)))
    exact (D.intertwine n r (le_max_right _ _) _ hη).trans
      (hval.trans (D.intertwine m r (le_max_left _ _) _ hξ.1).symm)
  change rawChart D n ((rawChart D m).symm ξ) = b.symm (a ξ)
  rw [← heq, b.left_inv (D.change_source _ _ _ ▸ hη)]

lemma overlap_regular (m n : ℕ) :
    ContDiffOn ℝ (k : ℕ∞ω) (overlap D m n) (overlap D m n).source := by
  apply (D.change_symm_regular n (max m n) (le_max_right _ _)).comp
    ((D.change_regular m (max m n) (le_max_left _ _)).mono inter_subset_left)
  exact fun _ hx => hx.2

lemma raw_transition_regular (m n : ℕ) :
    ContDiffOn ℝ (k : ℕ∞ω) ((rawChart D m).symm.trans (rawChart D n))
      ((rawChart D m).symm.trans (rawChart D n)).source := by
  apply ContDiffOn.congr _ (raw_transition_eqOn D m n)
  rw [raw_transition_source]
  exact overlap_regular D m n


/-- The gluing topology is generated by the raw charts. -/
def core : ChartedSpaceCore S (Point D) where
  atlas := range (rawChart D)
  chartAt x := rawChart D (Classical.choose (rawChart_cover D x))
  mem_chart_source x := Classical.choose_spec (rawChart_cover D x)
  chart_mem_atlas x := mem_range_self _
  open_source := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [raw_transition_source]
    exact (overlap D m n).open_source
  continuousOn_toFun := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact (raw_transition_regular D m n).continuousOn

/-- A separately constructed topology, which can be finer than the ambient subspace topology. -/
@[instance_reducible] def topology : TopologicalSpace (Point D) := (core D).toTopologicalSpace

local instance : TopologicalSpace (Point D) := topology D

def chart (m : ℕ) : OpenPartialHomeomorph (Point D) S :=
  (core D).openPartialHomeomorph (rawChart D m) (mem_range_self m)

@[simp] lemma chart_source (m : ℕ) : (chart D m).source = (rawChart D m).source := rfl
@[simp] lemma chart_target (m : ℕ) : (chart D m).target = D.U m := rfl
lemma chart_source_eq (m : ℕ) : (chart D m).source = {x | x.val ∈ D.f m '' D.U m} :=
  rawChart_source D m
lemma chart_inverse_val (m : ℕ) {ξ : S} (hξ : ξ ∈ D.U m) :
    ((chart D m).symm ξ).val = D.f m ξ := rawChart_inverse_val D m hξ

lemma chart_cover : ⋃ m, (chart D m).source = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨m, hm⟩ := rawChart_cover D x
  exact mem_iUnion.mpr ⟨m, hm⟩

lemma chart_transition_regular (m n : ℕ) :
    ContDiffOn ℝ (k : ℕ∞ω) ((chart D m).symm.trans (chart D n))
      ((chart D m).symm.trans (chart D n)).source := raw_transition_regular D m n

lemma inclusion_regular (m : ℕ) :
    ContDiffOn ℝ (k : ℕ∞ω) (fun ξ => ((chart D m).symm ξ).val) (D.U m) :=
  (D.regular m).congr (fun _ hξ => chart_inverse_val D m hξ)

lemma inclusion_differential (m : ℕ) {ξ : S} (hξ : ξ ∈ D.U m) :
    Function.Injective (fderiv ℝ (fun ξ => ((chart D m).symm ξ).val) ξ) := by
  have heq : (fun ξ => ((chart D m).symm ξ).val) =ᶠ[nhds ξ] D.f m := by
    filter_upwards [(D.open_U m).mem_nhds hξ] with η hη
    exact chart_inverse_val D m hη
  rw [heq.fderiv_eq]
  exact D.differential m ξ hξ

lemma inclusion_continuous : Continuous (fun x : Point D => x.val) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨m, hx⟩ := rawChart_cover D x
  have hx' : x ∈ (chart D m).source := hx
  have hpar := (chart D m).map_source hx'
  have hcont : ContinuousAt (fun ξ => ((chart D m).symm ξ).val) (chart D m x) :=
    ((inclusion_regular D m).continuousOn.continuousAt ((D.open_U m).mem_nhds hpar))
  exact ((chart D m).symm.continuousAt_iff_continuousAt_comp_right hx').mpr hcont

lemma hausdorff : T2Space (Point D) :=
  T2Space.of_injective_continuous Subtype.val_injective (inclusion_continuous D)

lemma second_countable [FiniteDimensional ℝ S] : SecondCountableTopology (Point D) := by
  let : ∀ m, SecondCountableTopology (chart D m).source :=
    fun m => (chart D m).secondCountableTopology_source
  exact secondCountableTopology_of_countable_cover (fun m => (chart D m).open_source)
    (chart_cover D)

/-- The genuine charted space associated to this countable family. -/
@[instance_reducible] def chartedSpace : ChartedSpace S (Point D) := (core D).toChartedSpace

lemma chartedSpace_atlas :
    @atlas S _ (Point D) (topology D) (chartedSpace D) = range (chart D) := by
  ext e
  change (e ∈ ⋃ (c : PartialEquiv (Point D) S), ⋃ (hc : c ∈ range (rawChart D)),
    {(core D).openPartialHomeomorph c hc}) ↔ _
  simp only [mem_iUnion, mem_singleton_iff]
  constructor
  · rintro ⟨c, hc, he⟩
    obtain ⟨m, rfl⟩ := hc
    exact ⟨m, he.symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨rawChart D m, ⟨m, rfl⟩, rfl⟩

lemma manifold : @IsManifold ℝ _ S _ _ S _ (modelWithCornersSelf ℝ S)
    (k : ℕ∞ω) (Point D) (topology D) (chartedSpace D) := by
  let : ChartedSpace S (Point D) := chartedSpace D
  apply isManifold_of_contDiffOn (modelWithCornersSelf ℝ S) (k : ℕ∞ω) (Point D)
  intro e e' he he'
  rw [chartedSpace_atlas D] at he he'
  obtain ⟨m, rfl⟩ := he
  obtain ⟨n, rfl⟩ := he'
  simpa using chart_transition_regular D m n

/-- Assemble the constructed atlas and all its global separation and immersion properties. -/
def gluedAtlas [FiniteDimensional ℝ S] : Atlas D where
  topology := topology D
  chart := chart D
  source_eq := chart_source_eq D
  target_eq := chart_target D
  inverse_eq := fun m _ hξ => chart_inverse_val D m hξ
  cover := chart_cover D
  transitions := chart_transition_regular D
  inclusion_continuous := inclusion_continuous D
  inclusion_injective := Subtype.val_injective
  inclusion_regular := inclusion_regular D
  inclusion_differential := fun m _ hξ => inclusion_differential D m hξ
  hausdorff := hausdorff D
  second_countable := second_countable D
  chartedSpace := chartedSpace D
  atlas_eq := chartedSpace_atlas D
  atlas_countable := (chartedSpace_atlas D).symm ▸ countable_range (chart D)
  manifold := manifold D
  dimension := fun _ => rfl

/-- Countable compatible immersed atlas gluing, including zero-dimensional model spaces. -/
theorem gluing : gluingExpected := by
  intro S E _ _ _ _ _ _ k D
  exact ⟨gluedAtlas D⟩

end D13Unified.Ch20.CountableImmersedAtlas
