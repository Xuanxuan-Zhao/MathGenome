import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LocalNullVariant
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch04.MeasurableMapTests

open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
universe u v
namespace D11.Ch20.LocalNullVariant

abbrev locallyNull {X : Type u} [MeasurableSpace X] := @LocallyNull X _
abbrev localLInfinity {X : Type u} [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜] :=
  @LocalLInfinity X _ 𝕜 _
abbrev classOf {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜] :=
  @ClassOf X _ 𝕜 _
abbrev localNorm {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜] :=
  @LocalNorm X _ 𝕜 _

theorem locallyNull_empty : Specs.D11.Ch20.LocalNullVariant.locallyNull_empty := by
  intro X _ μ
  exact ⟨MeasurableSet.empty, by simp⟩

theorem locallyNull_subset : Specs.D11.Ch20.LocalNullVariant.locallyNull_subset := by
  intro X _ μ N A hN hA hAN
  refine ⟨hA, fun E _ _ => ?_⟩
  exact measure_mono_null (inter_subset_inter_left E hAN) (hN.2 E ‹_› ‹_›)

theorem locallyNull_iUnion : Specs.D11.Ch20.LocalNullVariant.locallyNull_iUnion := by
  intro X _ μ N hN
  refine ⟨MeasurableSet.iUnion fun n => (hN n).1, fun E hE hfin => ?_⟩
  rw [iUnion_inter]
  exact measure_iUnion_null fun n => (hN n).2 E hE hfin

theorem testingMeasure_null_iff : Specs.D11.Ch20.LocalNullVariant.testingMeasure_null_iff := by
  intro X _ μ N hN
  rw [TestingMeasure, Measure.sum_apply_eq_zero' hN]
  constructor
  · intro h
    exact ⟨hN, fun E hE hfin => by
      simpa only [Measure.restrict_apply hN] using h ⟨E, hE, hfin⟩⟩
  · intro h E
    rw [Measure.restrict_apply hN]
    exact h.2 E.val E.property.1 E.property.2

theorem classOf_eq_iff : Specs.D11.Ch20.LocalNullVariant.classOf_eq_iff := by
  intro X _ 𝕜 _ μ f g
  rw [ClassOf, ClassOf, MemLp.toLp_eq_toLp_iff]
  exact testingMeasure_null_iff μ _ (measurableSet_eq_fun f.property.1 g.property.1).compl

theorem classOf_add : Specs.D11.Ch20.LocalNullVariant.classOf_add := by
  intro X _ 𝕜 _ μ f g
  exact MemLp.toLp_add (boundedMemLp μ f) (boundedMemLp μ g)

theorem classOf_smul : Specs.D11.Ch20.LocalNullVariant.classOf_smul := by
  intro X _ 𝕜 _ μ c f
  apply Lp.ext
  filter_upwards [(boundedMemLp μ (c • f)).coeFn_toLp,
    Lp.coeFn_smul c (ClassOf μ f), (boundedMemLp μ f).coeFn_toLp] with x h1 h2 h3
  change (ClassOf μ (c • f)) x = (c • ClassOf μ f) x
  calc
    _ = c • f.val x := h1
    _ = c • (ClassOf μ f) x := congrArg (c • ·) h3.symm
    _ = _ := h2.symm

/-- Attainment of the essential bound for our auxiliary measure, including the
zero measure. This uses only the scalar L-infinity bound theorem. -/
lemma norm_bound {X : Type u} [MeasurableSpace X] (μ : Measure X) {𝕜 : Type v} [RCLike 𝕜]
    (q : LocalLInfinity 𝕜 μ) : ∀ᵐ x ∂TestingMeasure μ, ‖q x‖ ≤ ‖q‖ := by
  simpa only [← toReal_eLpNorm, Lp.norm_def] using ae_le_lpNorm_exponent_top (Lp.memLp q)

/-- Exact local level-set test for a quotient norm bound. -/
lemma classOf_norm_le_iff {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
    (μ : Measure X) (f : BoundedMeasurable X 𝕜) (C : ℝ) (hC : 0 ≤ C) :
    ‖ClassOf μ f‖ ≤ C ↔ LocallyNull μ {x | C < ‖f.val x‖} := by
  have hmeas : MeasurableSet {x | C < ‖f.val x‖} :=
    measurableSet_lt measurable_const f.property.1.norm
  rw [← testingMeasure_null_iff μ _ hmeas]
  have hae : (∀ᵐ x ∂TestingMeasure μ, ‖f.val x‖ ≤ C) ↔
      TestingMeasure μ {x | C < ‖f.val x‖} = 0 := by
    simp only [ae_iff, not_le]
  rw [← hae]
  constructor
  · intro h
    filter_upwards [norm_bound μ (ClassOf μ f), (boundedMemLp μ f).coeFn_toLp] with x hx heq
    exact heq ▸ hx.trans h
  · intro h
    rw [ClassOf, Lp.norm_toLp, eLpNorm_exponent_top (boundedMemLp μ f).aestronglyMeasurable]
    have hb := eLpNormEssSup_le_of_ae_bound h
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [ENNReal.toReal_ofReal hC] using ht

theorem norm_formula : Specs.D11.Ch20.LocalNullVariant.norm_formula := by
  intro X _ 𝕜 _ μ f
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨norm_nonneg _, (classOf_norm_le_iff μ f _ (norm_nonneg _)).mp le_rfl⟩, ?_⟩
  intro C hC
  exact (classOf_norm_le_iff μ f C hC.1).mpr hC.2

theorem norm_well_defined : Specs.D11.Ch20.LocalNullVariant.norm_well_defined := by
  intro X _ 𝕜 _ μ f g h
  rw [← norm_formula μ f, ← norm_formula μ g, (classOf_eq_iff μ f g).mpr h]

theorem norm_nonneg : Specs.D11.Ch20.LocalNullVariant.norm_nonneg := by
  intro X _ 𝕜 _ μ q
  exact _root_.norm_nonneg q

theorem norm_triangle : Specs.D11.Ch20.LocalNullVariant.norm_triangle := by
  intro X _ 𝕜 _ μ q r
  exact norm_add_le q r

theorem norm_homogeneous : Specs.D11.Ch20.LocalNullVariant.norm_homogeneous := by
  intro X _ 𝕜 _ μ c q
  exact norm_smul c q

theorem norm_definite : Specs.D11.Ch20.LocalNullVariant.norm_definite := by
  intro X _ 𝕜 _ μ q
  exact norm_eq_zero

theorem bounded_representative : Specs.D11.Ch20.LocalNullVariant.bounded_representative := by
  intro X _ 𝕜 _ μ q
  classical
  let S : Set X := {x | ‖q x‖ ≤ ‖q‖}
  have hq : Measurable (q : X → 𝕜) := (Lp.stronglyMeasurable q).measurable
  have hS : MeasurableSet S := measurableSet_le hq.norm measurable_const
  let h : X → 𝕜 := S.indicator q
  have hb : ∀ x, ‖h x‖ ≤ ‖q‖ := by
    intro x
    by_cases hx : x ∈ S
    · simpa only [h, indicator_of_mem hx] using (show ‖q x‖ ≤ ‖q‖ from hx)
    · simp only [h, indicator_of_notMem hx, norm_zero]
      exact _root_.norm_nonneg _
  let f : BoundedMeasurable X 𝕜 :=
    ⟨h, hq.indicator hS, ‖q‖, _root_.norm_nonneg _, hb⟩
  refine ⟨f, ?_, hb⟩
  apply Lp.ext
  filter_upwards [(boundedMemLp μ f).coeFn_toLp, norm_bound μ q] with x hx hbound
  exact hx.trans (indicator_of_mem (show x ∈ S from hbound) _)

theorem localEssentiallyBounded_representative :
    Specs.D11.Ch20.LocalNullVariant.localEssentiallyBounded_representative := by
  intro X _ 𝕜 _ μ g hg h
  obtain ⟨C, hC, hN⟩ := h
  classical
  let S : Set X := {x | ‖g x‖ ≤ C}
  have hS : MeasurableSet S := measurableSet_le hg.norm measurable_const
  let f : BoundedMeasurable X 𝕜 := ⟨S.indicator g, hg.indicator hS, C, hC, by
    intro x
    by_cases hx : x ∈ S
    · simpa only [indicator_of_mem hx] using (show ‖g x‖ ≤ C from hx)
    · simp only [indicator_of_notMem hx, norm_zero]
      exact hC⟩
  refine ⟨f, locallyNull_subset μ _ _ hN
    (measurableSet_eq_fun f.property.1 hg).compl ?_⟩
  intro x hx
  by_contra hn
  change ¬ C < ‖g x‖ at hn
  have hxS : x ∈ S := le_of_not_gt hn
  exact hx (indicator_of_mem hxS _)

/-- On a single infinite atom, all finite-measure tests are empty. -/
theorem localNull_can_be_nonnull : Specs.D11.Ch20.LocalNullVariant.localNull_can_be_nonnull := by
  letI : MeasurableSpace Unit := ⊤
  let μ : Measure Unit := (∞ : ℝ≥0∞) • Measure.dirac ()
  refine ⟨⊤, μ, univ, ⟨MeasurableSet.univ, ?_⟩, ?_⟩
  · intro E _ hfin
    rw [univ_inter]
    by_cases h : () ∈ E
    · have htop : μ E = ∞ := by simp [μ, Measure.smul_apply, Measure.dirac_apply_of_mem h]
      exact False.elim ((not_lt_of_ge le_top) (htop ▸ hfin))
    · have he : E = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        cases x
        exact h hx
      simp [he]
  · simp [μ, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ ())]

end D11.Ch20.LocalNullVariant
