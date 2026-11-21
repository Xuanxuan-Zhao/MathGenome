import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MaximalLemma
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.MeasureDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.CompositionIsometry
import Mathlib.Tactic.Linarith

namespace D13Unified.Ch19.MaximalLemma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
universe u v

abbrev finiteMaximum {X : Type u} (T : X → X) (f : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  Specs.D13Unified.Ch19.MaximalLemma.finiteMaximum T f N x
abbrev finitePositiveSet {X : Type u} (T : X → X) (f : X → ℝ) (N : ℕ) : Set X :=
  Specs.D13Unified.Ch19.MaximalLemma.finitePositiveSet T f N
abbrev infinitePositiveSet {X : Type u} (T : X → X) (f : X → ℝ) : Set X :=
  Specs.D13Unified.Ch19.MaximalLemma.infinitePositiveSet T f
abbrev maximalAverageSet {X : Type u} {𝕜 : Type v} [NormedAddCommGroup 𝕜]
    (T : X → X) (h : X → 𝕜) (α : ℝ) : Set X :=
  Specs.D13Unified.Ch19.MaximalLemma.maximalAverageSet T h α

@[simp] theorem finiteMaximum_zero {X : Type u} (T : X → X) (f : X → ℝ) (x : X) :
    finiteMaximum T f 0 x = 0 := rfl

@[simp] theorem finiteMaximum_succ {X : Type u} (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    finiteMaximum T f (n + 1) x = max (finiteMaximum T f n x)
      (MeasureDefinitions.ergodicSum T f (n + 1) x) := rfl

theorem finiteMaximum_characterization :
    Specs.D13Unified.Ch19.MaximalLemma.finiteMaximum_characterizationStatement.{u} := by
  intro X T f N x
  induction N with
  | zero =>
    refine ⟨le_rfl, ?_, 0, le_rfl, rfl⟩
    intro k hk
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact le_rfl
  | succ N ih =>
    refine ⟨le_trans ih.1 (le_max_left _ _), ?_, ?_⟩
    · intro k hk
      rcases Nat.eq_or_lt_of_le hk with hk | hk
      · subst k
        exact le_max_right _ _
      · exact le_trans (ih.2.1 k (Nat.le_of_lt_succ hk)) (le_max_left _ _)
    · rcases le_total (finiteMaximum T f N x) (MeasureDefinitions.ergodicSum T f (N+1) x)
        with h | h
      · exact ⟨N+1, le_rfl, max_eq_right h⟩
      · obtain ⟨k, hk, heq⟩ := ih.2.2
        exact ⟨k, hk.trans (Nat.le_succ N), (max_eq_left h).trans heq⟩

theorem finiteMaximum_pos :
    Specs.D13Unified.Ch19.MaximalLemma.finiteMaximum_posStatement.{u} := by
  intro X T f N
  ext x
  constructor
  · rintro ⟨k, hk, hkN, hpos⟩
    exact hpos.trans_le ((finiteMaximum_characterization T f N x).2.1 k hkN)
  · intro hx
    obtain ⟨k, hkN, heq⟩ := (finiteMaximum_characterization T f N x).2.2
    have hk : 0 < k := by
      by_contra h
      have : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h)
      subst k
      simp [heq, Specs.D13Unified.Ch19.MeasureDefinitions.ergodicSum] at hx
    exact ⟨k, hk, hkN, heq ▸ hx⟩

section Regularity
variable {X : Type u} [MeasurableSpace X] {T : X → X} {μ : Measure X}

theorem integrable_ergodicSum (hT : MeasureDefinitions.PreservesMeasure T μ)
    {f : X → ℝ} (hf : Integrable f μ) (n : ℕ) :
    Integrable (MeasureDefinitions.ergodicSum T f n) μ := by
  change Integrable (birkhoffSum T f n) μ
  induction n with
  | zero => simp
  | succ n ih =>
    erw [birkhoffSum_succ]
    exact ih.add ((hT.iterate n).integrable_comp_of_integrable hf)

theorem integrable_finiteMaximum [IsProbabilityMeasure μ]
    (hT : MeasureDefinitions.PreservesMeasure T μ)
    {f : X → ℝ} (hf : Integrable f μ) (n : ℕ) :
    Integrable (finiteMaximum T f n) μ := by
  induction n with
  | zero => exact integrable_zero X ℝ μ
  | succ n ih =>
    exact ih.sup (integrable_ergodicSum hT hf (n + 1))

theorem finiteRegularity :
    Specs.D13Unified.Ch19.MaximalLemma.finiteRegularityStatement.{u} := by
  intro X _ T μ _ hT f hf N
  have hM := integrable_finiteMaximum hT hf N
  refine ⟨hM, ?_⟩
  erw [finiteMaximum_pos T f _]
  exact nullMeasurableSet_lt aemeasurable_const hM.aestronglyMeasurable.aemeasurable

omit [MeasurableSpace X] in
theorem finitePositiveSet_monotone (T : X → X) (f : X → ℝ) :
    Monotone (finitePositiveSet T f) := by
  intro m n hmn x hx
  obtain ⟨k, hk, hkm, hpos⟩ := hx
  exact ⟨k, hk, hkm.trans hmn, hpos⟩

omit [MeasurableSpace X] in
theorem infinitePositiveSet_eq_iUnion (T : X → X) (f : X → ℝ) :
    infinitePositiveSet T f = ⋃ N : ℕ, finitePositiveSet T f N := by
  ext x
  constructor
  · rintro ⟨k, hk, hpos⟩
    exact mem_iUnion.mpr ⟨k, k, hk, le_rfl, hpos⟩
  · intro hx
    obtain ⟨N, k, hk, _, hpos⟩ := mem_iUnion.mp hx
    exact ⟨k, hk, hpos⟩

theorem measurable_ergodicSum (hT : Measurable T) {f : X → ℝ}
    (hf : Measurable f) (n : ℕ) : Measurable (MeasureDefinitions.ergodicSum T f n) := by
  change Measurable (birkhoffSum T f n)
  induction n with
  | zero => erw [birkhoffSum_zero]; exact measurable_const
  | succ n ih =>
    erw [birkhoffSum_succ]
    exact ih.add (hf.comp (hT.iterate n))

theorem measurable_finiteMaximum (hT : Measurable T) {f : X → ℝ}
    (hf : Measurable f) (n : ℕ) : Measurable (finiteMaximum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (measurable_ergodicSum hT hf (n + 1))

theorem measurable_sets : Specs.D13Unified.Ch19.MaximalLemma.measurableStatement.{u} := by
  intro X _ T hT f hf
  have hfinite : ∀ n, Measurable (finiteMaximum T f n) ∧
      MeasurableSet (finitePositiveSet T f n) := by
    intro n
    have hM := measurable_finiteMaximum hT hf n
    refine ⟨hM, ?_⟩
    exact (congrArg (fun A : Set X => MeasurableSet A)
      (finiteMaximum_pos T f n)).mpr (measurableSet_lt measurable_const hM)
  refine ⟨hfinite, ?_⟩
  exact (congrArg (fun A : Set X => MeasurableSet A)
    (infinitePositiveSet_eq_iUnion T f)).mpr
      (MeasurableSet.iUnion (fun n => (hfinite n).2))
end Regularity

/-- The pointwise coboundary bound behind the finite estimate. -/
theorem indicator_ge_coboundary {X : Type u} (T : X → X) (f : X → ℝ)
    (N : ℕ) (x : X) :
    finiteMaximum T f N x - finiteMaximum T f N (T x) ≤
      (finitePositiveSet T f N).indicator f x := by
  classical
  by_cases hx : x ∈ finitePositiveSet T f N
  · erw [indicator_of_mem hx]
    have hpos : 0 < finiteMaximum T f N x := by
      simpa only [finiteMaximum_pos T f N, mem_ofPred_eq] using hx
    obtain ⟨k, hkN, heq⟩ := (finiteMaximum_characterization T f N x).2.2
    cases k with
    | zero =>
      simp [Specs.D13Unified.Ch19.MeasureDefinitions.ergodicSum] at heq
      linarith
    | succ k =>
      have hbound := (finiteMaximum_characterization T f N (T x)).2.1 k
        (Nat.le_trans (Nat.le_succ k) hkN)
      change finiteMaximum T f N x = birkhoffSum T f (k+1) x at heq
      erw [birkhoffSum_succ_apply'] at heq
      change birkhoffSum T f k (T x) ≤ finiteMaximum T f N (T x) at hbound
      linarith
  · erw [indicator_of_notMem hx]
    have hnonneg := (finiteMaximum_characterization T f N x).1
    have hcomp := (finiteMaximum_characterization T f N (T x)).1
    have hnonpos : finiteMaximum T f N x ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      apply hx
      simpa only [finiteMaximum_pos T f N, mem_ofPred_eq] using hpos
    linarith

theorem finite_maximal : Specs.D13Unified.Ch19.MaximalLemma.finite_maximalStatement.{u} := by
  intro X _ T μ _ hT f hf N
  have hM := integrable_finiteMaximum hT hf N
  have hcomp := hT.integrable_comp_of_integrable hM
  have hset := (finiteRegularity T μ hT f hf N).2
  have hint := (CompositionIsometry.integration T μ hT).2 ℝ (finiteMaximum T f N) hM
  have hle := integral_mono (hM.sub hcomp) (hf.indicator₀ hset)
    (indicator_ge_coboundary T f N)
  change (∫ x, finiteMaximum T f N x - finiteMaximum T f N (T x) ∂μ) ≤
    (∫ x, (finitePositiveSet T f N).indicator f x ∂μ) at hle
  erw [integral_sub hM hcomp, hint.2, sub_self, integral_indicator₀ hset] at hle
  exact hle

theorem infinite_passage : Specs.D13Unified.Ch19.MaximalLemma.infinite_passageStatement.{u} := by
  intro X _ T μ _ hT f hf
  have hm := finitePositiveSet_monotone T f
  have heq := infinitePositiveSet_eq_iUnion T f
  have hsets := fun N => (finiteRegularity T μ hT f hf N).2
  refine ⟨hm, heq, ?_, ?_⟩
  · exact (congrArg (fun A : Set X => NullMeasurableSet A μ) heq).mpr
      (NullMeasurableSet.iUnion hsets)
  · exact (congrArg (fun A : Set X =>
      Tendsto (fun N => ∫ x in finitePositiveSet T f N, f x ∂μ) atTop
        (𝓝 (∫ x in A, f x ∂μ))) heq).mpr
          (tendsto_setIntegral_of_monotone₀ hsets hm hf.integrableOn)

theorem infinite_maximal : Specs.D13Unified.Ch19.MaximalLemma.infinite_maximalStatement.{u} := by
  intro X _ T μ _ hT f hf
  exact ge_of_tendsto (infinite_passage T μ hT f hf).2.2.2
    (Eventually.of_forall (finite_maximal T μ hT f hf))

/-- Positive sums of the shifted observable are exactly the strict maximal
average superlevel set. No boundedness of the sequence of averages is needed. -/
theorem averageSet_eq : Specs.D13Unified.Ch19.MaximalLemma.averageSet_eqStatement.{u,v} := by
  intro X 𝕜 _ T h α
  ext x
  change (∃ n : ℕ, 0 < n ∧ α < birkhoffAverage ℝ T (fun y => ‖h y‖) n x) ↔
    (∃ n : ℕ, 0 < n ∧ 0 < birkhoffSum T (fun y => ‖h y‖ - α) n x)
  have hs (n : ℕ) :
      birkhoffSum T (fun y => ‖h y‖ - α) n x =
        birkhoffSum T (fun y => ‖h y‖) n x - (n : ℝ) * α := by
    simp [birkhoffSum, Finset.sum_sub_distrib]
  have havg (n : ℕ) : birkhoffAverage ℝ T (fun y => ‖h y‖) n x =
      birkhoffSum T (fun y => ‖h y‖) n x / (n : ℝ) := by
    simp only [birkhoffAverage, smul_eq_mul, div_eq_inv_mul]
  constructor
  · rintro ⟨n, hn, hav⟩
    refine ⟨n, hn, ?_⟩
    rw [hs n]
    rw [havg n] at hav
    have hmul := (lt_div_iff₀ (Nat.cast_pos.mpr hn)).mp hav
    linarith
  · rintro ⟨n, hn, hsum⟩
    refine ⟨n, hn, ?_⟩
    rw [hs n] at hsum
    rw [havg n]
    apply (lt_div_iff₀ (Nat.cast_pos.mpr hn)).mpr
    linarith

theorem maximal_inequality : Specs.D13Unified.Ch19.MaximalLemma.maximal_inequalityStatement.{u,v} := by
  intro X _ 𝕜 _ T μ _ hT h hh α hα
  let E := maximalAverageSet T h α
  have hi : Integrable (fun x => ‖h x‖ - α) μ := hh.norm.sub (integrable_const α)
  have hE : NullMeasurableSet E μ := by
    exact (congrArg (fun A : Set X => NullMeasurableSet A μ)
      (averageSet_eq T h α)).mpr (infinite_passage T μ hT _ hi).2.2.1
  refine ⟨hE, ?_⟩
  have hnonneg : 0 ≤ ∫ x in E, (‖h x‖ - α) ∂μ := by
    exact (congrArg (fun A : Set X => 0 ≤ ∫ x in A, (‖h x‖ - α) ∂μ)
      (averageSet_eq T h α)).mpr (infinite_maximal T μ hT _ hi)
  erw [integral_sub hh.norm.integrableOn (integrable_const α), integral_const,
    measureReal_def, Measure.restrict_apply_univ, smul_eq_mul] at hnonneg
  have hbound : (∫ x in E, ‖h x‖ ∂μ) ≤ ∫ x, ‖h x‖ ∂μ :=
    setIntegral_le_integral hh.norm (ae_of_all μ (fun x => norm_nonneg (h x)))
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ E)
    (div_nonneg (integral_nonneg (fun x => norm_nonneg (h x))) hα.le)).mpr
  apply (le_div_iff₀ hα).mpr
  change (μ E).toReal * α ≤ ∫ x, ‖h x‖ ∂μ
  linarith

end
end D13Unified.Ch19.MaximalLemma
