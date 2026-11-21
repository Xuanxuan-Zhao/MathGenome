import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions

/-! Canonical measure-theoretic interface for Chapter 19. -/
namespace D13Unified.Ch19.MeasureDefinitions

noncomputable section

universe u v
open Set Filter MeasureTheory
open scoped Topology symmDiff BigOperators

abbrev PreservesMeasure : Specs.D13Unified.Ch19.MeasureDefinitions.PreservesMeasureType.{u} :=
  Specs.D13Unified.Ch19.MeasureDefinitions.PreservesMeasure

abbrev InvariantModNull : Specs.D13Unified.Ch19.MeasureDefinitions.InvariantModNullType.{u} :=
  Specs.D13Unified.Ch19.MeasureDefinitions.InvariantModNull

abbrev IsErgodic : Specs.D13Unified.Ch19.MeasureDefinitions.IsErgodicType.{u} :=
  Specs.D13Unified.Ch19.MeasureDefinitions.IsErgodic

abbrev iteratePreimage : Specs.D13Unified.Ch19.MeasureDefinitions.iteratePreimageType.{u} :=
  Specs.D13Unified.Ch19.MeasureDefinitions.iteratePreimage

abbrev IsMixing : Specs.D13Unified.Ch19.MeasureDefinitions.IsMixingType.{u} :=
  Specs.D13Unified.Ch19.MeasureDefinitions.IsMixing

abbrev ergodicSum : Specs.D13Unified.Ch19.MeasureDefinitions.ergodicSumType.{u, v} :=
  Specs.D13Unified.Ch19.MeasureDefinitions.ergodicSum

abbrev ergodicAverage : Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverageType.{u, v} :=
  Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverage

theorem preservesMeasure_iff :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X),
  PreservesMeasure T μ ↔ Measurable T ∧
    ∀ E : Set X, MeasurableSet E → μ (T ⁻¹' E) = μ E := by
  intro X _ T μ
  constructor
  · intro h
    exact ⟨h.measurable, fun E hE => h.measure_preimage hE.nullMeasurableSet⟩
  · rintro ⟨hT, h⟩
    refine ⟨hT, ?_⟩
    apply Measure.ext
    intro E hE
    rw [Measure.map_apply hT hE]
    exact h E hE

theorem invariantModNull_iff :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X) (E : Set X),
  InvariantModNull T μ E ↔ μ ((T ⁻¹' E) ∆ E) = 0 := by
  intro X _ T μ E
  rfl

theorem invariantModNull_iff_ae :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X) (E : Set X),
  InvariantModNull T μ E ↔ T ⁻¹' E =ᵐ[μ] E := by
  intro X _ T μ E
  exact measure_symmDiff_eq_zero_iff

/-- The source zero-one condition, with no preservation assumption. -/
theorem isErgodic_iff :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
  [IsProbabilityMeasure μ], IsErgodic T μ ↔
    ∀ E : Set X, MeasurableSet E → InvariantModNull T μ E → μ E = 0 ∨ μ E = 1 := by
  intro X _ T μ _
  rfl

theorem isErgodic_iff_zero_one :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
  [IsProbabilityMeasure μ],
  (IsErgodic T μ ↔ ∀ E : Set X, MeasurableSet E →
    μ ((T ⁻¹' E) ∆ E) = 0 → μ E = 0 ∨ μ E = 1) := by
  intro X _ T μ _
  rfl

/-- Preservation is a separate conjunct in the native structure. Its API
extends the measurable-set zero-one law to null-measurable sets. -/
theorem nativeErgodic_iff :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
  [IsProbabilityMeasure μ], Ergodic T μ ↔ PreservesMeasure T μ ∧ IsErgodic T μ := by
  intro X _ T μ _
  constructor
  · intro h
    refine ⟨h.toMeasurePreserving, ?_⟩
    intro E hE hInv
    exact h.toPreErgodic.prob_eq_zero_or_one hE.nullMeasurableSet
      ((invariantModNull_iff_ae T μ E).mp hInv)
  · rintro ⟨hT, h⟩
    apply Ergodic.of_preimage_eq hT
    intro E hE hInv
    have hzeroone := h E hE (by
      show μ ((T ⁻¹' E) ∆ E) = 0
      simp [hInv])
    simpa only [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ,
      prob_compl_eq_zero_iff hE] using hzeroone

theorem isErgodic_iff_native :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
  [IsProbabilityMeasure μ], PreservesMeasure T μ → (IsErgodic T μ ↔ Ergodic T μ) := by
  intro X _ T μ _ hT
  rw [nativeErgodic_iff]
  exact (and_iff_right hT).symm

theorem iteratePreimage_eq :
  ∀ {X : Type u} (T : X → X) (n : ℕ) (E : Set X),
  iteratePreimage T n E = T^[n] ⁻¹' E := by
  intro X T n E
  rfl

theorem mem_iteratePreimage :
  ∀ {X : Type u} (T : X → X) (n : ℕ) (E : Set X) (x : X),
  x ∈ iteratePreimage T n E ↔ T^[n] x ∈ E := by
  intro X T n E x
  rfl

theorem iteratePreimage_zero :
  ∀ {X : Type u} (T : X → X) (E : Set X), iteratePreimage T 0 E = E := by
  intro X T E
  rfl

theorem iteratePreimage_succ :
  ∀ {X : Type u} (T : X → X) (n : ℕ) (E : Set X),
  iteratePreimage T (n + 1) E = iteratePreimage T n (T ⁻¹' E) := by
  intro X T n E
  change T^[n + 1] ⁻¹' E = T^[n] ⁻¹' (T ⁻¹' E)
  rw [Function.iterate_succ', preimage_comp]

theorem isMixing_iff :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X),
  IsMixing T μ ↔ ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℕ => μ (A ∩ (T^[n] ⁻¹' B))) atTop (𝓝 (μ A * μ B)) := by
  intro X _ T μ
  rfl

theorem preservesMeasure_iterate :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X),
  PreservesMeasure T μ → ∀ n : ℕ, PreservesMeasure T^[n] μ := by
  intro X _ T μ hT n
  exact hT.iterate n

theorem measure_iteratePreimage :
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X),
  PreservesMeasure T μ → ∀ (n : ℕ) (E : Set X), MeasurableSet E →
    μ (iteratePreimage T n E) = μ E := by
  intro X _ T μ hT n E hE
  exact (hT.iterate n).measure_preimage hE.nullMeasurableSet

theorem ergodicSum_eq_sum :
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E]
  (T : X → X) (f : X → E) (n : ℕ) (x : X),
  ergodicSum T f n x = ∑ j ∈ Finset.range n, f (T^[j] x) := by
  intro X E _ T f n x
  rfl

theorem ergodicSum_zero :
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E]
  (T : X → X) (f : X → E) (x : X), ergodicSum T f 0 x = 0 := by
  intro X E _ T f x
  exact birkhoffSum_zero_apply T f x

theorem ergodicSum_succ :
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E]
  (T : X → X) (f : X → E) (n : ℕ) (x : X),
  ergodicSum T f (n + 1) x = ergodicSum T f n x + f (T^[n] x) := by
  intro X E _ T f n x
  exact birkhoffSum_succ_apply T f n x

theorem ergodicAverage_eq :
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E] [Module ℝ E]
  (T : X → X) (f : X → E) (n : ℕ) (x : X),
  ergodicAverage T f n x = (n : ℝ)⁻¹ • ergodicSum T f n x := by
  intro X E _ _ T f n x
  rfl

theorem ergodicAverage_eq_sum :
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E] [Module ℝ E]
  (T : X → X) (f : X → E) (n : ℕ) (x : X),
  ergodicAverage T f n x = (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, f (T^[j] x) := by
  intro X E _ _ T f n x
  rfl

theorem ergodicAverage_real_eq :
  ∀ {X : Type u} (T : X → X) (f : X → ℝ) (n : ℕ), 0 < n →
  ∀ x : X, ergodicAverage T f n x = (∑ j ∈ Finset.range n, f (T^[j] x)) / (n : ℝ) := by
  intro X T f n _ x
  rw [ergodicAverage_eq_sum, smul_eq_mul, div_eq_inv_mul]

theorem ergodicAverage_one :
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E] [Module ℝ E]
  (T : X → X) (f : X → E) (x : X), ergodicAverage T f 1 x = f x := by
  intro X E _ _ T f x
  exact birkhoffAverage_one_apply ℝ T f x

end

end D13Unified.Ch19.MeasureDefinitions
