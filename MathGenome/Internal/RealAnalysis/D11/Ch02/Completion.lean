import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion

/-!
# Completion of an arbitrary measure

The canonical library completion is identified with the source's literal
sandwich sigma-algebra. Its native measure structure supplies countable
additivity; the sandwich value, generators, and complete-extension universal
property are proved below. Null differences are used without subtracting
possibly infinite endpoint masses.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v

namespace D11.Ch02.Completion

abbrev completedSpace {α : Type u} [m : MeasurableSpace α] (μ : Measure α) :
    MeasurableSpace α := eventuallyMeasurableSpace m (ae μ)

noncomputable def completedMeasure {α : Type u} [m : MeasurableSpace α] (μ : Measure α) :
    @Measure α (completedSpace μ) := μ.completion

/-- The bridge from null measurability to the exact sandwich in the manuscript. -/
theorem completed_measurable_iff {α : Type u} [m : MeasurableSpace α]
    (μ : Measure α) (E : Set α) :
    MeasurableSet[completedSpace μ] E ↔ Sandwiched μ E := by
  change NullMeasurableSet E μ ↔ _
  constructor
  · intro hE
    obtain ⟨A, hAE, hA, hAs⟩ := hE.exists_measurable_subset_ae_eq
    obtain ⟨B, hEB, hB, hBs⟩ := hE.exists_measurable_superset_ae_eq
    exact ⟨A, B, hA, hB, hAE, hEB, ae_le_set.mp (hBs.trans hAs.symm).le⟩
  · rintro ⟨A, B, hA, _hB, hAE, hEB, hnull⟩
    have hEA : μ (E \ A) = 0 :=
      measure_mono_null (sdiff_subset_sdiff_left hEB) hnull
    exact ⟨A, hA, (ae_le_set.mpr hEA).antisymm hAE.eventuallySubset⟩

theorem sandwich_value {α : Type u} [m : MeasurableSpace α] (μ : Measure α)
    (E A B : Set α) (_hA : MeasurableSet A) (_hB : MeasurableSet B)
    (hAE : A ⊆ E) (hEB : E ⊆ B) (hnull : μ (B \ A) = 0) :
    completedMeasure μ E = μ A ∧ μ A = μ B := by
  obtain ⟨hAEμ, hEBμ⟩ := measure_eq_measure_of_between_null_sdiff hAE hEB hnull
  exact ⟨hAEμ.symm, hAEμ.trans hEBμ⟩

theorem well_defined : Specs.D11.Ch02.Completion.well_defined := by
  intro α m μ E A B C D hA hB hAE hEB hBA hC hD hCE hED hDC
  have h₁ := sandwich_value μ E A B hA hB hAE hEB hBA
  have h₂ := sandwich_value μ E C D hC hD hCE hED hDC
  exact ⟨h₁.1.symm.trans h₂.1, h₁.2.symm.trans (h₁.1.symm.trans h₂.1) |>.trans h₂.2⟩

theorem extends_original {α : Type u} [m : MeasurableSpace α] (μ : Measure α) :
    m ≤ completedSpace μ ∧
      ∀ E : Set α, MeasurableSet[m] E → completedMeasure μ E = μ E :=
  ⟨le_eventuallyMeasurableSpace, fun _ _ => rfl⟩

theorem countable_additivity {α : Type u} {ι : Type v} [m : MeasurableSpace α]
    [Countable ι] (μ : Measure α) (E : ι → Set α)
    (hE : ∀ i, MeasurableSet[completedSpace μ] (E i))
    (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
    completedMeasure μ (⋃ i, E i) = ∑' i, completedMeasure μ (E i) :=
  @measure_iUnion ι α (completedSpace μ) (completedMeasure μ) _ E hd hE

theorem completed_empty {α : Type u} [m : MeasurableSpace α] (μ : Measure α) :
    completedMeasure μ ∅ = 0 := measure_empty

theorem completed_complete {α : Type u} [m : MeasurableSpace α] (μ : Measure α) :
    @Measure.IsComplete α (completedSpace μ) (completedMeasure μ) :=
  Measure.completion.isComplete μ

theorem completed_subset_null {α : Type u} [m : MeasurableSpace α] (μ : Measure α)
    (E N : Set α) (hEN : E ⊆ N) (_hN : MeasurableSet[completedSpace μ] N)
    (hnull : completedMeasure μ N = 0) :
    MeasurableSet[completedSpace μ] E ∧ completedMeasure μ E = 0 := by
  have hE : completedMeasure μ E = 0 := measure_mono_null hEN hnull
  exact ⟨(completed_complete μ).out E hE, hE⟩

theorem generated_characterization {α : Type u} [m : MeasurableSpace α]
    (μ : Measure α) :
    completedSpace μ = MeasurableSpace.generateFrom (generators μ) := by
  apply le_antisymm
  · intro E hE
    obtain ⟨A, B, hA, hB, hAE, hEB, hnull⟩ := (completed_measurable_iff μ E).mp hE
    have hA' : MeasurableSet[MeasurableSpace.generateFrom (generators μ)] A :=
      MeasurableSpace.measurableSet_generateFrom (Or.inl hA)
    have hEA' : MeasurableSet[MeasurableSpace.generateFrom (generators μ)] (E \ A) :=
      MeasurableSpace.measurableSet_generateFrom
        (Or.inr ⟨B \ A, sdiff_subset_sdiff_left hEB, hB.diff hA, hnull⟩)
    simpa only [union_sdiff_cancel hAE] using hA'.union hEA'
  · apply MeasurableSpace.generateFrom_le
    intro E hE
    rcases hE with hE | ⟨N, hEN, hN, hnull⟩
    · exact hE.nullMeasurableSet
    · exact NullMeasurableSet.of_null (measure_mono_null hEN hnull)

theorem minimality {α : Type u} [m : MeasurableSpace α] (μ : @Measure α m)
    (n : MeasurableSpace α) (ν : @Measure α n) (hmn : m ≤ n)
    (hcomplete : @Measure.IsComplete α n ν)
    (hagree : ∀ E : Set α, MeasurableSet[m] E → ν E = μ E) :
    completedSpace (m := m) μ ≤ n ∧
      ∀ E : Set α, MeasurableSet[completedSpace (m := m) μ] E → ν E = completedMeasure (m := m) μ E := by
  have hle : completedSpace (m := m) μ ≤ n := by
    rw [generated_characterization (m := m) μ]
    apply MeasurableSpace.generateFrom_le
    intro E hE
    rcases hE with hE | ⟨N, hEN, hN, hnull⟩
    · exact hmn E hE
    · have hνN : ν N = 0 := (hagree N hN).trans hnull
      exact hcomplete.out E (measure_mono_null hEN hνN)
  refine ⟨hle, ?_⟩
  intro E hE
  obtain ⟨A, B, hA, hB, hAE, hEB, hnull⟩ := (completed_measurable_iff (m := m) μ E).mp hE
  have hvalue := sandwich_value (m := m) μ E A B hA hB hAE hEB hnull
  apply le_antisymm
  · calc
      ν E ≤ ν B := measure_mono hEB
      _ = μ B := hagree B hB
      _ = completedMeasure (m := m) μ E := hvalue.2.symm.trans hvalue.1.symm
  · calc
      completedMeasure (m := m) μ E = μ A := hvalue.1
      _ = ν A := (hagree A hA).symm
      _ ≤ ν E := measure_mono hAE

end D11.Ch02.Completion
