import MathGenome.Internal.RealAnalysis.D11.Ch02.Caratheodory
import MathGenome.Internal.RealAnalysis.D11.Ch02.Completion
import MathGenome.Internal.RealAnalysis.D11.Ch01.ExhaustionRestriction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.InducedOuterCompletion

/-!
# Induced outer measure and sigma-finite completion

The measurable-envelope infimum agrees with the native outer measure on every
subset, independently of sigma-finiteness. To identify its full splitting
domain, first enclose a finite-mass splitting set in a measurable set of the
same mass. Splitting that envelope and cancelling its finite mass shows that
the difference is null. A sigma-finite exhaustion reduces a general splitting
set to countably many such sets. The converse follows by splitting null
measurable sets. No nonempty-space or finite-total-mass hypothesis is used.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch02.InducedOuterCompletion

/-- The outer measure given by measurable envelopes; see its formula below. -/
def inducedOuterMeasure {α : Type u} [MeasurableSpace α] (μ : Measure α) :
    OuterMeasure α := μ.toOuterMeasure

theorem inducedOuterMeasure_apply {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) :
    inducedOuterMeasure μ E =
      ⨅ (A : Set α) (_ : E ⊆ A) (_ : MeasurableSet A), μ A :=
  measure_eq_iInf E

theorem inducedOuterMeasure_eq_sInf {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) :
    inducedOuterMeasure μ E =
      sInf {r : ℝ≥0∞ | ∃ A : Set α, E ⊆ A ∧ MeasurableSet A ∧ r = μ A} := by
  rw [inducedOuterMeasure_apply]
  apply le_antisymm
  · apply le_sInf
    rintro r ⟨A, hEA, hA, rfl⟩
    exact iInf_le_of_le A (iInf_le_of_le hEA (iInf_le_of_le hA le_rfl))
  · refine le_iInf fun A => le_iInf fun hEA => le_iInf fun hA => ?_
    exact sInf_le ⟨A, hEA, hA, rfl⟩

theorem original_measurable {α : Type u} [m : MeasurableSpace α]
    (μ : Measure α) : m ≤ Caratheodory.measurableSpace (inducedOuterMeasure μ) :=
  le_toOuterMeasure_caratheodory μ

/-- Finite outer mass permits cancellation in the measurable-envelope split. -/
theorem nullMeasurableSet_of_caratheodory_of_lt_top {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : Set α)
    (hE : Caratheodory.isMeasurable (inducedOuterMeasure μ) E)
    (hfin : μ E < ∞) : NullMeasurableSet E μ := by
  obtain ⟨B, hEB, hB, hmass⟩ := exists_measurable_superset μ E
  have hsplit := hE B
  change μ B = μ (B ∩ E) + μ (B \ E) at hsplit
  rw [inter_eq_right.mpr hEB, hmass] at hsplit
  have hnull : μ (B \ E) = 0 := by
    apply (ENNReal.add_right_inj hfin.ne).mp
    simpa only [add_zero] using hsplit.symm
  have hdiff := hB.nullMeasurableSet.diff (NullMeasurableSet.of_null hnull)
  simpa only [sdiff_sdiff_cancel_left hEB] using hdiff

theorem caratheodory_eq_completion {α : Type u} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] :
    Caratheodory.measurableSpace (inducedOuterMeasure μ) =
      Completion.completedSpace μ := by
  apply le_antisymm
  · intro E hE
    change NullMeasurableSet E μ
    obtain ⟨F, hF, _hmono, hcover⟩ :=
      (D11.Ch01.ExhaustionRestriction.sigmaFinite_iff_increasing_exhaustion μ).mp
        inferInstance
    have hparts : ∀ n, NullMeasurableSet (E ∩ F n) μ := by
      intro n
      apply nullMeasurableSet_of_caratheodory_of_lt_top μ
      · exact (inducedOuterMeasure μ).isCaratheodory_inter hE
          (original_measurable μ _ (hF n).1)
      · exact (measure_mono inter_subset_right).trans_lt (hF n).2
    have hunion := NullMeasurableSet.iUnion hparts
    simpa only [← inter_iUnion, hcover, inter_univ] using hunion
  · intro E hE
    change NullMeasurableSet E μ at hE
    exact fun A => (measure_inter_add_sdiff₀ A hE).symm

theorem caratheodory_iff_sandwiched {α : Type u} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (E : Set α) :
    Caratheodory.isMeasurable (inducedOuterMeasure μ) E ↔
      Completion.Sandwiched μ E := by
  rw [← Caratheodory.measurableSet_iff, caratheodory_eq_completion,
    Completion.completed_measurable_iff]

theorem measure_eq_completion {α : Type u} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (E : Set α)
    (hE : MeasurableSet[Completion.completedSpace μ] E) :
    Caratheodory.measure (inducedOuterMeasure μ) E =
      Completion.completedMeasure μ E := by
  have hC : Caratheodory.isMeasurable (inducedOuterMeasure μ) E := by
    change MeasurableSet[Caratheodory.measurableSpace (inducedOuterMeasure μ)] E
    rwa [caratheodory_eq_completion]
  exact Caratheodory.measure_apply _ E hC

end D11.Ch02.InducedOuterCompletion
