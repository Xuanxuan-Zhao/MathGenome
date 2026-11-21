import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Caratheodory
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion

/-!
Independent specification of paper.tex:695–728.

The native outer measure of a measure is used only together with its exact
measurable-envelope formula on arbitrary subsets. It does not enlarge the
original sigma-algebra. Equality with the *full* Carathéodory sigma-algebra
requires sigma-finiteness. Measure agreement is stated on their common domain.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace Specs.D11.Ch02.InducedOuterCompletion

def inducedOuterMeasure_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → OuterMeasure α

def inducedOuterMeasure_value : inducedOuterMeasure_type.{u} :=
  fun μ => μ.toOuterMeasure

def inducedOuterMeasure_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α),
    inducedOuterMeasure_value μ E =
      ⨅ (A : Set α) (_ : E ⊆ A) (_ : MeasurableSet A), μ A

def inducedOuterMeasure_eq_sInf : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α),
    inducedOuterMeasure_value μ E =
      sInf {r : ℝ≥0∞ | ∃ A : Set α, E ⊆ A ∧ MeasurableSet A ∧ r = μ A}

def original_measurable : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α),
    m ≤ Caratheodory.measurableSpace_value (inducedOuterMeasure_value μ)

def caratheodory_eq_completion : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ],
    Caratheodory.measurableSpace_value (inducedOuterMeasure_value μ) =
      Completion.completedSpace_value μ

def caratheodory_iff_sandwiched : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (E : Set α),
    Caratheodory.isMeasurable_value (inducedOuterMeasure_value μ) E ↔
      _root_.D11.Ch02.Completion.Sandwiched μ E

def measure_eq_completion : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (E : Set α),
    MeasurableSet[Completion.completedSpace_value μ] E →
      Caratheodory.measure_value (inducedOuterMeasure_value μ) E =
        Completion.completedMeasure_value μ E

end Specs.D11.Ch02.InducedOuterCompletion
