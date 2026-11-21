import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.Vitali
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.EuclideanProductCompletion
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.Sections

/-! Independent statements for paper.tex:2836–2846.
The real set V is transported by the sole coordinate to the already shared
Euclidean one-space, exactly as in the upstream Vitali specification.
All products below are ordinary products of the completed Lebesgue factors;
only `completedSpace_value` denotes a further completion. -/

open Set MeasureTheory
open D11.Ch03 D11.Ch03.Vitali

namespace D11.Ch08.CompletionSectionsFailure

/-- The source's {0} × V, using the canonical real/one-space coordinates. -/
def verticalSet (V : Set ℝ) : Set (Point 1 × Point 1) :=
  ({0} : Set (Point 1)) ×ˢ inOneSpace V

/-- The measurable null rectangle containing every such V ⊆ [0,1]. -/
def nullRectangle : Set (Point 1 × Point 1) := verticalSet (Icc 0 1)

end D11.Ch08.CompletionSectionsFailure

namespace Specs.D11.Ch08.CompletionSectionsFailure

open _root_.D11.Ch08.CompletionSectionsFailure
open _root_.Specs.D11.Ch03.LebesgueMeasures
open _root_.Specs.D11.Ch08.EuclideanProductCompletion
open _root_.Specs.D11.Ch02.Completion

/-- Both factors are complete, whereas the displayed ordinary-product
rectangle is measurable and has mass zero. -/
def complete_factors_null_rectangle : Prop :=
  @Measure.IsComplete (Point 1) (lebesgueSpace_value 1) (lebesgue_value 1) ∧
  MeasurableSet[factorSpace 1 1] nullRectangle ∧
  factorProduct 1 1 nullRectangle = 0

/-- Any non-Lebesgue-measurable V ⊆ [0,1] gives the precise obstruction,
including its value and section in the completed product. -/
def vertical_obstruction : Prop :=
  ∀ V : Set ℝ, V ⊆ Icc 0 1 →
    ¬ MeasurableSet[lebesgueSpace_value 1] (inOneSpace V) →
    verticalSet V ⊆ nullRectangle ∧
    MeasurableSet[completedSpace_value (m := factorSpace 1 1) (factorProduct 1 1)]
      (verticalSet V) ∧
    completedMeasure_value (m := factorSpace 1 1) (factorProduct 1 1) (verticalSet V) = 0 ∧
    {y : Point 1 | ((0 : Point 1), y) ∈ verticalSet V} = inOneSpace V ∧
    {y : ℝ | ((0 : Point 1), WithLp.toLp 2 (fun _ : Fin 1 => y)) ∈ verticalSet V} = V ∧
    ¬ MeasurableSet[factorSpace 1 1] (verticalSet V)

/-- An actual witness exists; its zero section fails measurability even though
the set is completed-product measurable. No completeness failure is assumed. -/
def completion_sections_failure : Prop :=
  (∃ V : Set ℝ, V ⊆ Icc 0 1 ∧
    ¬ MeasurableSet[lebesgueSpace_value 1] (inOneSpace V) ∧
    MeasurableSet[completedSpace_value (m := factorSpace 1 1) (factorProduct 1 1)]
      (verticalSet V) ∧
    ¬ MeasurableSet[factorSpace 1 1] (verticalSet V) ∧
    ¬ MeasurableSet[lebesgueSpace_value 1]
      {y : Point 1 | ((0 : Point 1), y) ∈ verticalSet V}) ∧
  ¬ @Measure.IsComplete (Point 1 × Point 1) (factorSpace 1 1) (factorProduct 1 1)

end Specs.D11.Ch08.CompletionSectionsFailure
