import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.EuclideanProductCompletion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent statements for paper.tex:2898–2928. The real Borel measure is
Mathlib's length-normalized real volume; its completion is used explicitly in
the second assertion. Euclidean measures and coordinates reuse the shared
covering-volume construction and completion interfaces. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
open Specs.D11.Ch02.Completion
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch05.NonnegativeIntegral
open D11.Ch03 D11.Ch08.EuclideanProductCompletion

universe u
namespace Specs.D11.Ch08.SubgraphCavalieri

/-- The real factor agrees with the existing Euclidean one-dimensional
Borel measure under the canonical coordinate identification. -/
def real_borel_identification : Prop :=
  (borelMeasure_value 1).map (fun x : Point 1 => x 0) = (volume : Measure ℝ)

/-- Both the measurable domain and the values of the completed real factor
agree with the already constructed one-dimensional Lebesgue space. -/
def real_completion_identification : Prop := ∀ A : Set ℝ,
  (MeasurableSet[completedSpace_value (volume : Measure ℝ)] A ↔
    MeasurableSet[lebesgueSpace_value 1] ((fun x : Point 1 => x 0) ⁻¹' A)) ∧
  (MeasurableSet[completedSpace_value (volume : Measure ℝ)] A →
    completedMeasure_value (volume : Measure ℝ) A =
      lebesgue_value 1 ((fun x : Point 1 => x 0) ⁻¹' A))

/-- A strict subgraph, including an infinite upper endpoint. -/
abbrev strictSubgraph {X : Type u} (f : X → ℝ≥0∞) : Set (X × ℝ) :=
  {p | 0 < p.2 ∧ ENNReal.ofReal p.2 < f p.1}

abbrev euclideanSection (m n : ℕ) (E : Set (Point (m+n))) (x : Point m) :
    Set (Point n) := {y | (coordinates m n).symm (x,y) ∈ E}

/-- The source's prescribed zero at every non-Lebesgue-measurable section. -/
def sectionMass (m n : ℕ) [NeZero m] [NeZero n]
    (E : Set (Point (m+n))) (x : Point m) : ℝ≥0∞ := by
  classical
  exact if MeasurableSet[lebesgueSpace_value n] (euclideanSection m n E x) then
    lebesgue_value n (euclideanSection m n E x) else 0

def borel_subgraph : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X), SigmaFinite μ →
    ∀ (f : X → ℝ≥0∞), Measurable f →
      MeasurableSet (strictSubgraph f) ∧
      (μ.prod (volume : Measure ℝ)) (strictSubgraph f) = nonnegativeIntegral_value μ f

/-- An ordinary product with a completed real factor, rather than the
completion of the product. The first factor retains its original domain. -/
def completed_factor_subgraph : Prop :=
  ∀ {X : Type u} [m : MeasurableSpace X] (μ : Measure X), SigmaFinite μ →
    ∀ (f : X → ℝ≥0∞), Measurable f →
      MeasurableSet[m.prod (completedSpace_value (volume : Measure ℝ))] (strictSubgraph f) ∧
      (@Measure.prod X ℝ m (completedSpace_value (volume : Measure ℝ)) μ
        (completedMeasure_value (volume : Measure ℝ))) (strictSubgraph f) =
          nonnegativeIntegral_value μ f

/-- Sections are measurable almost everywhere, the exact zero-extended mass
map is Lebesgue measurable, and its nonnegative integral is the joint mass. -/
def cavalieri : Prop :=
  ∀ (m n : ℕ) [NeZero m] [NeZero n] (E : Set (Point (m+n))),
    MeasurableSet[lebesgueSpace_value (m+n)] E →
      (∀ᵐ x ∂(lebesgue_value m),
        MeasurableSet[lebesgueSpace_value n] (euclideanSection m n E x)) ∧
      Measurable[lebesgueSpace_value m] (sectionMass m n E) ∧
      lebesgue_value (m+n) E =
        @nonnegativeIntegral_value (Point m) (lebesgueSpace_value m)
          (lebesgue_value m) (sectionMass m n E)

end Specs.D11.Ch08.SubgraphCavalieri
