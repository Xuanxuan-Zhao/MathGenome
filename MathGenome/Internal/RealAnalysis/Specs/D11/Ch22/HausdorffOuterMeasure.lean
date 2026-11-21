import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffScaleContent
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.MetricOuterBorel

/-!
Independent specification of paper.tex:6020–6032. The finite positive scales
use the previously fixed coefficient-one diameter-cover costs. No measurable
structure, separability, nonemptiness, or mass bound is imposed on the metric
space. The Borel restriction and the full Carathéodory restriction have their
distinct, explicitly specified measurable spaces.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ENNReal

universe u

namespace Specs.D11.Ch22.HausdorffOuterMeasure

def outerMeasureType : Type (u + 1) :=
  {X : Type u} → [MetricSpace X] → ℝ≥0 → OuterMeasure X

/-- Supremum of the scale outer measures at all finite positive scales.
The exact bridge to the fixed covering infimum is specified by `applyStatement`.
`pre` removes empty slots, but retains nonempty singleton costs at exponent zero. -/
def outerMeasureValue : outerMeasureType :=
  fun {X} _ s => ⨆ (δ : ℝ≥0) (_ : 0 < δ),
    OuterMeasure.mkMetric'.pre (fun U : Set X => ediam U ^ (s : ℝ)) (δ : ℝ≥0∞)

def scaleAntitoneStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0) (E : Set X),
    Antitone (fun δ : ℝ≥0 => Specs.D11.Ch22.hausdorffScaleContentValue s δ E)

def applyStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0) (E : Set X),
    outerMeasureValue s E =
      ⨆ (δ : ℝ≥0) (_ : 0 < δ), Specs.D11.Ch22.hausdorffScaleContentValue s δ E

def nativeBridgeStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0),
    outerMeasureValue (X := X) s =
      OuterMeasure.mkMetric' (fun U : Set X => ediam U ^ (s : ℝ))

def axiomsStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0),
    outerMeasureValue s (∅ : Set X) = 0 ∧
    Monotone (fun E : Set X => outerMeasureValue s E) ∧
    ∀ E : ℕ → Set X, outerMeasureValue s (⋃ n, E n) ≤
      ∑' n, outerMeasureValue s (E n)

def metricStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0), (outerMeasureValue (X := X) s).IsMetric

def separatedStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0) (A B : Set X),
    (∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) →
    outerMeasureValue s (A ∪ B) = outerMeasureValue s A + outerMeasureValue s B

def borelStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0),
    borel X ≤ (outerMeasureValue s).caratheodory

/-- Agreement on Borel sets and on the full splitting domain, with completeness
on precisely the latter. No identification with Borel completion is asserted. -/
def restrictionsStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0),
    (∀ B : Set X, MeasurableSet[borel X] B →
      ∀ E : Set X, outerMeasureValue s E =
        outerMeasureValue s (E ∩ B) + outerMeasureValue s (E \ B)) ∧
    (∃ μ : @Measure X (borel X),
      ∀ B : Set X, MeasurableSet[borel X] B → μ B = outerMeasureValue s B) ∧
    (∀ C : Set X,
      (∀ E : Set X, outerMeasureValue s E =
        outerMeasureValue s (E ∩ C) + outerMeasureValue s (E \ C)) →
      Specs.D11.Ch02.Caratheodory.measure_value (outerMeasureValue s) C =
        outerMeasureValue s C) ∧
    @Measure.IsComplete X
      (Specs.D11.Ch02.Caratheodory.measurableSpace_value (outerMeasureValue s))
      (Specs.D11.Ch02.Caratheodory.measure_value (outerMeasureValue s))

end Specs.D11.Ch22.HausdorffOuterMeasure
