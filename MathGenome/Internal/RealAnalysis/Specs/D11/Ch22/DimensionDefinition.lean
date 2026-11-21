import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure

/-!
Independent specification for paper.tex:6085–6090,
`D11.22.dimension_definition`.

Dimension takes values in `[0,∞]`. The infimum ranges over finite nonnegative
exponents and is taken in `ℝ≥0∞`, so no zero exponent means infimum infinity.
The empty set is assigned dimension zero explicitly. The mass in every
statement is the shared coefficient-one diameter-cover outer measure, evaluated
on arbitrary subsets of a genuine metric space. No measurability or finiteness
assumption is imposed, and neither threshold statement includes the critical
exponent itself.
-/

noncomputable section

open Set
open scoped NNReal ENNReal

universe u

namespace Specs.D11.Ch22.DimensionDefinition

def dimensionType : Type (u + 1) :=
  {X : Type u} → [MetricSpace X] → Set X → ℝ≥0∞

/-- The prescribed infimum, including both endpoint conventions. -/
def dimensionValue : dimensionType := by
  classical
  exact fun {X} _ E => if E = ∅ then 0 else
    ⨅ (s : ℝ≥0) (_ : HausdorffOuterMeasure.outerMeasureValue s E = 0), (s : ℝ≥0∞)

def emptyStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X], dimensionValue (∅ : Set X) = 0

/-- The infimum formula also holds for the empty set, because all its masses
vanish and zero is one of the allowed exponents. -/
def infimumStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X),
    dimensionValue E =
      ⨅ (s : ℝ≥0) (_ : HausdorffOuterMeasure.outerMeasureValue s E = 0), (s : ℝ≥0∞)

def leOfZeroStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0) (E : Set X),
    HausdorffOuterMeasure.outerMeasureValue s E = 0 → dimensionValue E ≤ s

/-- In particular, an empty class of zero exponents has infimum infinity. -/
def infiniteIffStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X),
    dimensionValue E = ∞ ↔
      ∀ s : ℝ≥0, HausdorffOuterMeasure.outerMeasureValue s E ≠ 0

def aboveStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (t : ℝ≥0) (E : Set X),
    dimensionValue E < t → HausdorffOuterMeasure.outerMeasureValue t E = 0

def belowStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ≥0) (E : Set X),
    (s : ℝ≥0∞) < dimensionValue E →
      HausdorffOuterMeasure.outerMeasureValue s E = ∞

def infiniteMassesStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X),
    dimensionValue E = ∞ →
      ∀ s : ℝ≥0, HausdorffOuterMeasure.outerMeasureValue s E = ∞

def zeroEndpointStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X),
    dimensionValue E = 0 → ¬ ∃ s : ℝ≥0, (s : ℝ≥0∞) < dimensionValue E

end Specs.D11.Ch22.DimensionDefinition
