import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure

/-!
Independent statements for paper.tex:6077–6085, D11.22.exponent_threshold.

The shared coefficient-one diameter-cover outer measure is evaluated on every
subset of a genuine metric space. Exponents are nonnegative, including zero;
no measurable structure or nonemptiness assumption is required.
-/

open Set
open scoped NNReal ENNReal

universe u

namespace Specs.D11.Ch22.ExponentThreshold

/-- Finite lower-exponent outer mass forces zero higher-exponent outer mass. -/
def finiteLowerStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s t : ℝ≥0) (E : Set X), s < t →
    HausdorffOuterMeasure.outerMeasureValue s E < ∞ →
    HausdorffOuterMeasure.outerMeasureValue t E = 0

/-- Equivalently, positive higher-exponent outer mass forces infinite
lower-exponent outer mass. The positive mass is allowed to be infinite. -/
def positiveHigherStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s t : ℝ≥0) (E : Set X), s < t →
    0 < HausdorffOuterMeasure.outerMeasureValue t E →
    HausdorffOuterMeasure.outerMeasureValue s E = ∞

end Specs.D11.Ch22.ExponentThreshold
