import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.PositiveStieltjes
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The positive-measure implication in paper.tex:4055–4061. The AC
hypothesis is the single global finite disjoint-open-interval modulus;
the measure is the accepted Borel Stieltjes construction. -/

namespace Specs.D11.Ch12.AcPositiveStieltjesNull

/-- Every Lebesgue-null Borel set has zero positive Stieltjes mass. -/
def null_sets : Prop :=
  ∀ (H : ℝ → ℝ) (hH : PositiveStieltjes.positiveGenerator_value H),
    absolutelyContinuousValue H →
    ∀ E : Set ℝ, MeasurableSet E → MeasureTheory.volume E = 0 →
      PositiveStieltjes.stieltjesMeasure_value H hH E = 0

/-- Absolute continuity relative to native Borel Lebesgue volume. -/
def absolutely_continuous : Prop :=
  ∀ (H : ℝ → ℝ) (hH : PositiveStieltjes.positiveGenerator_value H),
    absolutelyContinuousValue H →
      MeasureTheory.Measure.AbsolutelyContinuous
        (PositiveStieltjes.stieltjesMeasure_value H hH) MeasureTheory.volume

end Specs.D11.Ch12.AcPositiveStieltjesNull
