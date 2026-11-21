import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Exact normalization for the raw diameter-power Hausdorff measure.
The coefficient is the existing Euclidean volume of the radius-one-half ball.
This proposition includes dimension zero and assumes no geometric certificate.
-/
namespace Specs.ExpandedFA.PartIV

open MeasureTheory

/-- The full, unconditional Euclidean Hausdorff normalization obligation. -/
def EuclideanHausdorffNormalization : Prop :=
  ∀ n : ℕ,
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ)) •
      (Measure.hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) =
        (volume : Measure (EuclideanSpace ℝ (Fin n)))

end Specs.ExpandedFA.PartIV
