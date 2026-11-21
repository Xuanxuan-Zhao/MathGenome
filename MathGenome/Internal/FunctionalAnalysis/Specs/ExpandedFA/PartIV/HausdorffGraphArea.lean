import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Hausdorff

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.HausdorffGraphArea

/-- The Euclidean parameter space, including the zero-dimensional space. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ordinary graph, with the height in the last coordinate. -/
def graphMap {n : ℕ} (g : E n → ℝ) (x : E n) : E (n + 1) :=
  WithLp.toLp 2 (Fin.lastCases (g x) (fun i => x i))

/-- The Euclidean coordinate unit vector. -/
def coordinateVector {n : ℕ} (i : Fin n) : E n := EuclideanSpace.single i 1

/-- The scalar graph area factor, using the ambient Fréchet derivative. -/
def graphJacobian {n : ℕ} (g : E n → ℝ) (x : E n) : ℝ :=
  Real.sqrt (1 + ∑ i : Fin n, (fderiv ℝ g x (coordinateVector i)) ^ 2)

namespace Specs

/-- Borel images of arbitrary measurable subsets of the open parameter domain. -/
def MeasurableGraphImage : Prop :=
  ∀ (n : ℕ) (U : Set (E n)) (g : E n → ℝ), IsOpen U → ContDiffOn ℝ 1 g U →
    ∀ (s : Set (E n)), MeasurableSet s → s ⊆ U → MeasurableSet (graphMap g '' s)

/-- The full nonnegative integral formula for raw Hausdorff measure on both spaces. -/
def WeightedGraphArea : Prop :=
  ∀ (n : ℕ) (U : Set (E n)) (g : E n → ℝ), IsOpen U → ContDiffOn ℝ 1 g U →
    ∀ (s : Set (E n)), MeasurableSet s → s ⊆ U →
      ∀ (h : E (n + 1) → ℝ≥0∞), Measurable h →
        (∫⁻ y in graphMap g '' s, h y ∂(Measure.hausdorffMeasure (n : ℝ))) =
          ∫⁻ x in s, ENNReal.ofReal (graphJacobian g x) * h (graphMap g x)
            ∂(Measure.hausdorffMeasure (n : ℝ))

end Specs
end ExpandedFA.HausdorffGraphArea
