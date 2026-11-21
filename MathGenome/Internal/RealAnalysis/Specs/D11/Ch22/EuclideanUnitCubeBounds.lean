import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.OuterVolume

/-! Independent statements for the quantitative part of
`paper.tex:6103–6105`. `Point n` has its genuine Euclidean (l2) metric.
The cube uses the shared closed-box definition. The outer measure is the
shared coefficient-one diameter-cover construction, evaluated on subsets.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ENNReal

namespace Specs.D11.Ch22.EuclideanUnitCubeBounds

open _root_.D11.Ch03

/- The cover sets are arbitrary; no measurability or boundedness is assumed.
At positive integer exponent empty slots have zero cost. -/
def arbitraryCoverStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (U : ℕ → Set (Point n)),
    closedBox (0 : Fin n → ℝ) 1 ⊆ ⋃ j, U j →
    1 ≤ ∑' j, ediam (U j) ^ (n : ℝ)

def boundsStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    1 ≤ HausdorffOuterMeasure.outerMeasureValue (n : ℝ≥0)
      (closedBox (0 : Fin n → ℝ) 1) ∧
    HausdorffOuterMeasure.outerMeasureValue (n : ℝ≥0)
      (closedBox (0 : Fin n → ℝ) 1) ≤
      ENNReal.ofReal ((n : ℝ) ^ ((n : ℝ) / 2))

def oneDimensionalStatement : Prop :=
  HausdorffOuterMeasure.outerMeasureValue (1 : ℝ≥0)
    (closedBox (0 : Fin 1 → ℝ) 1) = 1

end Specs.D11.Ch22.EuclideanUnitCubeBounds
