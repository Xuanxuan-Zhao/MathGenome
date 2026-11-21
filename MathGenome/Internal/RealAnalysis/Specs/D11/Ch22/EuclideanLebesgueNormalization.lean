import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.EuclideanUnitCubeBounds
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.VolumeUniqueness

/-! Independent statements for paper.tex:6103–6109.

`Point n` carries its l2 Euclidean metric. The Hausdorff outer measure is
the shared coefficient-one construction; the Lebesgue measure is the earlier
Borel restriction. Positive natural dimensions are expressed by `NeZero n`.
The Borel measure used in the proof is explicitly identified with that outer
measure, before its invariance, nonvanishing and bounded-set finiteness are used.
-/

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace Specs.D11.Ch22.EuclideanLebesgueNormalization

open _root_.D11.Ch03

def borelMeasurePropertiesStatement : Prop :=
  ∀ (n : ℕ) [NeZero n],
    let μ : Measure (Point n) := Measure.hausdorffMeasure (n : ℝ)
    (∀ E : Set (Point n), MeasurableSet E →
      μ E = HausdorffOuterMeasure.outerMeasureValue (n : ℝ≥0) E) ∧
    μ ≠ 0 ∧
    (∀ (a : Point n) (E : Set (Point n)), MeasurableSet E →
      μ ((fun x => a + x) '' E) = μ E) ∧
    (∀ E : Set (Point n), MeasurableSet E → Bornology.IsBounded E → μ E < ∞)

def normalizationStatement : Prop :=
  ∀ (n : ℕ) [NeZero n], ∃ c : ℝ,
    0 < c ∧ (n = 1 → c = 1) ∧
    ∀ E : Set (Point n), MeasurableSet E →
      Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value n E =
        ENNReal.ofReal c * HausdorffOuterMeasure.outerMeasureValue (n : ℝ≥0) E

end Specs.D11.Ch22.EuclideanLebesgueNormalization
