import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.Vitali
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.MeasurableMapTests
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.SimpleIntegral
import Mathlib.MeasureTheory.Measure.Comap

/-! Independent specification of paper.tex:1454–1462. The interval is the
closed unit box in canonical Euclidean one-space, with its completed Lebesgue
trace and restricted measure. Its sole coordinate identifies it with [0,1]
in ℝ. The hypothesis uses the same completed measurability test as Vitali.
Only the nonnegative simple integral of the modulus is asserted. -/

open Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section

namespace Specs.D11.Ch04.ModulusCounterexample

open _root_.D11.Ch03

def closedUnitInterval : Set (Point 1) := closedBox (fun _ => 0) (fun _ => 1)

def Interval := ↥closedUnitInterval

abbrev intervalSpace : MeasurableSpace Interval :=
  (Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1).comap (Subtype.val : Interval → Point 1)

instance : MeasurableSpace Interval := intervalSpace

def intervalMeasure : Measure Interval :=
  @Measure.comap Interval (Point 1) intervalSpace
    (Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1) Subtype.val
    (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1)

/-- Literally `2 * 𝟙_V - 1`, restricted to the unit interval. -/
def signFunction (V : Set ℝ) (x : Interval) : ℝ :=
  2 * V.indicator (fun _ => (1 : ℝ)) (x.val 0) - 1

def modulusSimple : SimpleFunc Interval ℝ≥0 := SimpleFunc.const Interval 1

/-- All assertions of the example, including the finite *simple* integral.
The exact value one makes the measure and domain normalization explicit. -/
def ModulusProperties (V : Set ℝ) : Prop :=
  (∀ x : Interval, |signFunction V x| = 1) ∧
  @Measurable Interval ℝ intervalSpace (borel ℝ) (fun x => |signFunction V x|) ∧
  (∀ x : Interval, (modulusSimple x : ℝ) = |signFunction V x|) ∧
  Specs.D11.Ch05.SimpleIntegral.simpleIntegral_value intervalMeasure modulusSimple = 1 ∧
  Specs.D11.Ch05.SimpleIntegral.simpleIntegral_value intervalMeasure modulusSimple < ∞ ∧
  {x : Interval | 0 < signFunction V x} = {x | x.val 0 ∈ V} ∧
  ¬ @Measurable Interval ℝ intervalSpace (borel ℝ) (signFunction V)

def measurable_modulus_insufficient : Prop :=
  ∀ V : Set ℝ, V ⊆ Icc 0 1 →
    ¬ MeasurableSet[Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1]
      (_root_.D11.Ch03.Vitali.inOneSpace V) → ModulusProperties V

def counterexample_exists : Prop :=
  ∃ V : Set ℝ, V ⊆ Icc 0 1 ∧
    ¬ MeasurableSet[Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1]
      (_root_.D11.Ch03.Vitali.inOneSpace V) ∧ ModulusProperties V

end Specs.D11.Ch04.ModulusCounterexample
