import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Independent statements for the two examples in paper.tex:4997–5008.
`Interval` carries the induced Borel structure, not the Lebesgue completion.
Its Lebesgue measure is the pullback of real Borel volume along the inclusion.
The singleton space is `Fin 1`, with its full sigma-algebra. Densities take
values in [0,∞], so the nonexistence includes infinite-valued densities.
The last statement uses exactly the shared measurable sigma-finite-set
predicate, and expresses carrying the target by a null complement. -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section

namespace D11.Ch15.RNNonSigmaFiniteFailure

abbrev Interval := Set.Icc (0 : ℝ) 1
abbrev Point := Fin 1

end D11.Ch15.RNNonSigmaFiniteFailure

namespace Specs.D11.Ch15.RNNonSigmaFiniteFailure

open _root_.D11.Ch15.RNNonSigmaFiniteFailure

abbrev intervalCounting_type := Measure Interval
def intervalCounting_value : intervalCounting_type := Measure.count

abbrev intervalLebesgue_type := Measure Interval
def intervalLebesgue_value : intervalLebesgue_type :=
  Measure.comap Subtype.val (volume : Measure ℝ)

abbrev pointReference_type := Measure Point
def pointReference_value : pointReference_type :=
  (∞ : ℝ≥0∞) • Measure.dirac (0 : Point)

abbrev pointTarget_type := Measure Point
def pointTarget_value : pointTarget_type := Measure.dirac (0 : Point)

def interval_borel : Prop :=
  (inferInstance : MeasurableSpace Interval) = borel Interval

def interval_counting_null : Prop :=
  ∀ E : Set Interval, intervalCounting_value E = 0 ↔ E = ∅

def interval_lebesgue_values : Prop :=
  intervalLebesgue_value univ = 1 ∧
    ∀ x : Interval, intervalLebesgue_value {x} = 0

def interval_absolute_continuity : Prop :=
  intervalLebesgue_value ≪ intervalCounting_value

def interval_no_density : Prop :=
  ¬ ∃ h : Interval → ℝ≥0∞, Measurable h ∧
    ∀ E : Set Interval, MeasurableSet E →
      intervalLebesgue_value E = ∫⁻ x in E, h x ∂intervalCounting_value

def interval_not_sigmaFinite : Prop := ¬ SigmaFinite intervalCounting_value

def point_values : Prop :=
  pointReference_value {(0 : Point)} = ∞ ∧
  pointReference_value univ = ∞ ∧
  pointTarget_value {(0 : Point)} = 1 ∧ pointTarget_value univ = 1

def point_absolute_continuity : Prop := pointTarget_value ≪ pointReference_value

def point_integral : Prop :=
  ∀ h : Point → ℝ≥0∞, (∫⁻ x, h x ∂pointReference_value) =
    if h 0 = 0 then 0 else ∞

def point_no_density : Prop :=
  ¬ ∃ h : Point → ℝ≥0∞, Measurable h ∧
    ∀ E : Set Point, MeasurableSet E →
      pointTarget_value E = ∫⁻ x in E, h x ∂pointReference_value

def point_no_sigmaFinite_carrier : Prop :=
  ¬ ∃ S : Set Point,
    Ch01.MeasureDefinitions.isSigmaFiniteSet_value pointReference_value S ∧
    pointTarget_value Sᶜ = 0

end Specs.D11.Ch15.RNNonSigmaFiniteFailure
