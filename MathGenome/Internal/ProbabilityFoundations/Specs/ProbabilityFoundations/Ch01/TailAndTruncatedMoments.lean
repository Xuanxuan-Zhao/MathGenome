import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityObjects

/-! Independent full propositions for paper.tex, Theorem `thm:prob-tail`.
The variable may take the value infinity. All integrals are extended
nonnegative integrals. Real thresholds are embedded by `ENNReal.ofReal`.
The intervals exclude zero, which is a Lebesgue null endpoint. -/
open MeasureTheory Set
open scoped ENNReal
namespace Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments
universe u

def fullMomentType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ p : ℝ, 0 < p →
    (∫⁻ ω, Y ω ^ p ∂P) = ENNReal.ofReal p *
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t < Y ω}

def lowerMomentType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ p a : ℝ, 0 < p → 0 < a →
    (∫⁻ ω in {ω | Y ω ≤ ENNReal.ofReal a}, Y ω ^ p ∂P) =
      ENNReal.ofReal p * (∫⁻ t : ℝ in Ioo 0 a,
        ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t < Y ω}) -
      ENNReal.ofReal a ^ p * P {ω | ENNReal.ofReal a < Y ω}

def upperMomentType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ p a : ℝ, 0 < p → 0 < a →
    (∫⁻ ω in {ω | ENNReal.ofReal a < Y ω}, Y ω ^ p ∂P) =
      ENNReal.ofReal a ^ p * P {ω | ENNReal.ofReal a < Y ω} +
      ENNReal.ofReal p * (∫⁻ t : ℝ in Ioi a,
        ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t < Y ω})

/-- Both terms of the subtraction in the bounded lower formula are finite,
as is the lower moment itself. -/
def boundedTermsType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ p a : ℝ, 0 < p → 0 < a →
    (∫⁻ ω in {ω | Y ω ≤ ENNReal.ofReal a}, Y ω ^ p ∂P) < ∞ ∧
    ENNReal.ofReal p * (∫⁻ t : ℝ in Ioo 0 a,
      ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t < Y ω}) < ∞ ∧
    ENNReal.ofReal a ^ p * P {ω | ENNReal.ofReal a < Y ω} < ∞

/-- A single statement for any measurable positive integration region covers
all three integrals in the source. -/
def tailConventionType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ (p : ℝ), 0 < p →
    ∀ s : Set ℝ, MeasurableSet s → s ⊆ Ioi 0 →
    (∫⁻ t : ℝ in s, ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t < Y ω}) =
    ∫⁻ t : ℝ in s, ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t ≤ Y ω}

/-- Additive endpoint corrections remain meaningful for infinite upper moments. -/
def lowerEndpointType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ p a : ℝ, 0 < p → 0 < a →
    (∫⁻ ω in {ω | Y ω ≤ ENNReal.ofReal a}, Y ω ^ p ∂P) =
      (∫⁻ ω in {ω | Y ω < ENNReal.ofReal a}, Y ω ^ p ∂P) +
      ENNReal.ofReal a ^ p * P {ω | Y ω = ENNReal.ofReal a}

def upperEndpointType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ p a : ℝ, 0 < p → 0 < a →
    (∫⁻ ω in {ω | ENNReal.ofReal a ≤ Y ω}, Y ω ^ p ∂P) =
      (∫⁻ ω in {ω | ENNReal.ofReal a < Y ω}, Y ω ^ p ∂P) +
      ENNReal.ofReal a ^ p * P {ω | Y ω = ENNReal.ofReal a}
/-- Removing the atom gives the reverse change of lower endpoint convention. -/
def lowerEndpointSubType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ p a : ℝ, 0 < p → 0 < a →
    (∫⁻ ω in {ω | Y ω < ENNReal.ofReal a}, Y ω ^ p ∂P) =
      (∫⁻ ω in {ω | Y ω ≤ ENNReal.ofReal a}, Y ω ^ p ∂P) -
      ENNReal.ofReal a ^ p * P {ω | Y ω = ENNReal.ofReal a}

/-- The reverse upper correction also permits infinite upper moments, since
the subtracted atom term is finite. -/
def upperEndpointSubType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ p a : ℝ, 0 < p → 0 < a →
    (∫⁻ ω in {ω | ENNReal.ofReal a < Y ω}, Y ω ^ p ∂P) =
      (∫⁻ ω in {ω | ENNReal.ofReal a ≤ Y ω}, Y ω ^ p ∂P) -
      ENNReal.ofReal a ^ p * P {ω | Y ω = ENNReal.ofReal a}

end Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments
