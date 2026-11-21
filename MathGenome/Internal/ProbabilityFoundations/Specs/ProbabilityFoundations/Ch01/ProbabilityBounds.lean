import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityObjects
import Mathlib.MeasureTheory.Function.L2Space

/-! Independent statements for paper.tex, Corollary `thm:prob-markov`.
All nonnegative expectations are extended integrals, including infinite moments.
`MemLp X 2 P` expresses finite second moment. No completeness is assumed. -/
open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch01.ProbabilityBounds
universe u

def realVarianceType :=
  ∀ {Ω : Type u} [MeasurableSpace Ω], Measure Ω → (Ω → ℝ) → ℝ
noncomputable def realVarianceValue : realVarianceType :=
  fun P X => ∫ ω, (X ω - ∫ t, X t ∂P) ^ 2 ∂P

def markovGeType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ (a : ℝ), 0 < a →
    P {ω | ENNReal.ofReal a ≤ Y ω} ≤ (∫⁻ ω, Y ω ∂P) / ENNReal.ofReal a

def momentGeType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ), Measurable X → ∀ (a p : ℝ), 0 < a → 0 < p →
    P {ω | a ≤ |X ω|} ≤
      ENNReal.ofReal (a ^ (-p)) * (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂P)

def chebyshevGeType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ), Measurable X → MemLp X 2 P → ∀ (a : ℝ), 0 < a →
    P {ω | a ≤ |X ω - ∫ t, X t ∂P|} ≤
      ENNReal.ofReal ((∫ ω, (X ω - ∫ t, X t ∂P) ^ 2 ∂P) / a ^ 2)

def exponentialMarkovGeType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ), Measurable X → ∀ (x θ : ℝ), 0 < θ →
    P {ω | x ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-θ * x)) *
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω)) ∂P)

def markovGtType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞), Measurable Y → ∀ (a : ℝ), 0 < a →
    P {ω | ENNReal.ofReal a < Y ω} ≤ (∫⁻ ω, Y ω ∂P) / ENNReal.ofReal a

def momentGtType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ), Measurable X → ∀ (a p : ℝ), 0 < a → 0 < p →
    P {ω | a < |X ω|} ≤
      ENNReal.ofReal (a ^ (-p)) * (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂P)

def chebyshevGtType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ), Measurable X → MemLp X 2 P → ∀ (a : ℝ), 0 < a →
    P {ω | a < |X ω - ∫ t, X t ∂P|} ≤
      ENNReal.ofReal ((∫ ω, (X ω - ∫ t, X t ∂P) ^ 2 ∂P) / a ^ 2)

def exponentialMarkovGtType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ), Measurable X → ∀ (x θ : ℝ), 0 < θ →
    P {ω | x < X ω} ≤ ENNReal.ofReal (Real.exp (-θ * x)) *
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω)) ∂P)

end Specs.ProbabilityFoundations.Ch01.ProbabilityBounds
