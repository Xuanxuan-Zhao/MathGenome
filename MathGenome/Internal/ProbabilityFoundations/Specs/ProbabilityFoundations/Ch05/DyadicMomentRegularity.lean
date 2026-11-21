import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent interfaces for the adjacent-increment stage of
Kolmogorov--Chentsov, paper.tex:1343–1363.

The process is represented on the real line, with hypotheses only on `[0,T]`.
A finite nonnegative constant is represented by `ℝ≥0`; the source moment
inequality at the distinct endpoints forces any admissible real constant to be
nonnegative. No completeness of either the probability space or state space is
required for this stage. -/
open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityFoundations.Ch05

/-- The dyadic mesh `T 2⁻ⁿ`. -/
noncomputable def dyadicStep (T : ℝ) (n : ℕ) : ℝ := T / (2 : ℝ) ^ n

/-- A level is bad if at least one of its `2^n` adjacent increments is too large.
The index `j : Fin (2^n)` corresponds to the source index `j+1`. -/
def dyadicBadEvent {Ω S : Type*} [MetricSpace S]
    (X : ℝ → Ω → S) (T γ : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ j : Fin (2 ^ n), (dyadicStep T n) ^ γ <
    dist (X ((j.val + 1 : ℕ) * dyadicStep T n) ω)
      (X ((j.val : ℝ) * dyadicStep T n) ω)}

/-- All adjacent dyadic increments obey the specified power bound. -/
def DyadicBound {Ω S : Type*} [MetricSpace S]
    (X : ℝ → Ω → S) (T γ : ℝ) (ω : Ω) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (j : Fin (2 ^ n)),
    dist (X ((j.val + 1 : ℕ) * dyadicStep T n) ω)
      (X ((j.val : ℝ) * dyadicStep T n) ω) ≤ A * (dyadicStep T n) ^ γ

/-- The original moment condition, including potentially infinite left sides. -/
def IncrementMomentCondition {Ω S : Type*} [MeasurableSpace Ω] [MetricSpace S]
    (P : Measure Ω) (X : ℝ → Ω → S) (T p β : ℝ) (C : ℝ≥0) : Prop :=
  ∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T,
    (∫⁻ ω, ENNReal.ofReal (dist (X t ω) (X s ω) ^ p) ∂P) ≤
      ENNReal.ofReal ((C : ℝ) * |t - s| ^ (1 + β))

end ProbabilityFoundations.Ch05

namespace Specs.ProbabilityFoundations.Ch05.DyadicMomentRegularity
open _root_.ProbabilityFoundations.Ch05
universe u v

def dyadicProbabilityBoundType : Prop :=
  ∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → Ω → S)
    (T p β : ℝ) (C : ℝ≥0), 0 < T → 0 < p → 0 < β →
    (∀ t ∈ Set.Icc 0 T, Measurable (X t)) →
    IncrementMomentCondition P X T p β C →
    ∀ γ : ℝ, 0 < γ → γ < β / p → ∀ n : ℕ,
    P (dyadicBadEvent X T γ n) ≤
      ENNReal.ofReal ((C : ℝ) * T ^ (1 + β - p * γ) *
        (2 : ℝ) ^ (-(n : ℝ) * (β - p * γ)))

def dyadicSummableType : Prop :=
  ∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → Ω → S)
    (T p β : ℝ) (C : ℝ≥0), 0 < T → 0 < p → 0 < β →
    (∀ t ∈ Set.Icc 0 T, Measurable (X t)) →
    IncrementMomentCondition P X T p β C →
    ∀ γ : ℝ, 0 < γ → γ < β / p →
      (∑' n, P (dyadicBadEvent X T γ n)) < ∞

def commonDyadicEventType : Prop :=
  ∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → Ω → S)
    (T p β : ℝ) (C : ℝ≥0), 0 < T → 0 < p → 0 < β →
    (∀ t ∈ Set.Icc 0 T, Measurable (X t)) →
    IncrementMomentCondition P X T p β C →
    ∃ G : Set Ω, MeasurableSet G ∧ P G = 1 ∧
      ∀ ω ∈ G, ∀ γ : ℝ, 0 < γ → γ < β / p → DyadicBound X T γ ω

end Specs.ProbabilityFoundations.Ch05.DyadicMomentRegularity
