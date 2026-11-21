import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Independent specification of paper.tex:675–710, Theorem 2.7.
All variables are real and measurable for the specified sigma algebra; the
probability space need not be complete. Probability convergence and uniform
integrability are exactly the chapter-1 strict-tail interfaces. Real powers
and `MemLp` at `ofReal p` retain the full range `0 < p < 1` as well as `p ≥ 1`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

universe u

namespace Specs.ProbabilityFoundations.Ch02.ConvergenceComparisons
open Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces

/-- Almost sure convergence implies convergence in probability. -/
def almostSureImpliesProbabilityType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ),
    (∀ n, Measurable (Xn n)) → Measurable X →
    (∀ᵐ ω ∂P, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) →
    ConvergesInProbabilityValue P Xn X

/-- The source's moment formulation of Lp convergence, for every finite real p > 0. -/
def lpImpliesProbabilityType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (p : ℝ),
    (∀ n, Measurable (Xn n)) → Measurable X → 0 < p →
    (∀ n, MemLp (Xn n) (ENNReal.ofReal p) P) → MemLp X (ENNReal.ofReal p) P →
    Tendsto (fun n => ∫ ω, |Xn n ω - X ω| ^ p ∂P) atTop (𝓝 0) →
    ConvergesInProbabilityValue P Xn X

/-- Subsequences and further subsequences are strictly increasing maps N → N. -/
def probabilityIffSubsequencesType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ),
    (∀ n, Measurable (Xn n)) → Measurable X →
    (ConvergesInProbabilityValue P Xn X ↔
      ∀ s : ℕ → ℕ, StrictMono s → ∃ t : ℕ → ℕ, StrictMono t ∧
        ∀ᵐ ω ∂P, Tendsto (fun k => Xn (s (t k)) ω) atTop (𝓝 (X ω)))

/-- Two limits in probability of the same sequence agree almost surely. -/
def probabilityLimitUniqueType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → ℝ) (X Y : Ω → ℝ),
    (∀ n, Measurable (Xn n)) → Measurable X → Measurable Y →
    ConvergesInProbabilityValue P Xn X → ConvergesInProbabilityValue P Xn Y →
    X =ᵐ[P] Y

/-- The p = 1 implication includes integrability of the limit as a conclusion. -/
def probabilityUiImpliesL1Type : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ),
    (∀ n, Measurable (Xn n)) → Measurable X →
    ConvergesInProbabilityValue P Xn X → SourceUniformIntegrableValue P (Set.range Xn) →
    Integrable X P ∧ Tendsto (fun n => ∫ ω, |Xn n ω - X ω| ∂P) atTop (𝓝 0)

end Specs.ProbabilityFoundations.Ch02.ConvergenceComparisons
