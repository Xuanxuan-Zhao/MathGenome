import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityBounds

/-! Independent statements of paper.tex, Proposition `thm:prob-cond-variance`
(lines 1043–1061). The probability space and sub-sigma-algebra are arbitrary.
`MemLp X 2 P` includes almost-everywhere measurability and finite second moment;
there is no nondegeneracy or completeness assumption. -/

open MeasureTheory
open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
open Specs.ProbabilityFoundations.Ch01.ProbabilityBounds

namespace Specs.ProbabilityFoundations.Ch03.ConditionalAndTotalVariance
universe u

def varianceIntegrabilityType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), MemLp X 2 P →
      let M := realConditionalExpectationValue G P X
      let V := realConditionalExpectationValue G P (fun ω => (X ω - M ω) ^ 2)
      MemLp M 2 P ∧ Integrable X P ∧ Integrable M P ∧
        Integrable (fun ω => X ω ^ 2) P ∧
        Integrable (fun ω => M ω ^ 2) P ∧
        Integrable (fun ω => M ω * X ω) P ∧
        Integrable (fun ω => (X ω - M ω) ^ 2) P ∧ Integrable V P ∧
        Integrable (fun ω => (X ω - ∫ t, X t ∂P) ^ 2) P ∧
        Integrable (fun ω => (M ω - ∫ t, M t ∂P) ^ 2) P

def conditionalVarianceType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), MemLp X 2 P →
      let M := realConditionalExpectationValue G P X
      realConditionalExpectationValue G P (fun ω => (X ω - M ω) ^ 2) =ᵐ[P]
        (fun ω => realConditionalExpectationValue G P (fun t => X t ^ 2) ω - M ω ^ 2)

def totalVarianceType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), MemLp X 2 P →
      let M := realConditionalExpectationValue G P X
      let V := realConditionalExpectationValue G P (fun ω => (X ω - M ω) ^ 2)
      realVarianceValue P X = (∫ ω, V ω ∂P) + realVarianceValue P M

end Specs.ProbabilityFoundations.Ch03.ConditionalAndTotalVariance
