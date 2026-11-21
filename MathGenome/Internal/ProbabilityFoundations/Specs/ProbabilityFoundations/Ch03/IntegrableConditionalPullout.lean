import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-! The real integrable part of Theorem 3.4 in paper.tex. The probability
space and its sub-sigma-algebra need not be complete. The general factor
is measurable, with no boundedness or integrability assumption on it. -/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch03.IntegrableConditionalPullout

universe u

open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-- The pulled-out real product is integrable and gives the conditional
expectation of the original product. -/
def pulloutType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H X : Ω → ℝ), Measurable[G] H → Integrable X P →
      Integrable (fun ω => H ω * X ω) P →
      Integrable (fun ω => H ω * realConditionalExpectationValue (F := F) G P X ω) P ∧
      realConditionalExpectationValue (F := F) G P (fun ω => H ω * X ω) =ᵐ[P]
        (fun ω => H ω * realConditionalExpectationValue (F := F) G P X ω)

/-- A common almost-sure bound on the factor suffices to make both products
integrable. In particular this applies to every pointwise bounded factor. -/
def boundedPulloutType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H X : Ω → ℝ), Measurable[G] H → Integrable X P →
    ∀ (C : ℝ), (∀ᵐ ω ∂P, |H ω| ≤ C) →
      Integrable (fun ω => H ω * X ω) P ∧
      Integrable (fun ω => H ω * realConditionalExpectationValue (F := F) G P X ω) P ∧
      realConditionalExpectationValue (F := F) G P (fun ω => H ω * X ω) =ᵐ[P]
        (fun ω => H ω * realConditionalExpectationValue (F := F) G P X ω)

end Specs.ProbabilityFoundations.Ch03.IntegrableConditionalPullout
