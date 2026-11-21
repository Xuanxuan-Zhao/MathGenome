import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-! The nonnegative part of Theorem 3.4 (paper.tex, taking out a measurable
factor). Both factors take values in ℝ≥0∞, whose multiplication has 0 * ∞ = 0.
No boundedness, integrability, or completeness is assumed. -/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch03.NonnegativeConditionalPullout

universe u

open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-- The product with the conditional expectation satisfies every event test. -/
def productIsVersionType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H X : Ω → ℝ≥0∞), Measurable[G] H → Measurable[F] X →
      nonnegativeVersionValue (F := F) G P (fun ω => H ω * X ω)
        (fun ω => H ω * nonnegativeConditionalExpectationValue (F := F) G P X ω)

/-- Taking out an arbitrary extended nonnegative measurable factor. -/
def pulloutType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H X : Ω → ℝ≥0∞), Measurable[G] H → Measurable[F] X →
      nonnegativeConditionalExpectationValue (F := F) G P (fun ω => H ω * X ω) =ᵐ[P]
        (fun ω => H ω * nonnegativeConditionalExpectationValue (F := F) G P X ω)

end Specs.ProbabilityFoundations.Ch03.NonnegativeConditionalPullout
