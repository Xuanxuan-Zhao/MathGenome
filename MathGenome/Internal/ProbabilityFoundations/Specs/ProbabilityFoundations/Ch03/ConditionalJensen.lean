import Mathlib.Analysis.Convex.Function
import Mathlib.Data.EReal.Operations
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-! The full extended conditional Jensen assertion, paper.tex 939–984.
The positive conditional integral may be infinite. The negative one is
finite almost surely under the convexity and integrability hypotheses.
No completeness assumption is made on either sigma-algebra. -/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch03.ConditionalJensen

universe u

def extendedConditionalExpectationType :=
  ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → (Ω → ℝ) → (Ω → EReal)

noncomputable def extendedConditionalExpectationValue : extendedConditionalExpectationType :=
  fun {_Ω} G _F P Y ω =>
    (condLExp G P (fun ω => ENNReal.ofReal (Y ω)) ω : EReal) -
      (condLExp G P (fun ω => ENNReal.ofReal (-Y ω)) ω : EReal)

def convexContinuousType : Prop :=
  ∀ (φ : ℝ → ℝ), ConvexOn ℝ Set.univ φ → Continuous φ ∧ Measurable φ

def negativePartIntegrableType : Prop :=
  ∀ {Ω : Type u} [F : MeasurableSpace Ω] (P : Measure[F] Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (φ : ℝ → ℝ),
    Integrable X P → ConvexOn ℝ Set.univ φ →
      Integrable (fun ω => max (-(φ (X ω))) 0) P

def negativeConditionalFiniteType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ) (φ : ℝ → ℝ), Integrable X P → ConvexOn ℝ Set.univ φ →
      ∀ᵐ ω ∂P, condLExp G P (fun ω => ENNReal.ofReal (-(φ (X ω)))) ω < ∞

def conditionalJensenType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ) (φ : ℝ → ℝ), Integrable X P → ConvexOn ℝ Set.univ φ →
      ∀ᵐ ω ∂P, (φ (condExp G P X ω) : EReal) ≤
        extendedConditionalExpectationValue G P (fun ω => φ (X ω)) ω

def integrableAgreementType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (Y : Ω → ℝ), Integrable Y P →
      extendedConditionalExpectationValue G P Y =ᵐ[P]
        (fun ω => ((condExp G P Y ω : ℝ) : EReal))

end Specs.ProbabilityFoundations.Ch03.ConditionalJensen
