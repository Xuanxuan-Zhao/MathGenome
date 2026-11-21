import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-! The nonnegative case of Theorem 3.2, paper.tex 819–824 and 847–862.
The probability space and its sub-sigma-algebra need not be complete.
Extended inputs and test integrals may be infinite. -/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch03.NonnegativeConditionalExistsUnique

universe u
open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

def existsNonnegativeVersionType : Prop :=
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
        ∃ U : Ω → ℝ≥0∞, nonnegativeVersionValue G P X U

def nonnegativeVersionUniqueType : Prop :=
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (X U V : Ω → ℝ≥0∞), Measurable[F] X →
        nonnegativeVersionValue G P X U → nonnegativeVersionValue G P X V → U =ᵐ[P] V

def extendedTestIntegralComparisonType : Prop :=
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (U V : Ω → ℝ≥0∞), Measurable[G] U → Measurable[G] V →
        (∀ A, MeasurableSet[G] A →
          (∫⁻ ω in A, U ω ∂P) ≤ ∫⁻ ω in A, V ω ∂P) → U ≤ᵐ[P] V

def nonnegativeRealAgreementType : Prop :=
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (X : Ω → ℝ), Measurable[F] X → Integrable X P → (0 ≤ᵐ[P] X) →
        (∀ᵐ ω ∂P, nonnegativeConditionalExpectationValue G P
          (fun ω => ENNReal.ofReal (X ω)) ω < ∞) ∧
        nonnegativeConditionalExpectationValue G P (fun ω => ENNReal.ofReal (X ω)) =ᵐ[P]
          (fun ω => ENNReal.ofReal (realConditionalExpectationValue G P X ω))

def nonnegativeRealVersionsAgreementType : Prop :=
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (X V : Ω → ℝ) (U : Ω → ℝ≥0∞),
        Measurable[F] X → Integrable X P → (0 ≤ᵐ[P] X) →
        nonnegativeVersionValue G P (fun ω => ENNReal.ofReal (X ω)) U →
        realVersionValue G P X V →
        (∀ᵐ ω ∂P, U ω < ∞) ∧ U =ᵐ[P] (fun ω => ENNReal.ofReal (V ω))

end Specs.ProbabilityFoundations.Ch03.NonnegativeConditionalExistsUnique
