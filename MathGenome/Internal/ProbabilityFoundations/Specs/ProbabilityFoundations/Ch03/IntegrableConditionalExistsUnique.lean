import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-!
The integrable part of Theorem 3.2 and its test-integral comparison
(paper.tex, 819–845). Both sigma algebras are arbitrary and may be incomplete.
The extended nonnegative existence and the real/ENNReal bridge are allocated
separately; the nonnegative representative here has codomain ℝ and is therefore
finite at every point.
-/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch03.IntegrableConditionalExistsUnique

universe u

open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

def existsRealVersionType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Measurable[F] X → Integrable X P →
      ∃ U : Ω → ℝ, realVersionValue G P X U

def realVersionUniqueType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X U V : Ω → ℝ), Integrable X P →
      realVersionValue G P X U → realVersionValue G P X V → U =ᵐ[P] V

def existsNonnegativeRealVersionType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Measurable[F] X → Integrable X P → (∀ ω, 0 ≤ X ω) →
      ∃ U : Ω → ℝ, realVersionValue G P X U ∧ ∀ ω, 0 ≤ U ω

def testIntegralComparisonType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (U V : Ω → ℝ), Measurable[G] U → Measurable[G] V →
      Integrable U P → Integrable V P →
      (∀ A, MeasurableSet[G] A → (∫ ω in A, U ω ∂P) ≤ ∫ ω in A, V ω ∂P) →
      U ≤ᵐ[P] V

end Specs.ProbabilityFoundations.Ch03.IntegrableConditionalExistsUnique
