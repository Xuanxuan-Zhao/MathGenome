import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityObjects

/-!
Definition 3.1 of paper.tex, with the chapter's arbitrary sub-sigma-algebra
convention. The ambient measurable space is the specified F, and P is a
canonical measure. The version predicates record measurability of the chosen
representative, not merely almost-everywhere measurability. In the real case
X is used on its integrable domain; in the extended case X is used on its
measurable domain and may take the value infinity. No completeness or
countable-generation hypothesis is imposed.
-/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

universe u

def realVersionType :=
  ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → (Ω → ℝ) → (Ω → ℝ) → Prop

def realVersionValue : realVersionType :=
  fun {_Ω} G _F P X U =>
    Measurable[G] U ∧ Integrable U P ∧
      ∀ A, MeasurableSet[G] A → (∫ ω in A, U ω ∂P) = ∫ ω in A, X ω ∂P

def nonnegativeVersionType :=
  ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → (Ω → ℝ≥0∞) → (Ω → ℝ≥0∞) → Prop

def nonnegativeVersionValue : nonnegativeVersionType :=
  fun {_Ω} G _F P X U =>
    Measurable[G] U ∧
      ∀ A, MeasurableSet[G] A → (∫⁻ ω in A, U ω ∂P) = ∫⁻ ω in A, X ω ∂P

def realConditionalExpectationType :=
  ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → (Ω → ℝ) → (Ω → ℝ)

noncomputable def realConditionalExpectationValue : realConditionalExpectationType :=
  fun {_Ω} G _F P X => condExp G P X

def nonnegativeConditionalExpectationType :=
  ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → (Ω → ℝ≥0∞) → (Ω → ℝ≥0∞)

noncomputable def nonnegativeConditionalExpectationValue : nonnegativeConditionalExpectationType :=
  fun {_Ω} G _F P X => condLExp G P X

def conditionalProbabilityType :=
  ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → Set Ω → (Ω → ℝ)

noncomputable def conditionalProbabilityValue : conditionalProbabilityType :=
  fun {_Ω} G _F P B => condExp G P (B.indicator (fun _ => (1 : ℝ)))

def realConditionalExpectationIsVersionType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Integrable X P →
      realVersionValue G P X (realConditionalExpectationValue G P X)

def nonnegativeConditionalExpectationIsVersionType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
      nonnegativeVersionValue G P X (nonnegativeConditionalExpectationValue G P X)

def conditionalProbabilityIsVersionType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (B : Set Ω), MeasurableSet[F] B →
      realVersionValue G P (B.indicator (fun _ => (1 : ℝ)))
        (conditionalProbabilityValue G P B)

def realVersionIffType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X U : Ω → ℝ), Integrable X P →
      (realVersionValue G P X U ↔
        Measurable[G] U ∧ U =ᵐ[P] realConditionalExpectationValue G P X)

def nonnegativeVersionIffType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X U : Ω → ℝ≥0∞), Measurable[F] X →
      (nonnegativeVersionValue G P X U ↔
        Measurable[G] U ∧ U =ᵐ[P] nonnegativeConditionalExpectationValue G P X)

end Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
