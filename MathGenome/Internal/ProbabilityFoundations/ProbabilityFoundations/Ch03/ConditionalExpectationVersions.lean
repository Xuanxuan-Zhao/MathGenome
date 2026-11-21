import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityObjects

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

namespace ProbabilityFoundations.Ch03

universe u

def IsRealConditionalExpectationVersion :
    ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → (Ω → ℝ) → (Ω → ℝ) → Prop :=
  fun {_Ω} G _F P X U =>
    Measurable[G] U ∧ Integrable U P ∧
      ∀ A, MeasurableSet[G] A → (∫ ω in A, U ω ∂P) = ∫ ω in A, X ω ∂P

def IsNonnegativeConditionalExpectationVersion :
    ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → (Ω → ℝ≥0∞) → (Ω → ℝ≥0∞) → Prop :=
  fun {_Ω} G _F P X U =>
    Measurable[G] U ∧
      ∀ A, MeasurableSet[G] A → (∫⁻ ω in A, U ω ∂P) = ∫⁻ ω in A, X ω ∂P

noncomputable def realConditionalExpectation :
    ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → (Ω → ℝ) → (Ω → ℝ) :=
  fun {_Ω} G _F P X => condExp G P X

noncomputable def nonnegativeConditionalExpectation :
    ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → (Ω → ℝ≥0∞) → (Ω → ℝ≥0∞) :=
  fun {_Ω} G _F P X => condLExp G P X

noncomputable def conditionalProbability :
    ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
    Measure[F] Ω → Set Ω → (Ω → ℝ) :=
  fun {_Ω} G _F P B => condExp G P (B.indicator (fun _ => (1 : ℝ)))

theorem realConditionalExpectation_isVersion :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Integrable X P →
      IsRealConditionalExpectationVersion G P X (realConditionalExpectation G P X) := by
  intro Ω G F P _ hGF X hX
  exact ⟨stronglyMeasurable_condExp.measurable, integrable_condExp,
    fun A hA => setIntegral_condExp hGF hX hA⟩

theorem nonnegativeConditionalExpectation_isVersion :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
      IsNonnegativeConditionalExpectationVersion G P X (nonnegativeConditionalExpectation G P X) := by
  intro Ω G F P _ hGF X _hX
  exact ⟨measurable_condLExp G P X, fun A hA => setLIntegral_condLExp hGF P X hA⟩

theorem conditionalProbability_isVersion :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (B : Set Ω), MeasurableSet[F] B →
      IsRealConditionalExpectationVersion G P (B.indicator (fun _ => (1 : ℝ)))
        (conditionalProbability G P B) := by
  intro Ω G F P _ hGF B hB
  exact realConditionalExpectation_isVersion G P hGF _
    (Ch01.indicator_integrable P B hB).1

theorem isRealConditionalExpectationVersion_iff :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X U : Ω → ℝ), Integrable X P →
      (IsRealConditionalExpectationVersion G P X U ↔
        Measurable[G] U ∧ U =ᵐ[P] realConditionalExpectation G P X) := by
  intro Ω G F P _ hGF X U hX
  constructor
  · rintro ⟨hU, hUi, htest⟩
    refine ⟨hU, ?_⟩
    exact ae_eq_condExp_of_forall_setIntegral_eq hGF hX
      (fun A _ _ => hUi.integrableOn) (fun A hA _ => htest A hA)
      hU.stronglyMeasurable.aestronglyMeasurable
  · rintro ⟨hU, hEq⟩
    refine ⟨hU, integrable_condExp.congr hEq.symm, ?_⟩
    intro A hA
    rw [integral_congr_ae (ae_restrict_of_ae hEq)]
    exact setIntegral_condExp hGF hX hA

theorem isNonnegativeConditionalExpectationVersion_iff :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X U : Ω → ℝ≥0∞), Measurable[F] X →
      (IsNonnegativeConditionalExpectationVersion G P X U ↔
        Measurable[G] U ∧ U =ᵐ[P] nonnegativeConditionalExpectation G P X) := by
  intro Ω G F P _ hGF X U _hX
  constructor
  · rintro ⟨hU, htest⟩
    exact ⟨hU, ae_eq_condLExp hGF P X hU htest⟩
  · rintro ⟨hU, hEq⟩
    refine ⟨hU, ?_⟩
    intro A hA
    rw [lintegral_congr_ae (ae_restrict_of_ae hEq)]
    exact setLIntegral_condLExp hGF P X hA

end ProbabilityFoundations.Ch03
