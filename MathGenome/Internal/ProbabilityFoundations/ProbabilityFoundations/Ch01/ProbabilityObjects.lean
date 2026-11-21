import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityObjects

/-! Interfaces and facts for Definition 1.1. All measures, sigma algebras,
measurability, integration and almost-everywhere predicates are Mathlib's
canonical objects. In particular the original space need not be complete. -/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch01

universe u v

/-- An event belongs to the specified sigma algebra. -/
def IsEvent {Ω : Type u} [MeasurableSpace Ω] (A : Set Ω) : Prop := MeasurableSet A

/-- A random element is measurable for the specified source and target spaces. -/
def IsRandomElement {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S]
    (X : Ω → S) : Prop := Measurable X

/-- The target sigma algebra of a real random variable is the Borel sigma algebra. -/
def IsRealRandomVariable {Ω : Type u} [mΩ : MeasurableSpace Ω] (X : Ω → ℝ) : Prop :=
  @Measurable Ω ℝ mΩ (borel ℝ) X

/-- Expectation of an integrable real variable uses the Bochner integral.
Outside the integrable domain this inherits Mathlib's totalized definition. -/
noncomputable def realExpectation {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂P

/-- Expectation of an integrable complex variable uses the Bochner integral. -/
noncomputable def complexExpectation {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℂ) : ℂ := ∫ ω, X ω ∂P

/-- Extended nonnegative expectation permits the value `∞`. -/
noncomputable def nonnegativeExpectation {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ ω, X ω ∂P

/-- Almost surely means eventually in the canonical almost-everywhere filter. -/
def AlmostSurely {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (p : Ω → Prop) : Prop :=
  ∀ᵐ ω ∂P, p ω

/-- A canonical measure is a probability measure exactly when its mass is one. -/
theorem probability_normalization {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) :
    IsProbabilityMeasure P ↔ P Set.univ = 1 := isProbabilityMeasure_iff

theorem real_random_variable_iff {Ω : Type u} [MeasurableSpace Ω] (X : Ω → ℝ) :
    IsRealRandomVariable X ↔ IsRandomElement X := Iff.rfl

/-- Event indicators are in the integrable domain of real and complex expectation. -/
theorem indicator_integrable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : IsEvent A) :
    Integrable (A.indicator (fun _ => (1 : ℝ))) P ∧
    Integrable (A.indicator (fun _ => (1 : ℂ))) P :=
  ⟨(integrable_const (1 : ℝ)).indicator hA, (integrable_const (1 : ℂ)).indicator hA⟩

theorem real_indicator_expectation {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : IsEvent A) :
    realExpectation P (A.indicator (fun _ => (1 : ℝ))) = (P A).toReal := by
  exact integral_indicator_one hA

theorem complex_indicator_expectation {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : IsEvent A) :
    complexExpectation P (A.indicator (fun _ => (1 : ℂ))) = ((P A).toReal : ℂ) := by
  simp [complexExpectation, integral_indicator_const (1 : ℂ) hA, measureReal_def]

theorem nonnegative_indicator_expectation {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : IsEvent A) :
    nonnegativeExpectation P (A.indicator (fun _ => (1 : ℝ≥0∞))) = P A := by
  exact lintegral_indicator_one hA

/-- The exceptional set can be chosen measurable even on an incomplete space.
The property itself is arbitrary and is not assumed measurable. -/
theorem almostSurely_iff_measurable_null {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (p : Ω → Prop) :
    AlmostSurely P p ↔
      ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → p ω := by
  classical
  constructor
  · intro hp
    obtain ⟨N, hsub, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
    refine ⟨N, hN, hzero, ?_⟩
    intro ω hω
    by_contra hnot
    exact hω (hsub hnot)
  · rintro ⟨N, _, hzero, hp⟩
    apply ae_iff.mpr
    apply measure_mono_null _ hzero
    intro ω hω
    by_contra hnot
    exact hω (hp ω hnot)

/-- Almost sure truth is equivalent to truth on a measurable probability-one event. -/
theorem almostSurely_iff_measurable_one {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : Ω → Prop) :
    AlmostSurely P p ↔
      ∃ A : Set Ω, MeasurableSet A ∧ P A = 1 ∧ ∀ ω ∈ A, p ω := by
  constructor
  · intro hp
    obtain ⟨N, hN, hzero, hpN⟩ := (almostSurely_iff_measurable_null P p).mp hp
    exact ⟨Nᶜ, hN.compl, (prob_compl_eq_one_iff hN).mpr hzero, hpN⟩
  · rintro ⟨A, hA, hone, hpA⟩
    have hAe : ∀ᵐ ω ∂P, ω ∈ A := (mem_ae_iff_prob_eq_one hA).mpr hone
    exact hAe.mono hpA

end ProbabilityFoundations.Ch01
