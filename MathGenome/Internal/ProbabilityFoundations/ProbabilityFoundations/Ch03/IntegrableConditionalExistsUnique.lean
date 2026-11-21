import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.IntegrableConditionalExistsUnique
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-!
The integrable case of Theorem 3.2 (paper.tex, 819–845).
Existence uses the canonical conditional expectation, and uniqueness uses its
upstream characterization. Taking the maximum with zero removes any negative
values on the null exceptional set without requiring completeness. Comparison
is applied on the measure trimmed to G, where the candidates are measurable,
and then transferred to the original measure.
-/

open MeasureTheory

namespace ProbabilityFoundations.Ch03

universe u

theorem exists_realConditionalExpectationVersion
    {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P] (hGF : G ≤ F)
    (X : Ω → ℝ) (_hXm : Measurable[F] X) (hX : Integrable X P) :
    ∃ U : Ω → ℝ, IsRealConditionalExpectationVersion G P X U := by
  exact ⟨realConditionalExpectation G P X,
    realConditionalExpectation_isVersion G P hGF X hX⟩

theorem realConditionalExpectationVersion_ae_unique
    {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P] (hGF : G ≤ F)
    (X U V : Ω → ℝ) (hX : Integrable X P)
    (hU : IsRealConditionalExpectationVersion G P X U)
    (hV : IsRealConditionalExpectationVersion G P X V) : U =ᵐ[P] V := by
  have hUeq := ((isRealConditionalExpectationVersion_iff G P hGF X U hX).mp hU).2
  have hVeq := ((isRealConditionalExpectationVersion_iff G P hGF X V hX).mp hV).2
  exact hUeq.trans hVeq.symm

/-- This version is real-valued, hence finite everywhere, and nonnegative everywhere. -/
theorem exists_nonnegative_realConditionalExpectationVersion
    {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P] (hGF : G ≤ F)
    (X : Ω → ℝ) (_hXm : Measurable[F] X) (hX : Integrable X P)
    (hXnonneg : ∀ ω, 0 ≤ X ω) :
    ∃ U : Ω → ℝ, IsRealConditionalExpectationVersion G P X U ∧ ∀ ω, 0 ≤ U ω := by
  let U : Ω → ℝ := fun ω => max (realConditionalExpectation G P X ω) 0
  have hCm : Measurable[G] (realConditionalExpectation G P X) :=
    (realConditionalExpectation_isVersion G P hGF X hX).1
  have hUm : Measurable[G] U := hCm.max measurable_const
  have hUeq : U =ᵐ[P] realConditionalExpectation G P X := by
    have hCnonneg : 0 ≤ᵐ[P] realConditionalExpectation G P X :=
      condExp_nonneg (Filter.Eventually.of_forall hXnonneg)
    filter_upwards [hCnonneg] with ω hω
    exact max_eq_left hω
  exact ⟨U, (isRealConditionalExpectationVersion_iff G P hGF X U hX).mpr
    ⟨hUm, hUeq⟩, fun ω => le_max_right _ _⟩

/-- Ordered integrals on all G-events imply almost sure order. -/
theorem ae_le_of_forall_conditional_setIntegral_le
    {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P] (hGF : G ≤ F)
    (U V : Ω → ℝ) (hUm : Measurable[G] U) (hVm : Measurable[G] V)
    (hUi : Integrable U P) (hVi : Integrable V P)
    (htest : ∀ A, MeasurableSet[G] A →
      (∫ ω in A, U ω ∂P) ≤ ∫ ω in A, V ω ∂P) : U ≤ᵐ[P] V := by
  apply ae_le_of_ae_le_trim (hm := hGF)
  apply ae_le_of_forall_setIntegral_le
    (hUi.trim hGF hUm.stronglyMeasurable) (hVi.trim hGF hVm.stronglyMeasurable)
  intro A hA _hfinite
  rw [← setIntegral_trim hGF hUm.stronglyMeasurable hA,
    ← setIntegral_trim hGF hVm.stronglyMeasurable hA]
  exact htest A hA

end ProbabilityFoundations.Ch03
