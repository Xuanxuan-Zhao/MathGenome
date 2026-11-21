import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.NonnegativeConditionalExistsUnique
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.IntegrableConditionalExistsUnique
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

/-! The nonnegative part of Theorem 3.2.
Existence and uniqueness use the canonical conditional Lebesgue expectation.
Comparison uses the finite measure P trimmed to G; no finiteness assumption
is made on the measure weighted by X. The real/extended agreement is stated
both for canonical expectations and arbitrary measurable versions. -/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch03

universe u

theorem exists_nonnegativeConditionalExpectationVersion :
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
        ∃ U : Ω → ℝ≥0∞, IsNonnegativeConditionalExpectationVersion G P X U := by
  intro Ω G F P _ hGF X hXm
  exact ⟨nonnegativeConditionalExpectation G P X,
    nonnegativeConditionalExpectation_isVersion G P hGF X hXm⟩

theorem nonnegativeConditionalExpectationVersion_ae_unique :
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (X U V : Ω → ℝ≥0∞), Measurable[F] X →
        IsNonnegativeConditionalExpectationVersion G P X U → IsNonnegativeConditionalExpectationVersion G P X V → U =ᵐ[P] V := by
  intro Ω G F P _ hGF X U V hXm hU hV
  have hUeq := ((isNonnegativeConditionalExpectationVersion_iff G P hGF X U hXm).mp hU).2
  have hVeq := ((isNonnegativeConditionalExpectationVersion_iff G P hGF X V hXm).mp hV).2
  exact hUeq.trans hVeq.symm

theorem ae_le_of_forall_conditional_setLIntegral_le :
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (U V : Ω → ℝ≥0∞), Measurable[G] U → Measurable[G] V →
        (∀ A, MeasurableSet[G] A →
          (∫⁻ ω in A, U ω ∂P) ≤ ∫⁻ ω in A, V ω ∂P) → U ≤ᵐ[P] V := by
  intro Ω G F P _ hGF U V hUm hVm htest
  apply ae_le_of_ae_le_trim (hm := hGF)
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := P.trim hGF) hUm
  intro A hA _hfinite
  rw [setLIntegral_trim hGF hUm hA, setLIntegral_trim hGF hVm hA]
  exact htest A hA

theorem nonnegativeConditionalExpectation_real_agreement :
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (X : Ω → ℝ), Measurable[F] X → Integrable X P → (0 ≤ᵐ[P] X) →
        (∀ᵐ ω ∂P, nonnegativeConditionalExpectation G P
          (fun ω => ENNReal.ofReal (X ω)) ω < ∞) ∧
        nonnegativeConditionalExpectation G P (fun ω => ENNReal.ofReal (X ω)) =ᵐ[P]
          (fun ω => ENNReal.ofReal (realConditionalExpectation G P X ω)) := by
  intro Ω G F P _ _hGF X _hXm hXi hXpos
  have heq : nonnegativeConditionalExpectation G P (fun ω => ENNReal.ofReal (X ω)) =ᵐ[P]
      (fun ω => ENNReal.ofReal (realConditionalExpectation G P X ω)) :=
    condLExp_ofReal G hXi hXpos
  refine ⟨?_, heq⟩
  filter_upwards [heq] with ω hω
  rw [hω]
  exact ENNReal.ofReal_lt_top

theorem nonnegative_realConditionalExpectationVersions_agree :
    ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
      (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
      ∀ (X V : Ω → ℝ) (U : Ω → ℝ≥0∞),
        Measurable[F] X → Integrable X P → (0 ≤ᵐ[P] X) →
        IsNonnegativeConditionalExpectationVersion G P (fun ω => ENNReal.ofReal (X ω)) U →
        IsRealConditionalExpectationVersion G P X V →
        (∀ᵐ ω ∂P, U ω < ∞) ∧ U =ᵐ[P] (fun ω => ENNReal.ofReal (V ω)) := by
  intro Ω G F P _ hGF X V U hXm hXi hXpos hU hV
  have hUeq := ((isNonnegativeConditionalExpectationVersion_iff G P hGF
    (fun ω => ENNReal.ofReal (X ω)) U hXm.ennreal_ofReal).mp hU).2
  have hVeq := ((isRealConditionalExpectationVersion_iff G P hGF X V hXi).mp hV).2
  obtain ⟨hfinite, heq⟩ := nonnegativeConditionalExpectation_real_agreement
    G P hGF X hXm hXi hXpos
  constructor
  · filter_upwards [hUeq, hfinite] with ω hω hfin
    exact hω ▸ hfin
  · filter_upwards [hUeq, heq, hVeq] with ω hω hbridge hreal
    exact hω.trans (hbridge.trans (congrArg ENNReal.ofReal hreal.symm))

end ProbabilityFoundations.Ch03
