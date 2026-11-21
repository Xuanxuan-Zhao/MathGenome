import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.IntegrableConditionalPullout
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! The real integrable part of the measurable-factor theorem (paper.tex,
Theorem 3.4). Mathlib's real pullout theorem allows an arbitrary strongly
measurable factor when X and H * X are integrable. Its conclusion identifies
the pulled-out product with an integrable conditional expectation. -/

open MeasureTheory

namespace ProbabilityFoundations.Ch03

universe u

/-- Taking out an arbitrary real G-measurable factor, including integrability
of the resulting product. -/
theorem realConditionalExpectation_mul :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H X : Ω → ℝ), Measurable[G] H → Integrable X P →
      Integrable (fun ω => H ω * X ω) P →
      Integrable (fun ω => H ω * realConditionalExpectation (F := F) G P X ω) P ∧
      realConditionalExpectation (F := F) G P (fun ω => H ω * X ω) =ᵐ[P]
        (fun ω => H ω * realConditionalExpectation (F := F) G P X ω) := by
  intro Ω G F P _ _hGF H X hH hX hHX
  have hEq : realConditionalExpectation (F := F) G P (fun ω => H ω * X ω) =ᵐ[P]
      (fun ω => H ω * realConditionalExpectation (F := F) G P X ω) :=
    condExp_mul_of_stronglyMeasurable_left hH.stronglyMeasurable hHX hX
  exact ⟨integrable_condExp.congr hEq, hEq⟩

/-- Bounded measurable factors satisfy the integrable pullout formula.
An almost-sure bound suffices, without a separate product hypothesis. -/
theorem realConditionalExpectation_mul_of_bound :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H X : Ω → ℝ), Measurable[G] H → Integrable X P →
    ∀ (C : ℝ), (∀ᵐ ω ∂P, |H ω| ≤ C) →
      Integrable (fun ω => H ω * X ω) P ∧
      Integrable (fun ω => H ω * realConditionalExpectation (F := F) G P X ω) P ∧
      realConditionalExpectation (F := F) G P (fun ω => H ω * X ω) =ᵐ[P]
        (fun ω => H ω * realConditionalExpectation (F := F) G P X ω) := by
  intro Ω G F P _ hGF H X hH hX C hbound
  have hHX : Integrable (fun ω => H ω * X ω) P :=
    hX.bdd_mul (hH.mono hGF le_rfl).aestronglyMeasurable (by
      simpa only [Real.norm_eq_abs] using hbound)
  exact ⟨hHX, realConditionalExpectation_mul (F := F) G P hGF H X hH hX hHX⟩

end ProbabilityFoundations.Ch03
