import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.NonnegativeConditionalPullout
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-! The nonnegative pullout theorem, with extended products. Event tests say
that the measures with densities U and X agree when trimmed to G. Integrating
a G-measurable factor against these equal measures proves the weighted event
tests, including infinite factors and infinite integrals. -/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch03

universe u

/-- Equal event integrals imply equal integrals weighted by any nonnegative
extended G-measurable factor, on each G-event. -/
theorem setLIntegral_mul_eq_of_forall_setLIntegral_eq
    {Ω : Type u} {G : MeasurableSpace Ω} [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) (hGF : G ≤ F) {U X H : Ω → ℝ≥0∞}
    (hU : Measurable[F] U) (hX : Measurable[F] X) (hH : Measurable[G] H)
    (htest : ∀ A, MeasurableSet[G] A →
      (∫⁻ ω in A, U ω ∂P) = ∫⁻ ω in A, X ω ∂P)
    {A : Set Ω} (hA : MeasurableSet[G] A) :
    (∫⁻ ω in A, H ω * U ω ∂P) = ∫⁻ ω in A, H ω * X ω ∂P := by
  have hmeas : (P.withDensity U).trim hGF = (P.withDensity X).trim hGF := by
    apply @Measure.ext _ G
    intro B hB
    rw [trim_measurableSet_eq hGF hB, trim_measurableSet_eq hGF hB,
      withDensity_apply _ (hGF B hB), withDensity_apply _ (hGF B hB)]
    exact htest B hB
  calc
    (∫⁻ ω in A, H ω * U ω ∂P) = ∫⁻ ω in A, H ω ∂P.withDensity U := by
      rw [setLIntegral_withDensity_eq_setLIntegral_mul P hU (hH.mono hGF le_rfl)
        (hGF A hA)]
      exact lintegral_congr (fun ω => mul_comm _ _)
    _ = ∫⁻ ω in A, H ω ∂(P.withDensity U).trim hGF :=
      (setLIntegral_trim hGF hH hA).symm
    _ = ∫⁻ ω in A, H ω ∂(P.withDensity X).trim hGF := by rw [hmeas]
    _ = ∫⁻ ω in A, H ω ∂P.withDensity X := setLIntegral_trim hGF hH hA
    _ = ∫⁻ ω in A, H ω * X ω ∂P := by
      rw [setLIntegral_withDensity_eq_setLIntegral_mul P hX (hH.mono hGF le_rfl)
        (hGF A hA)]
      exact lintegral_congr (fun ω => mul_comm _ _)

/-- The pulled-out product is a measurable extended conditional version. -/
theorem nonnegativeConditionalExpectation_mul_isVersion :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H X : Ω → ℝ≥0∞), Measurable[G] H → Measurable[F] X →
      IsNonnegativeConditionalExpectationVersion (F := F) G P (fun ω => H ω * X ω)
        (fun ω => H ω * nonnegativeConditionalExpectation (F := F) G P X ω) := by
  intro Ω G F P _ hGF H X hH hX
  have hV := nonnegativeConditionalExpectation_isVersion (F := F) G P hGF X hX
  refine ⟨hH.mul hV.1, ?_⟩
  intro A hA
  exact setLIntegral_mul_eq_of_forall_setLIntegral_eq P hGF
    (hV.1.mono hGF le_rfl) hX hH hV.2 hA

/-- Taking out a G-measurable factor, with neither factor required finite. -/
theorem nonnegativeConditionalExpectation_mul :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H X : Ω → ℝ≥0∞), Measurable[G] H → Measurable[F] X →
      nonnegativeConditionalExpectation (F := F) G P (fun ω => H ω * X ω) =ᵐ[P]
        (fun ω => H ω * nonnegativeConditionalExpectation (F := F) G P X ω) := by
  intro Ω G F P _ hGF H X hH hX
  have hproduct := nonnegativeConditionalExpectation_mul_isVersion (F := F) G P hGF H X hH hX
  exact ((isNonnegativeConditionalExpectationVersion_iff (F := F) G P hGF
    (fun ω => H ω * X ω) _ ((hH.mono hGF le_rfl).mul hX)).mp hproduct).2.symm

end ProbabilityFoundations.Ch03
