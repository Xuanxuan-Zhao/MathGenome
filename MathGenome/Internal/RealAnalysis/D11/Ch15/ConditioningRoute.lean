import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.ConditioningRoute
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNSignedComplex

/-! Conditional expectation via the finite signed Radon–Nikodym theorem.
The restricted probability is finite for every sub-sigma-algebra. RN is applied
to the restriction of `P.withDensityᵥ X`, and the trim identities transfer its
integrability, integral equations and a.e. uniqueness back to the original P.
-/

open Set MeasureTheory
universe u
noncomputable section

namespace D11.Ch15.ConditioningRoute

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

def signedMeasure (P : Measure Ω) (T : MeasurableSpace Ω) (hT : T ≤ mΩ)
    (X : Ω → ℝ) (_ : Integrable X P) : @SignedMeasure Ω T :=
  (P.withDensityᵥ X).trim hT

theorem signedMeasure_apply (P : Measure Ω) (T : MeasurableSpace Ω) (hT : T ≤ mΩ)
    (X : Ω → ℝ) (hX : Integrable X P) (B : Set Ω) (hB : MeasurableSet[T] B) :
    @signedMeasure Ω mΩ P T hT X hX B = ∫ ω in B, X ω ∂P := by
  change (P.withDensityᵥ X).trim hT B = _
  rw [VectorMeasure.trim_measurableSet_eq hT hB, withDensityᵥ_apply hX (hT B hB)]

theorem signedMeasure_absolutelyContinuous (P : Measure Ω) (T : MeasurableSpace Ω)
    (hT : T ≤ mΩ) (X : Ω → ℝ) (hX : Integrable X P) :
    AbsoluteContinuity.scalarAbsolutelyContinuous
      (@signedMeasure Ω mΩ P T hT X hX) (P.trim hT) := by
  apply (AbsoluteContinuity.scalar_iff _ _).mpr
  intro B hB hzero
  rw [@signedMeasure_apply Ω mΩ P T hT X hX B hB]
  have hPB : P B = 0 := by
    rwa [trim_measurableSet_eq hT hB] at hzero
  simp [hPB]

theorem conditioning_route : Specs.D11.Ch15.ConditioningRoute.conditioning_route := by
  intro Ω mΩ P _ T hT X _hXm hX
  obtain ⟨Y, hYm, hYi, hYeq, _, hunique⟩ :=
    @RNSignedComplex.rn_signed Ω T (P.trim hT) _
      (@signedMeasure Ω mΩ P T hT X hX)
      (@signedMeasure_absolutelyContinuous Ω mΩ P T hT X hX)
  refine ⟨Y, hYm, integrable_of_integrable_trim hT hYi, ?_, ?_⟩
  · intro B hB
    rw [setIntegral_trim hT hYm.stronglyMeasurable hB, ← hYeq B hB]
    exact @signedMeasure_apply Ω mΩ P T hT X hX B hB
  · intro Z hZm hZi hZeq
    apply ae_eq_of_ae_eq_trim (hm := hT)
    apply hunique Z (hZi.trim hT hZm.stronglyMeasurable)
    intro B hB
    rw [@signedMeasure_apply Ω mΩ P T hT X hX B hB,
      ← setIntegral_trim hT hZm.stronglyMeasurable hB]
    exact (hZeq B hB).symm

end D11.Ch15.ConditioningRoute
