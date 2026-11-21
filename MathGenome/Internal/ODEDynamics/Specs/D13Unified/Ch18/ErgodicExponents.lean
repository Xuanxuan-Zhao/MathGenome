import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.GrowthDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.Birkhoff
import Mathlib.LinearAlgebra.Determinant

/-! Proposition d13:18:ergodic-exponents. A probability on the subtype K is
exactly a probability supported on K; all derivatives are ambient derivatives
on the open neighbourhood U, never derivatives within K.

The two hypotheses `hnz` and `hlog` together express L¹ integrability of
log |det DF| with the paper's convention log 0 = -∞. Merely requiring the
totalized real logarithm to be integrable would incorrectly admit zero
determinants on sets of positive measure. No global measurability or
differentiability of the representative outside U is required.
-/
namespace Specs.D13Unified.Ch18.ErgodicExponents
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
universe u

def volumeExponentStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    (F : E → E) (U K : Set E), IsOpen U → ContDiffOn ℝ 1 F U →
    IsCompact K → K ⊆ U → ∀ (hK : MapsTo F K K) (μ : Measure K)
    [IsProbabilityMeasure μ],
    let T : K → K := fun x => ⟨F x, hK x.property⟩
    let J : ℕ → E → ℝ := fun n x => LinearMap.det (fderiv ℝ F^[n] x).toLinearMap
    let g : K → ℝ := fun x => Real.log |J 1 x|
    MeasurePreserving T μ μ →
    (∀ᵐ (x : K) ∂μ, J 1 x ≠ 0) → Integrable g μ →
    ∃ gstar : K → ℝ, Integrable gstar μ ∧
      (gstar ∘ T =ᵐ[μ] gstar) ∧
      (∫ x, gstar x ∂μ) = (∫ x, g x ∂μ) ∧
      (Ch19.MeasureDefinitions.IsErgodic T μ →
        gstar =ᵐ[μ] fun _ => ∫ x, g x ∂μ) ∧
      ∀ᵐ (x : K) ∂μ,
        (∀ j : ℕ, J 1 (F^[j] x) ≠ 0) ∧
        (∀ n : ℕ, J n x ≠ 0 ∧
          Real.log |J n x| = ∑ j ∈ Finset.range n, g (T^[j] x)) ∧
        Tendsto (fun n : ℕ => Real.log |J n x| / (n : ℝ)) atTop (𝓝 (gstar x)) ∧
        Tendsto (fun n : ℕ => GrowthDefinitions.logarithmicRate (n : ℝ) |J n x|)
          atTop (𝓝 (gstar x : EReal)) ∧
        (Module.finrank ℝ E = 1 → ∀ v : E, v ≠ 0 →
          Tendsto (fun n : ℕ => GrowthDefinitions.directionalRate
            (fderiv ℝ F^[n+1] x) v (n+1)) atTop (𝓝 (gstar x : EReal)))

/-- Specialization to the shared C¹-map and directional-exponent objects.
The common full-measure set works for every nonzero vector, even though the
set of directions is uncountable. No such directional conclusion is asserted
in higher dimensions. -/
def scalarExponentStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E], Module.finrank ℝ E = 1 →
    ∀ (F : _root_.D13Unified.Ch18.GrowthDefinitions.C1SelfMap E) (K : Set E),
    IsCompact K → ∀ (hKU : K ⊆ F.domain) (hK : MapsTo F.value K K) (μ : Measure K)
    [IsProbabilityMeasure μ],
    let T : K → K := fun x => ⟨F.value x, hK x.property⟩
    let J : E → ℝ := fun x => LinearMap.det (fderiv ℝ F.value x).toLinearMap
    let g : K → ℝ := fun x => Real.log |J x|
    MeasurePreserving T μ μ →
    (∀ᵐ (x : K) ∂μ, J x ≠ 0) → Integrable g μ →
    ∃ gstar : K → ℝ, Integrable gstar μ ∧
      (gstar ∘ T =ᵐ[μ] gstar) ∧
      (∫ x, gstar x ∂μ) = (∫ x, g x ∂μ) ∧
      (Ch19.MeasureDefinitions.IsErgodic T μ →
        gstar =ᵐ[μ] fun _ => ∫ x, g x ∂μ) ∧
      ∀ᵐ (x : K) ∂μ, ∀ (v : E) (hv : v ≠ 0),
        GrowthDefinitions.HasDiscreteDirectionalExponent F ⟨x, hKU x.property⟩
          v hv (gstar x : EReal)

end
end Specs.D13Unified.Ch18.ErgodicExponents
