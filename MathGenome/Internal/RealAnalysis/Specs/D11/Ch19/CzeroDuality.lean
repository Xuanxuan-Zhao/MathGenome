import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.ComplexRadonVariation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CzeroBanachDensity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarIntegration
import Mathlib.Analysis.Normed.Operator.Basic

/-! The full scalar duality statement, paper.tex:5601–5609.
The linear maps below act on the canonical scalar Borel measures. Their
restriction to the Radon measures is onto and one-to-one, and preserves the
variation distance. Integration is asserted with its absolute integrability
witness, using the shared Jordan integral, without a conjugate in the pairing.
No countability, compactness, or nonemptiness of X is assumed. -/
namespace Specs.D11.Ch19.CzeroDuality
open MeasureTheory Set
open ComplexRadonVariation
open Specs.D11.Ch14.ScalarIntegration Specs.D11.Ch14.TotalVariation
universe u
local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

def real_duality : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X],
    ∃ T : SignedMeasure X →ₗ[ℝ] (ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ),
      (∀ (ν : SignedMeasure X) (f : ZeroAtInftyContinuousMap X ℝ),
        ∃ hf : signedIntegrable_value ν (f : X → ℝ),
        T ν f = signedIntegral_value ν f hf) ∧
      (∀ ν, isSignedRadon_value ν → ‖T ν‖ = (totalVariation_value ν univ).toReal) ∧
      (∀ ν η, isSignedRadon_value ν → isSignedRadon_value η →
        ‖T ν - T η‖ = (totalVariation_value (ν - η) univ).toReal) ∧
      (∀ L : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ,
        ∃! ν : SignedMeasure X, isSignedRadon_value ν ∧ T ν = L)

def complex_duality : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X],
    ∃ T : ComplexMeasure X →ₗ[ℂ] (ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ),
      (∀ (ν : ComplexMeasure X) (f : ZeroAtInftyContinuousMap X ℂ),
        ∃ hf : complexIntegrable_value ν (f : X → ℂ),
        T ν f = complexIntegral_value ν f hf) ∧
      (∀ ν, isComplexRadon_value ν → ‖T ν‖ = (totalVariation_value ν univ).toReal) ∧
      (∀ ν η, isComplexRadon_value ν → isComplexRadon_value η →
        ‖T ν - T η‖ = (totalVariation_value (ν - η) univ).toReal) ∧
      (∀ L : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ,
        ∃! ν : ComplexMeasure X, isComplexRadon_value ν ∧ T ν = L)
end Specs.D11.Ch19.CzeroDuality
