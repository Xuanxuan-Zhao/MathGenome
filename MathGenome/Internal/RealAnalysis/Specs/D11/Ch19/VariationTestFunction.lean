import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.ComplexRadonVariation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarIntegration
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Independent statements of paper.tex, `d11:19:variation-test-function`.
The native Cc space has no norm instance; its canonical bounded continuous
map carries precisely the uniform norm. Integrability is asserted before
using the shared, proof-indexed Jordan integrals. All domains are Borel. -/
namespace Specs.D11.Ch19.VariationTestFunction
open Set MeasureTheory
open ComplexRadonVariation
open Specs.D11.Ch14.ScalarIntegration Specs.D11.Ch14.TotalVariation
universe u
local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

def signed_variation_test_function : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (ν : @SignedMeasure X (borel X)), isSignedRadon_value ν →
    ∀ ε : ℝ, 0 < ε → ∃ f : CompactlySupportedContinuousMap X ℝ,
      ‖f.toBoundedContinuousFunction‖ ≤ 1 ∧
      ∃ hf : signedIntegrable_value ν (f : X → ℝ),
        (totalVariation_value ν univ).toReal - ε ≤ ‖signedIntegral_value ν f hf‖

def complex_variation_test_function : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (ν : @ComplexMeasure X (borel X)), isComplexRadon_value ν →
    ∀ ε : ℝ, 0 < ε → ∃ f : CompactlySupportedContinuousMap X ℂ,
      ‖f.toBoundedContinuousFunction‖ ≤ 1 ∧
      ∃ hf : complexIntegrable_value ν (f : X → ℂ),
        (totalVariation_value ν univ).toReal - ε ≤ ‖complexIntegral_value ν f hf‖
end Specs.D11.Ch19.VariationTestFunction
