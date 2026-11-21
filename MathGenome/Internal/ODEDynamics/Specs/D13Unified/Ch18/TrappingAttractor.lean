import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.TrappingLimit
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.AttractorDefinition

/-! Full independent statement of paper.tex, Theorem d13:18:trapping-attractor.
The union uses preimages of natural-number iterates. No inverse map or
injectivity hypothesis is involved. -/
namespace Specs.D13Unified.Ch18.TrappingAttractor

universe u
open Set Filter
open scoped Topology
open Specs.D13Unified.Ch15.DiscreteDefinitions
open Specs.D13Unified.Ch18.TrappingLimit
open Specs.D13Unified.Ch18.AttractorDefinition

def compact_trapping_attractorStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (K : Set X),
    Continuous F → IsCompact K → K.Nonempty → F '' K ⊆ interior K →
    StableAttractor F (trappingLimit F K) ∧
      (∀ V ∈ 𝓝ˢ (trappingLimit F K),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → iterate F n '' K ⊆ V) ∧
      IsOpen (⋃ n : ℕ, (iterate F n) ⁻¹' interior K) ∧
      (⋃ n : ℕ, (iterate F n) ⁻¹' interior K) ⊆ basin F (trappingLimit F K)

end Specs.D13Unified.Ch18.TrappingAttractor
