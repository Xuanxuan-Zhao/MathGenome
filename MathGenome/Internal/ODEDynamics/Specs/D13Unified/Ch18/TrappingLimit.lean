import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Topology.Separation.Hausdorff

/-! Independent specification of the nested-limit and uniform-neighborhood
clauses of paper.tex, Theorem `d13:18:trapping-attractor`.
The neighborhood filter of a set includes neighborhoods that are not open.
No injectivity of the map is assumed. -/
namespace Specs.D13Unified.Ch18.TrappingLimit

universe u
open Set Filter
open scoped Topology
open D13Unified.Ch15.DiscreteDefinitions

def trappingLimitType := {X : Type u} → (X → X) → Set X → Set X

/-- The intersection includes the zeroth image, which is K itself. -/
def trappingLimit : trappingLimitType :=
  fun F K => ⋂ n : ℕ, iterate F n '' K

/-- Precisely the compact limit, image equality, and uniform tail conclusion
under the original metric-space trapping hypotheses. -/
def compact_trapping_limitStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (K : Set X),
    Continuous F → IsCompact K → K.Nonempty → F '' K ⊆ interior K →
    (trappingLimit F K).Nonempty ∧ IsCompact (trappingLimit F K) ∧
      Invariant F (trappingLimit F K) ∧
      ∀ V ∈ 𝓝ˢ (trappingLimit F K),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → iterate F n '' K ⊆ V

end Specs.D13Unified.Ch18.TrappingLimit
