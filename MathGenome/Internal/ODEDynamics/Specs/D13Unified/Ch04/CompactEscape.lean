import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap
import Mathlib.Topology.Order.Filter

/-! Independent statements of paper.tex, Corollary d13:04:escape.
The field retains its original open domain and continuity. Endpoints and Φ
are the upstream canonical objects. Real endpoints express precisely finite
lifespans. Thresholds assert escape at every sufficiently late/early time;
`Tendsto ... atTop` is the full norm limit, for any finite-dimensional norm. -/
noncomputable section
open Set Filter
open scoped Topology
open D13Unified

namespace Specs.D13Unified.Ch04.CompactEscape
open Ch03.LocalLipschitz Ch04.MaximalSolutionMap
universe u

def rightEscapeExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), locallyLipschitzInStateValue F →
    ∀ s ξ, (s, ξ) ∈ F.domain → ∀ b : ℝ, upperEndpointValue F s ξ = (b : EReal) →
    ∀ K : Set (ℝ × E), IsCompact K → K ⊆ F.domain →
      ∃ τ : ℝ, τ < b ∧ ∀ t ∈ Ioo τ b, (t, solutionValueValue F t s ξ) ∉ K

def leftEscapeExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), locallyLipschitzInStateValue F →
    ∀ s ξ, (s, ξ) ∈ F.domain → ∀ a : ℝ, lowerEndpointValue F s ξ = (a : EReal) →
    ∀ K : Set (ℝ × E), IsCompact K → K ⊆ F.domain →
      ∃ τ : ℝ, a < τ ∧ ∀ t ∈ Ioo a τ, (t, solutionValueValue F t s ξ) ∉ K

def rightNormLimitExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), locallyLipschitzInStateValue F → F.domain = univ →
    ∀ s ξ, (s, ξ) ∈ F.domain → ∀ b : ℝ, upperEndpointValue F s ξ = (b : EReal) →
      Tendsto (fun t => ‖solutionValueValue F t s ξ‖) (𝓝[<] b) atTop

def leftNormLimitExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), locallyLipschitzInStateValue F → F.domain = univ →
    ∀ s ξ, (s, ξ) ∈ F.domain → ∀ a : ℝ, lowerEndpointValue F s ξ = (a : EReal) →
      Tendsto (fun t => ‖solutionValueValue F t s ξ‖) (𝓝[>] a) atTop

end Specs.D13Unified.Ch04.CompactEscape
