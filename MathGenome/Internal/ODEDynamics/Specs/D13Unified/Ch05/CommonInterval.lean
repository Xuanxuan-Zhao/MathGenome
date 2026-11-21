import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.CompactTube
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.PerturbationResidual
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap

/-! Persistence on the whole compact interval, paper.tex d13:05:common-interval.
The canonical maximal curve and its actual interval are the shared Chapter 4
objects. Their IVP correctness and uniqueness are proved upstream; inclusion
of the closed interval below asserts existence there, including both endpoints.
The second field has precisely the original domain and its own local Lipschitz
constants, with no common bound on those constants imposed. -/
noncomputable section
open Set Metric D13Unified

namespace Specs.D13Unified.Ch05.CommonInterval
open Ch01.SolutionConcepts Ch03.LocalLipschitz Ch04.MaximalSolutionMap
universe u

def commonIntervalExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E), locallyLipschitzInStateValue F →
    ∀ (I : OpenTimeInterval) (x : ℝ → E), classicalSolutionOnValue F I x →
    ∀ a b : ℝ, a ≤ b → Icc a b ⊆ I.carrier →
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧ IsCompact (closedTube x a b ρ) ∧
      closedTube x a b ρ ⊆ F.domain ∧
      (∀ t ∈ Icc a b, ∀ z ∈ closedBall (x t) ρ, ∀ w ∈ closedBall (x t) ρ,
        ‖F.eval t z - F.eval t w‖ ≤ L * ‖z - w‖) ∧
      ∀ (G : ODE E), G.domain = F.domain → locallyLipschitzInStateValue G →
      ∀ δ : ℝ, 0 ≤ δ →
      (∀ q ∈ closedTube x a b ρ, ‖G.eval q.1 q.2 - F.eval q.1 q.2‖ ≤ δ) →
      ∀ (s : ℝ) (ξ : E), s ∈ Icc a b →
      Real.exp (L * (b - a)) * (‖ξ - x s‖ + δ * (b - a)) < ρ / 2 →
      Icc a b ⊆ (maximalIntervalValue G s ξ).carrier ∧
      classicalIVPOnValue G (maximalIntervalValue G s ξ) (solutionCurveValue G s ξ) s ξ ∧
      (∀ (J : OpenTimeInterval) (y : ℝ → E), classicalIVPOnValue G J y s ξ →
        EqOn (solutionCurveValue G s ξ) y J.carrier) ∧
      ∀ t ∈ Icc a b,
        ‖solutionCurveValue G s ξ t - x t‖ ≤
          ‖ξ - x s‖ * Real.exp (L * |t - s|) + δ * Gronwall.EValue L |t - s| ∧
        ‖ξ - x s‖ * Real.exp (L * |t - s|) + δ * Gronwall.EValue L |t - s| < ρ / 2

end Specs.D13Unified.Ch05.CommonInterval
