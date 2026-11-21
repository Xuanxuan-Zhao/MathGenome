import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalLipschitz
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.Gronwall

/-! Independent statements of paper.tex, Theorem d13:04:linear-growth.
The normed realization is arbitrary and finite dimensional. ODE carries
continuity on its open domain. Estimates concern actual solution intervals,
and the two endpoint bounds imply the whole intervening segment is in [-B,B].
No uniqueness or maximality is needed for the quantitative assertion. -/
noncomputable section
open Set

namespace Specs.D13Unified.Ch04.LinearGrowth
open _root_.D13Unified
open Ch01.SolutionConcepts Ch03.LocalLipschitz
universe u

def positiveEstimateExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E) (I : TimeInterval) (x : ℝ → E), solutionOnValue F I x →
    ∀ (B a b : ℝ), 0 ≤ a → 0 < b →
    (∀ r : ℝ, |r| ≤ B → ∀ y : E, ‖F.eval r y‖ ≤ a + b * ‖y‖) →
    ∀ s ∈ I.carrier, ∀ t ∈ I.carrier, |s| ≤ B → |t| ≤ B →
      ‖x t‖ ≤ ‖x s‖ * Real.exp (b * |t - s|) +
        a * (Real.exp (b * |t - s|) - 1) / b

def zeroEstimateExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E) (I : TimeInterval) (x : ℝ → E), solutionOnValue F I x →
    ∀ (B a : ℝ), 0 ≤ a →
    (∀ r : ℝ, |r| ≤ B → ∀ y : E, ‖F.eval r y‖ ≤ a) →
    ∀ s ∈ I.carrier, ∀ t ∈ I.carrier, |s| ≤ B → |t| ≤ B →
      ‖x t‖ ≤ ‖x s‖ + a * |t - s|

def globalExistenceExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), locallyLipschitzInStateValue F → F.domain = univ →
    (∀ B : ℝ, 0 < B → ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ∀ r : ℝ, |r| ≤ B → ∀ y : E, ‖F.eval r y‖ ≤ a + b * ‖y‖) →
    ∀ x : Solution F, maximalValue x → globalValue x

end Specs.D13Unified.Ch04.LinearGrowth
