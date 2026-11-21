import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalExistenceUniqueness
import Mathlib.Data.EReal.Basic

/-! Independent statements for paper.tex, d13:04:maximal.
Uniqueness is equality of actual domains and values there; ambient representatives
may differ away from their domains. No solution map is assumed or chosen here. -/
noncomputable section
open Set
open D13Unified
open Specs.D13Unified.Ch01.SolutionConcepts

namespace Specs.D13Unified.Ch04.MaximalSolution
universe u v

/-- The complete maximal-solution conclusion at one datum. The universal
restriction clause records every competing solution's own open interval. -/
def MaximalThrough {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (s : ℝ) (ξ : E) : Prop :=
  ∃ x : Solution F,
    s ∈ x.interval.carrier ∧ x.representative s = ξ ∧ maximalValue x ∧
    (∃ a b : EReal, a < (s : EReal) ∧ (s : EReal) < b ∧
      x.interval.carrier = {t : ℝ | a < (t : EReal) ∧ (t : EReal) < b}) ∧
    (∀ (J : OpenTimeInterval) (y : ℝ → E), classicalIVPOnValue F J y s ξ →
      J.carrier ⊆ x.interval.carrier ∧ EqOn x.representative y J.carrier) ∧
    (∀ y : Solution F, s ∈ y.interval.carrier → y.representative s = ξ →
      maximalValue y → y.interval.carrier = x.interval.carrier ∧
        EqOn y.representative x.representative y.interval.carrier)

def maximalSolutionExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E),
    Ch03.LocalLipschitz.locallyLipschitzInStateValue F →
    ∀ (s : ℝ) (ξ : E), (s, ξ) ∈ F.domain → MaximalThrough F s ξ

/-- Fixing p uses precisely the time-state slice of the original open triple
domain. Continuity is joint, and the state Lipschitz bound is locally uniform
also in parameters, as in the chapter's standing hypotheses. -/
def parameterMaximalSolutionExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (F : ParameterODE E P),
    Ch03.LocalLipschitz.parameterLocallyLipschitzInStateValue F →
    ∀ (p : P) (s : ℝ) (ξ : E), ((s, ξ), p) ∈ F.domain →
      MaximalThrough (Ch01.AutonomousParameters.atParameterValue F p) s ξ

end Specs.D13Unified.Ch04.MaximalSolution
