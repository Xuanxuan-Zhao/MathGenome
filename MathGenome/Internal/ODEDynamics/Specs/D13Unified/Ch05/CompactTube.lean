import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalLipschitz

/-! Independent statements for the tube construction in d13:05:common-interval
and its parameter extension in d13:05:openness. Finite-dimensional normed
spaces retain arbitrary fixed norms and allow zero dimensions. -/

noncomputable section
open Set Metric

namespace D13Unified

/-- The closed, constant-radius state tube about a reference curve, restricted
exactly to the indicated compact time interval. -/
def closedTube {E : Type*} [NormedAddCommGroup E]
    (x : ℝ → E) (a b ρ : ℝ) : Set (ℝ × E) :=
  {q | q.1 ∈ Icc a b ∧ ‖q.2 - x q.1‖ ≤ ρ}

end D13Unified

namespace Specs.D13Unified.Ch05.CompactTube
open _root_.D13Unified
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch03.LocalLipschitz
universe u v

/-- The ordinary tube: compactness, actual domain containment, and a uniform
state Lipschitz bound on each full closed state slice. -/
def compactSolutionTubeExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E),
    locallyLipschitzInStateValue F →
    ∀ (I : OpenTimeInterval) (x : ℝ → E), classicalSolutionOnValue F I x →
    ∀ a b : ℝ, a ≤ b → Icc a b ⊆ I.carrier →
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧ IsCompact (closedTube x a b ρ) ∧
      closedTube x a b ρ ⊆ F.domain ∧
      ∀ t ∈ Icc a b, ∀ z ∈ closedBall (x t) ρ, ∀ w ∈ closedBall (x t) ρ,
        ‖F.eval t z - F.eval t w‖ ≤ L * ‖z - w‖

/-- A single positive state radius and parameter radius work over the entire
compact interval. The joint domain retains the association `((t,z),p)`. -/
def compactParameterSolutionTubeExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (F : ParameterODE E P),
    parameterLocallyLipschitzInStateValue F →
    ∀ (p₀ : P) (I : OpenTimeInterval) (x : ℝ → E),
    classicalParameterSolutionOnValue F p₀ I x →
    ∀ a b : ℝ, a ≤ b → Icc a b ⊆ I.carrier →
    ∃ ρ c L : ℝ, 0 < ρ ∧ 0 < c ∧ 0 ≤ L ∧
      IsCompact (closedTube x a b ρ ×ˢ closedBall p₀ c) ∧
      closedTube x a b ρ ×ˢ closedBall p₀ c ⊆ F.domain ∧
      ∀ t ∈ Icc a b, ∀ z ∈ closedBall (x t) ρ, ∀ w ∈ closedBall (x t) ρ,
      ∀ p ∈ closedBall p₀ c,
        ‖parameterEvalValue F t z p - parameterEvalValue F t w p‖ ≤ L * ‖z - w‖

end Specs.D13Unified.Ch05.CompactTube
