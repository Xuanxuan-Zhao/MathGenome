import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalLipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent statements for paper.tex, d13:03:picard.
The field, domain, arbitrary norm, and endpoint-aware solution predicate are
those of Chapter 1. Values of ambient curves outside the displayed intervals
are irrelevant. The additional overlap assertion uses classical local
solutions on their actual open intervals, with no global Lipschitz constant.
-/
noncomputable section
open Set Metric Filter MeasureTheory
open _root_.D13Unified

namespace Specs.D13Unified.Ch03.ControlledPicard
universe u

/-- Exactly the Picard recursion in the source, with oriented integrals. -/
def picardIterate {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (s : ℝ) (ξ : E) : ℕ → ℝ → E
  | 0 => fun _ => ξ
  | j + 1 => fun t => ξ + ∫ r in s..t, F.eval r (picardIterate F s ξ j r)

/-- The closed symmetric interval, using the supplied positivity of `h`. -/
def controlledInterval (s h : ℝ) (hh : 0 < h) : TimeInterval :=
  ⟨Icc (s - h) (s + h), ⟨s, by constructor <;> linarith⟩, ordConnected_Icc⟩

/-- Existence, convergence of the stated iterates, and uniqueness in the whole
controlled box. Nonnegativity of `b` follows from `0 ≤ M`, `0 < h`, `M*h ≤ b`;
no strict positivity of `b`, `M`, or `L` is imposed. -/
def controlledPicardExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (s : ℝ) (ξ : E)
    (a b M L h : ℝ), 0 ≤ M → 0 ≤ L → (hh : 0 < h) →
    h ≤ a → M * h ≤ b → L * h < 1 →
    Icc (s-a) (s+a) ×ˢ closedBall ξ b ⊆ F.domain →
    (∀ t ∈ Icc (s-a) (s+a), ∀ z ∈ closedBall ξ b, ‖F.eval t z‖ ≤ M) →
    LocalLipschitz.stateLipschitzOnValue F.eval (Icc (s-a) (s+a)) (closedBall ξ b) L →
    ∃ x : ℝ → E,
      Ch01.SolutionConcepts.ivpOnValue F (controlledInterval s h hh) x s ξ ∧
      MapsTo x (Icc (s-h) (s+h)) (closedBall ξ b) ∧
      TendstoUniformlyOn (picardIterate F s ξ) x atTop (Icc (s-h) (s+h)) ∧
      (∀ y : ℝ → E,
        Ch01.SolutionConcepts.ivpOnValue F (controlledInterval s h hh) y s ξ →
        MapsTo y (Icc (s-h) (s+h)) (closedBall ξ b) →
        EqOn y x (Icc (s-h) (s+h)))

/-- Agreement throughout the full common interval, to either side of `s`.
The local state estimate is allowed to vary with every time-state center. -/
def overlapUniquenessExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E),
    LocalLipschitz.locallyLipschitzInStateValue F →
    ∀ (I J : OpenTimeInterval) (x y : ℝ → E) (s : ℝ) (ξ : E),
      Ch01.SolutionConcepts.classicalIVPOnValue F I x s ξ →
      Ch01.SolutionConcepts.classicalIVPOnValue F J y s ξ →
      EqOn x y (I.carrier ∩ J.carrier)

end Specs.D13Unified.Ch03.ControlledPicard
