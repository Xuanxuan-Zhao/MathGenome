import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsAlgebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed

/-! K03.15.rs_jump (paper.tex:3748–3764).
A finite step function is specified by its strictly ordered nodes, its value on
each open cell, and its unrestricted actual node values. The hypotheses below
require continuity separately for each nonzero incident increment, even if the
two increments at an interior node cancel. Continuity is relative to the closed
original interval, including the available endpoint sides. The cell constants
are precisely the one-sided limits of the step function. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsJump
open scoped BigOperators
open RsSums

def stepIntegral : Prop :=
  ∀ {K : Type} [RCLike K] (n : ℕ) (x : Fin (n+2) → ℝ)
    (_hx : StrictMono x) (v : Fin (n+1) → ℝ) (α : ℝ → ℝ) (f : ℝ → K),
    (∀ i : Fin (n+1), ∀ y ∈ Set.Ioo (x i.castSucc) (x i.succ), α y = v i) →
    boundedOnValue (x 0) (x (Fin.last (n+1))) f →
    (∀ i : Fin (n+1),
      (v i - α (x i.castSucc) ≠ 0 →
        ContinuousWithinAt f (Set.Icc (x 0) (x (Fin.last (n+1)))) (x i.castSucc)) ∧
      (α (x i.succ) - v i ≠ 0 →
        ContinuousWithinAt f (Set.Icc (x 0) (x (Fin.last (n+1)))) (x i.succ))) →
    integralValue (x 0) (x (Fin.last (n+1))) f α
      ((v 0 - α (x 0)) • f (x 0) +
        (∑ i : Fin n, (v i.succ - v i.castSucc) • f (x i.succ.castSucc)) +
        (α (x (Fin.last (n+1))) - v (Fin.last n)) • f (x (Fin.last (n+1))))

/-- Right-continuous atoms lie at interior nodes or at b. -/
def rightContinuousAtom : Prop :=
  ∀ {K : Type} [RCLike K] (a b c : ℝ) (f : ℝ → K),
    a < c → c ≤ b → boundedOnValue a b f →
    ContinuousWithinAt f (Set.Icc a b) c →
    integralValue a b f (fun y => if c ≤ y then 1 else 0) (f c)

/-- A value already present at the initial endpoint has no increment there. -/
def initialValueNoAtom : Prop :=
  ∀ {K : Type} [RCLike K] (a b : ℝ) (f : ℝ → K),
    a ≤ b → boundedOnValue a b f →
    integralValue a b f (fun y => if a ≤ y then 1 else 0) 0

/-- The open-cell constants used in the formula are the actual one-sided limits. -/
def cellLimits : Prop :=
  ∀ (a b v : ℝ) (α : ℝ → ℝ), a < b →
    (∀ y ∈ Set.Ioo a b, α y = v) →
    Filter.Tendsto α (nhdsWithin a (Set.Ioi a)) (nhds v) ∧
    Filter.Tendsto α (nhdsWithin b (Set.Iio b)) (nhds v)

/-- The source's spike example: zero net interior jump does not imply existence. -/
def zeroNetObstruction : Prop :=
  ∀ (a b c : ℝ), a < c → c < b →
    ¬ ∃ I : ℝ, integralValue a b (fun y => if y = c then 1 else 0)
      (fun y => if y = c then 1 else 0) I

end Specs.SingleVariableAnalysis.Ch15.RsJump
