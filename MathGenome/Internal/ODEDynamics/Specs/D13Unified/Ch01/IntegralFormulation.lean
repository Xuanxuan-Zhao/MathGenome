import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Independent statements for paper.tex, Theorem d13:01:integral.
The interval may be bounded or unbounded, with either endpoint convention,
and may be a singleton. Integrals are oriented interval integrals. The
finite-dimensional real normed state space includes every `ℝⁿ` with any norm.
-/

noncomputable section

open Set MeasureTheory
open D13Unified

namespace Specs.D13Unified.Ch01.IntegralFormulation

universe u

/-- Differential and integral formulations on every actual time interval.
`ivpOnValue` includes continuity, graph membership, within derivatives at all
included points, the initial time, and the initial value. -/
def ivpIffIntegralExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (I : TimeInterval)
    (x : ℝ → E) (s : ℝ) (ξ : E),
    s ∈ I.carrier → ContinuousOn x I.carrier →
    (∀ t ∈ I.carrier, (t, x t) ∈ F.domain) →
    (SolutionConcepts.ivpOnValue F I x s ξ ↔
      ∀ t ∈ I.carrier, x t = ξ + ∫ r in s..t, F.eval r (x r))

/-- On an open interval the same identity is equivalent to the shared C¹
classical IVP predicate, including its ordinary derivative equation. -/
def classicalIVPIffIntegralExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (I : OpenTimeInterval)
    (x : ℝ → E) (s : ℝ) (ξ : E),
    s ∈ I.carrier → ContinuousOn x I.carrier →
    (∀ t ∈ I.carrier, (t, x t) ∈ F.domain) →
    (SolutionConcepts.classicalIVPOnValue F I x s ξ ↔
      ∀ t ∈ I.carrier, x t = ξ + ∫ r in s..t, F.eval r (x r))

end Specs.D13Unified.Ch01.IntegralFormulation
