import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! K03.08.thomae, paper.tex:2261–2282. The function is extended by zero
outside [0,1]. Rational numbers in Lean have a positive reduced denominator.
Continuity is relative to the closed unit interval, including both endpoints.
The integral below is the project's bounded Darboux integral. -/
namespace Specs.SingleVariableAnalysis.Ch08.Thomae
open _root_.SingleVariableAnalysis.Riemann
open scoped Topology

abbrev thomaeType := ℝ → ℝ
noncomputable def thomaeValue : thomaeType := by
  classical
  exact fun x =>
  if x ∈ Set.Icc (0 : ℝ) 1 then
    if h : ∃ q : ℚ, (q : ℝ) = x then 1 / ((Classical.choose h).den : ℝ) else 0
  else 0

abbrev lowDenominatorsType := ℕ → Set ℝ
def lowDenominatorsValue : lowDenominatorsType := fun N =>
  {x | ∃ q : ℚ, (q : ℝ) = x ∧ x ∈ Set.Icc (0 : ℝ) 1 ∧ q.den ≤ N}

def rationalValue : Prop := ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 →
  thomaeValue q = 1 / (q.den : ℝ)
def irrationalValue : Prop := ∀ x : ℝ, Irrational x → thomaeValue x = 0
def bounded : Prop := DarbouxSums.boundedOnIntervalValue thomaeValue 0 1
def finiteLowDenominators : Prop := ∀ N, (lowDenominatorsValue N).Finite
/-- The finite exceptional set controls every remaining value. -/
def outsideLowDenominators : Prop := ∀ N : ℕ, 0 < N → ∀ x ∈ Set.Icc (0 : ℝ) 1,
  x ∉ lowDenominatorsValue N → 0 ≤ thomaeValue x ∧ thomaeValue x ≤ 1 / (N : ℝ)
def continuousIrrational : Prop := ∀ x ∈ Set.Icc (0 : ℝ) 1, Irrational x →
  ContinuousWithinAt thomaeValue (Set.Icc (0 : ℝ) 1) x
def discontinuousRational : Prop := ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 →
  ¬ ContinuousWithinAt thomaeValue (Set.Icc (0 : ℝ) 1) q

def lowerSumsZero : Prop := ∀ (P : PartitionData 0 1)
  (hf : DarbouxSums.boundedOnIntervalValue thomaeValue 0 1),
  DarbouxSums.lowerSumValue thomaeValue P hf = 0
/-- Direct small upper sums, without a discontinuity-set criterion. -/
def smallUpperSums : Prop := ∀ (hf : DarbouxSums.boundedOnIntervalValue thomaeValue 0 1)
  (ε : ℝ), 0 < ε → ∃ P : PartitionData 0 1,
  DarbouxSums.upperSumValue thomaeValue P hf < ε

def integrable : Prop := Integral.realIntegrableValue thomaeValue 0 1
def integralZero : Prop := ∀ h : Integral.realIntegrableValue thomaeValue 0 1,
  Integral.realIntegralValue thomaeValue h = 0
end Specs.SingleVariableAnalysis.Ch08.Thomae
