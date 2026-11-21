import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.TentContinuity
import Mathlib.Order.Interval.Set.UnorderedInterval

/-! The signed half-cell increments and all quotient estimates in the proof of
K03.16.nowhere_differentiable, paper.tex:3973–3996. Natural exponents encode the
integer indices m ≥ 1; division by 4^m is the displayed negative power.
The tent and series below are exactly the upstream canonical objects. -/

namespace Specs.SingleVariableAnalysis.Ch16.TentQuotients

open TentContinuity

noncomputable def gamma (n : ℕ) (x h : ℝ) : ℝ :=
  (periodicTentValue ((4 : ℝ) ^ n * (x + h)) -
    periodicTentValue ((4 : ℝ) ^ n * x)) / h

def halfCellQuotients : Prop :=
  ∀ (x : ℝ) (m : ℕ), 1 ≤ m → ∃ h : ℝ,
    (h = (1 / 2 : ℝ) / 4 ^ m ∨ h = -((1 / 2 : ℝ) / 4 ^ m)) ∧
    h ≠ 0 ∧
    (∀ k : ℤ, (k : ℝ) ∉ Set.uIoo ((4 : ℝ) ^ m * x)
      ((4 : ℝ) ^ m * (x + h))) ∧
    |gamma m x h| = (4 : ℝ) ^ m ∧
    (∀ n : ℕ, n < m → |gamma n x h| ≤ (4 : ℝ) ^ n) ∧
    (∀ n : ℕ, m < n → gamma n x h = 0) ∧
    (tentSeriesValue (x + h) - tentSeriesValue x) / h =
      ∑ n ∈ Finset.range (m + 1), (3 / 4 : ℝ) ^ n * gamma n x h ∧
    ((3 : ℝ) ^ m + 1) / 2 ≤
      |(tentSeriesValue (x + h) - tentSeriesValue x) / h|

end Specs.SingleVariableAnalysis.Ch16.TentQuotients
