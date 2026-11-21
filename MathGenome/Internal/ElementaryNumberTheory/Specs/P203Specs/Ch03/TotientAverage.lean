import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.ClassicalFunctions
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Filter
open scoped BigOperators Asymptotics

namespace P203Specs.Ch03.TotientAverage

/-- The sum over positive integers at most the real upper limit `x`.
For negative `x` the sum is empty, as is the source's sum. -/
noncomputable def summatory (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (P203Specs.ClassicalFunctions.phi n : ℝ)

/-- The second assertion of Theorem 3.8, with real upper limits and
an absolute big-O error of order `x log x` as `x → +∞`. -/
def TotientAsymptotic : Prop :=
  (fun x : ℝ => summatory x - (3 / Real.pi ^ 2) * x ^ 2)
    =O[atTop] (fun x : ℝ => x * Real.log x)

end P203Specs.Ch03.TotientAverage
