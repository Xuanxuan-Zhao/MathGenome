import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.ClassicalFunctions
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The third assertion of paper.tex, Theorem 3.8 (1146–1151).
The cutoff is real; only positive natural indices enter the finite sum.
The square is taken in ℤ before mapping the coefficient to ℝ. -/
namespace P203Specs.Ch03.SquarefreeAverage

open P203Specs.ClassicalFunctions

noncomputable def squarefreeSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((mu n ^ 2 : ℤ) : ℝ)

def SquarefreeAsymptotic : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ => squarefreeSum x - (6 / Real.pi ^ 2) * x)
    (fun x : ℝ => Real.sqrt x)

end P203Specs.Ch03.SquarefreeAverage
