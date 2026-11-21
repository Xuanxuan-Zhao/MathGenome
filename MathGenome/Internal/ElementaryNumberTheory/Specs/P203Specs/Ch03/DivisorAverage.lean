import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.ClassicalFunctions
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Hyperbola
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.HarmonicBasel

open Filter
open scoped Asymptotics

namespace P203Specs.Ch03.DivisorAverage

/-- The first assertion of Theorem 3.8 (`nt:C07`), paper.tex:1146–1164.
The summatory function uses positive integer indices at a real cutoff.
The constant gamma is the same one as in the harmonic-number theorem. -/
def Asymptotic : Prop :=
  (fun x : ℝ =>
    P203Specs.summatory
      (P203Specs.restrictPositive (P203Specs.ClassicalFunctions.tau : ArithmeticFunction ℝ)) x -
    (x * Real.log x + (2 * P203Specs.Ch03.gamma - 1) * x))
    =O[atTop] (fun x : ℝ => Real.sqrt x)

end P203Specs.Ch03.DivisorAverage
