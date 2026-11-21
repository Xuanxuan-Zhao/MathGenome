import Mathlib.Analysis.Complex.Exponential
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace P203Specs.Ch05

/-- The irrationality of the classical constants in paper.tex, Chapter 5,
section nt:E01, Theorem 5.3. Here e is the real exponential at 1. -/
def ClassicalIrrationals : Prop :=
  Irrational (Real.exp 1) ∧ Irrational Real.pi

end P203Specs.Ch05
