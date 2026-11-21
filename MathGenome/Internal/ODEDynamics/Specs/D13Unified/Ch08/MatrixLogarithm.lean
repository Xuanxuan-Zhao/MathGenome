import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.MatrixExponential

namespace Specs.D13Unified.Ch08.MatrixLogarithm

/-- Every finite invertible complex matrix has a complex logarithm, using the
actual convergent exponential fixed in Chapter 7. -/
def logarithmType : Prop :=
  ∀ {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ),
    IsUnit M → ∃ L : Matrix n n ℂ,
      Specs.D13Unified.Ch07.MatrixExponential.exponentialValue L 1 = M

end Specs.D13Unified.Ch08.MatrixLogarithm
