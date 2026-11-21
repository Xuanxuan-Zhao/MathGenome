import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticContinuedFractions

/-! The necessity stage of paper.tex, Theorem nt:E08 (lines 2462–2494).
Periodicity refers to the actual canonical digits, and conjugation to the
minimal polynomial over ℚ, as in the shared definitions. -/
namespace P203Specs

/-- A purely periodic irrational is quadratic, with its other root in (-1,0). -/
def PurelyPeriodicQuadraticReduced : Prop :=
  ∀ y : ℝ, Irrational y → PurelyPeriodicCF y →
    QuadraticIrrational y ∧ ReducedQuadratic y

/-- Eventual periodicity, including a period beginning at zero, forces degree two. -/
def EventuallyPeriodicQuadratic : Prop :=
  ∀ x : ℝ, Irrational x → EventuallyPeriodicCF x → QuadraticIrrational x

end P203Specs
