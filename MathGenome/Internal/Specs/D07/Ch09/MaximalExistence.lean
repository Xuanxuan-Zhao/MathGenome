import MathGenome.Internal.Specs.D07.Ch09.MaximalIdeal

/-!
Independent specification for K07.09.maximal_existence,
paper.tex:1685–1698. Commutativity is the standing hypothesis from
paper.tex:1631 through the end of the chapter. The zero ring is allowed:
the assertion is conditional on the given ideal being proper.
-/

universe u

namespace Specs.D07.Ch09.MaximalExistence

/-- Every proper ideal of a commutative unital ring is contained in a
maximal ideal. This is an existence assertion, with no algorithmic data. -/
def MaximalExistence : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R), I ≠ ⊤ →
    ∃ M : Ideal R, I ≤ M ∧
      Specs.D07.Ch09.MaximalIdeal.maximalPredicateValue M

end Specs.D07.Ch09.MaximalExistence
