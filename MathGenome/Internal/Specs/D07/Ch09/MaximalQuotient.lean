import MathGenome.Internal.Specs.D07.Ch09.MaximalIdeal
import Mathlib.Algebra.Field.IsField
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
Independent specifications for K07.09.maximal_quotient,
paper.tex:1660–1672. The commutative convention starts at paper.tex:1631.
The ambient ring may be the zero ring and the ideal need not be proper
in advance: both properties are decided by the equivalence.

`IsField` refers to the canonical quotient operations, includes
nontriviality, and requires every nonzero element to have an inverse.
The second formulation explicitly supplies a field structure retaining
the entire canonical ring structure. Neither formulation merely asks
for an unrelated field structure on the quotient's underlying type.
-/

universe u

namespace Specs.D07.Ch09.MaximalQuotient

/-- An ideal is maximal exactly when its canonical quotient is a field. -/
def MaximalIffIsFieldQuotient : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Ideal R),
    MaximalIdeal.maximalPredicateValue M ↔ IsField (R ⧸ M)

/-- The field operations extend precisely the given quotient-ring operations. -/
def MaximalIffFieldStructure : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Ideal R),
    MaximalIdeal.maximalPredicateValue M ↔
      ∃ f : Field (R ⧸ M), f.toRing = (inferInstance : Ring (R ⧸ M))

end Specs.D07.Ch09.MaximalQuotient
