import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.ExactOperations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent

open CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.Unipotent

/-- The group scheme is isomorphic to the trivial group over the ground field. -/
def UnipotentMultiplicativeTypeTrivial : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsUnipotent G → (CharacterDescent.multiplicativeTypeSpecFunctor k).essImage G →
    IsZero G.val

/-- A homomorphism from a unipotent group to a group of multiplicative type
is the identity-section homomorphism. -/
def HomFromUnipotentToMultiplicativeType : Prop :=
  ∀ {k : Type u} [Field k] (U D : AffineAlgebraicGroup k) (f : U.val ⟶ D.val),
    IsUnipotent U → (CharacterDescent.multiplicativeTypeSpecFunctor k).essImage D →
    f = 0

/-- A homomorphism from a group of multiplicative type to a unipotent group
is the identity-section homomorphism. -/
def HomFromMultiplicativeTypeToUnipotent : Prop :=
  ∀ {k : Type u} [Field k] (D U : AffineAlgebraicGroup k) (f : D.val ⟶ U.val),
    (CharacterDescent.multiplicativeTypeSpecFunctor k).essImage D → IsUnipotent U →
    f = 0

/-- A scheme-theoretic intersection of a closed unipotent subgroup and a closed
subgroup of multiplicative type is trivial. -/
def UnipotentMultiplicativeTypeIntersection : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (U D : ClosedSubgroup G.val)
    {P : GroupScheme k} (p : P ⟶ U.group) (q : P ⟶ D.group),
    IsPullback p q U.inclusion D.inclusion →
    IsUnipotent (closedSubgroupAlgebraicGroup U) →
    (CharacterDescent.multiplicativeTypeSpecFunctor k).essImage (closedSubgroupAlgebraicGroup D) →
    IsZero P

end LinearAlgebraicGroups.Specs.Unipotent
