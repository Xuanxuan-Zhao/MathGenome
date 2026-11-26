import Mathlib.Algebra.Ring.Associator
import Mathlib.RingTheory.TensorProduct.Basic

open scoped TensorProduct

namespace Specs.LinearAlgebraicGroups.Composition.AlternativeIdentities

universe u v w

def IsAlternativeType := ∀ (A : Type u) [NonUnitalNonAssocRing A], Prop

def isAlternative (A : Type u) [NonUnitalNonAssocRing A] : Prop :=
  ∀ x y : A, associator x x y = 0 ∧ associator y x x = 0

def alternativeIffType : Prop :=
  ∀ {A : Type u} [NonUnitalNonAssocRing A],
    isAlternative A ↔
      ∀ x y z : A, x = y ∨ y = z ∨ x = z → associator x y z = 0

def flexibleType : Prop :=
  ∀ {A : Type u} [NonUnitalNonAssocRing A], isAlternative A →
    ∀ x y : A, (x * y) * x = x * (y * x)

def scalarExtensionType : Prop :=
  ∀ {A : Type u} [NonUnitalNonAssocRing A] {R : Type v} {S : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [Module R A] [SMulCommClass R A A] [IsScalarTower R A A],
    isAlternative A → isAlternative (S ⊗[R] A)

def moufangLeftType : Prop :=
  ∀ {A : Type u} [NonUnitalNonAssocRing A], isAlternative A →
    ∀ x a y : A, ((x * a) * x) * y = x * (a * (x * y))

def moufangRightType : Prop :=
  ∀ {A : Type u} [NonUnitalNonAssocRing A], isAlternative A →
    ∀ x a y : A, y * ((x * a) * x) = ((y * x) * a) * x

def moufangMiddleType : Prop :=
  ∀ {A : Type u} [NonUnitalNonAssocRing A], isAlternative A →
    ∀ x a y : A, (x * y) * (a * x) = (x * (y * a)) * x

end Specs.LinearAlgebraicGroups.Composition.AlternativeIdentities
