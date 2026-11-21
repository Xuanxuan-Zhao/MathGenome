import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions

/-! Independent statements for the permanence part of ET-04,
paper.tex:1595–1597 and 1609–1619. All rings are commutative and unital;
zero rings are allowed. Base change is A' ⊗[A] B with its left A'-action.
Principal localization includes localization at zero.
-/
namespace Specs.AdvCommAlg.Etale.Permanence

universe u v w

open scoped TensorProduct

/-- Étaleness is preserved by arbitrary extension of the base ring. -/
def etaleBaseChange : Prop :=
  ∀ (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'],
    etaleValue A B → etaleValue A' (A' ⊗[A] B)

/-- Étaleness is preserved by composition with compatible structural maps. -/
def etaleComposition : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    etaleValue A B → etaleValue B C → etaleValue A C

/-- Any model of the principal localization of an étale algebra is étale. -/
def etaleTargetLocalization : Prop :=
  ∀ (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [CommRing B] [CommRing L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    (b : B) [IsLocalization.Away b L],
    etaleValue A B → etaleValue A L

/-- In particular, the canonical localization B_b is étale for every b. -/
def etaleLocalizationAway : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (b : B), etaleValue A B → etaleValue A (Localization.Away b)

end Specs.AdvCommAlg.Etale.Permanence
