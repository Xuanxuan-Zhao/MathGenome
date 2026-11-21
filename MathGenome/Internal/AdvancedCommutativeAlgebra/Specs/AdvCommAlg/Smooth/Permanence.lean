import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import Mathlib.RingTheory.Localization.Away.Basic

/-! Independent statements for SM-06, paper.tex:1075–1095.
The structural maps in each tower are compatible. Base change is arbitrary,
and no nontriviality hypothesis is imposed on any ring or localization.
-/
namespace Specs.AdvCommAlg.Smooth.Permanence

universe u v w

open scoped TensorProduct

/-- Smoothness is preserved by compatible composition. -/
def smoothComposition : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    smoothValue A B → smoothValue B C → smoothValue A C

/-- Smoothness is preserved by extension along every base-ring map. -/
def smoothBaseChange : Prop :=
  ∀ (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'],
    smoothValue A B → smoothValue A' (A' ⊗[A] B)

/-- Every principal localization of a smooth algebra is smooth over the base. -/
def smoothTargetLocalization : Prop :=
  ∀ (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [CommRing B] [CommRing L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    (g : B) [IsLocalization.Away g L],
    smoothValue A B → smoothValue A L

/-- If the image of a base element is a unit, smoothness persists over the
principal localization of the base, with its induced structural map. -/
def smoothSourceLocalization : Prop :=
  ∀ (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]
    (a : A) [IsLocalization.Away a L] (ha : IsUnit (algebraMap A B a)),
    letI : Algebra L B := (IsLocalization.Away.lift (S := L) a ha).toAlgebra
    smoothValue A B → smoothValue L B

end Specs.AdvCommAlg.Smooth.Permanence
