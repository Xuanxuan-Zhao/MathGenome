import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! Localization, finite-type base change, composition and faithfully flat
descent of regular homomorphisms in Lemma 5.11. -/

universe u v w x

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence.Specs

/-- Localize the target at an arbitrary multiplicative set. -/
def regularMap_localizationTargetType : Prop :=
  ∀ (A : Type u) (B : Type v) (B' : Type w)
    [CommRing A] [CommRing B] [CommRing B']
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [Algebra B B'] [Algebra A B'] [IsScalarTower A B B']
    (N : Submonoid B) [IsLocalization N B'],
    RegularMapValue A B (algebraMap A B) →
      letI : IsNoetherianRing B' := IsLocalization.isNoetherianRing N B' inferInstance
      RegularMapValue A B' (algebraMap A B')

/-- Localize both source and target, where the induced map exists. The
scalar towers express compatibility of the induced map. -/
def regularMap_localizationType : Prop :=
  ∀ (A : Type u) (B : Type v) (A' : Type w) (B' : Type x)
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    (M : Submonoid A) (N : Submonoid B) [IsLocalization M A'] [IsLocalization N B'],
    RegularMapValue A B (algebraMap A B) →
      letI : IsNoetherianRing A' := IsLocalization.isNoetherianRing M A' inferInstance
      letI : IsNoetherianRing B' := IsLocalization.isNoetherianRing N B' inferInstance
      RegularMapValue A' B' (algebraMap A' B')

/-- In a pushout square, the horizontal regular map remains regular when the
change of base is of finite type. -/
def regularMap_baseChangeType : Prop :=
  ∀ (A : Type u) (B : Type v) (A' : Type w) (B' : Type x)
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A A' B B']
    [Algebra.FiniteType A A'],
    RegularMapValue A B (algebraMap A B) →
      letI : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
      letI : Algebra.IsPushout A B A' B' :=
        Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout A A' B B')
      letI : IsNoetherianRing (B ⊗[A] A') := Algebra.FiniteType.isNoetherianRing B _
      letI : IsNoetherianRing B' :=
        isNoetherianRing_of_ringEquiv _ (Algebra.IsPushout.equiv A B A' B').toRingEquiv
      RegularMapValue A' B' (algebraMap A' B')

def regularMap_compType : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w) [CommRing A] [CommRing B] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (f : A →+* B) (g : B →+* C),
    RegularMapValue A B f → RegularMapValue B C g → RegularMapValue A C (g.comp f)

def regularMap_of_comp_faithfullyFlatType : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w) [CommRing A] [CommRing B] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (f : A →+* B) (g : B →+* C),
    RegularMapValue A C (g.comp f) → g.FaithfullyFlat → RegularMapValue A B f

end CommutativeAlgebraNotes.Excellence.Specs
