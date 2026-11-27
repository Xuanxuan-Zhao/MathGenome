import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.TowerExactSequence

namespace Specs.DerivedFormalization.TowerKInjectivity

open CategoryTheory CategoryTheory.Limits Opposite
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels (isKInjectiveValue)
open Specs.DerivedFormalization.TowerExactSequence (transition)

universe u v

/-- A countable inverse limit of K-injective complexes is K-injective if the
successor maps admit module-linear sections in every degree. -/
def limitKInjectiveType : Prop :=
  ∀ (R : Type u) [CommRing R] (A : ℕᵒᵖ ⥤ compValue.{v} R),
    (∀ (n : ℕ) (i : ℤ), ∃ s : (A.obj (op n)).X i ⟶ (A.obj (op (n + 1))).X i,
      s ≫ (transition A n).f i = 𝟙 _) →
    (∀ n : ℕ, isKInjectiveValue (A.obj (op n))) →
    isKInjectiveValue (limit A)

end Specs.DerivedFormalization.TowerKInjectivity
