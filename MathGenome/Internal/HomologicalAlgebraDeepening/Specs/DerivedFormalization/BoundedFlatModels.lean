import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import Mathlib.RingTheory.Flat.Basic

/-! Specification of the bounded-above flat assertion in U03. -/

namespace Specs.DerivedFormalization.BoundedFlatModels

open CategoryTheory CategoryTheory.Limits
open Cochains (compValue)
open CochainModels (isKFlatValue)

universe u

/-- A bounded-above cochain complex with flat terms is K-flat. -/
def boundedAboveFlatIsKFlatType : Prop :=
  ∀ (R : Type u) [CommRing R] (F : compValue.{u} R),
    (∀ q : ℤ, Module.Flat R (F.X q)) →
    (∃ N : ℤ, ∀ q : ℤ, N < q → IsZero (F.X q)) →
    isKFlatValue F

end Specs.DerivedFormalization.BoundedFlatModels
