import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsSepClosed

open AlgebraicGeometry CategoryTheory

universe u

namespace Specs.LinearAlgebraicGroups.Descent

/-- A nonempty smooth finite-type scheme over a separably closed field has a rational point. -/
def ExistsRationalPointOfSmooth : Prop :=
  ∀ {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f], Nonempty X →
      ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _

/-- Every nonempty open subscheme has a rational point over the same field. -/
def ExistsRationalPointOfSmoothOpen : Prop :=
  ∀ {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
    (U : X.Opens), Nonempty U →
      ∃ s : Spec (CommRingCat.of k) ⟶ U, s ≫ (U.ι ≫ f) = 𝟙 _

end Specs.LinearAlgebraicGroups.Descent
