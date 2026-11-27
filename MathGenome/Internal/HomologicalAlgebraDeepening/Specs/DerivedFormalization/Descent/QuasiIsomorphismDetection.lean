import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.RingTheory.RingHom.FaithfullyFlat

open CategoryTheory

universe uA uB v

namespace DerivedFormalization.Descent

/-- Scalar extension is additive, including when the input module universe is
smaller than the target ring universe. -/
scoped instance extendScalarsAdditive {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    (ι : A →+* B) : (ModuleCat.extendScalars.{uA, uB, v} ι).Additive where
  map_add {M N} g h := by
    let : Algebra A B := ι.toAlgebra
    exact ModuleCat.hom_ext (LinearMap.baseChange_add (A := B) g.hom h.hom)

end DerivedFormalization.Descent

open scoped DerivedFormalization.Descent

namespace Specs.DerivedFormalization.Descent

/-- Faithfully flat scalar extension detects quasi-isomorphisms of unbounded
integer-graded cochain complexes. The tensor products have universe `max uB v`. -/
def QuasiIsoIffExtendScalars : Prop :=
  ∀ {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    (ι : A →+* B), ι.FaithfullyFlat →
    ∀ {X Y : CochainComplex (ModuleCat.{v} A) ℤ} (f : X ⟶ Y),
      QuasiIso f ↔ QuasiIso (((ModuleCat.extendScalars.{uA, uB, v} ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)

end Specs.DerivedFormalization.Descent
