import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.KProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone
import Mathlib.CategoryTheory.Limits.Shapes.Products

open CategoryTheory CategoryTheory.Limits

universe u v w j

namespace Specs.DerivedFormalization.DG.KProjectiveClosure

open _root_.DerivedFormalization

/-- Signed integer shifts preserve K-projectivity. -/
def Shift : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} (s : ℤ),
    KProjective.isKProjective P → KProjective.isKProjective (ShiftCone.shift P s)

/-- The cone of a strict map between K-projective modules is K-projective. -/
def Cone : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P Q : RightDGModuleModel A} (f : P ⟶ Q),
    KProjective.isKProjective P → KProjective.isKProjective Q →
      KProjective.isKProjective (ShiftCone.cone f)

/-- The vertex of any strict coproduct of K-projective modules is K-projective. -/
def Coproduct : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} {P : I → RightDGModuleModel A} (c : Cofan P),
    IsColimit c → (∀ i, KProjective.isKProjective (P i)) → KProjective.isKProjective c.pt

end Specs.DerivedFormalization.DG.KProjectiveClosure
