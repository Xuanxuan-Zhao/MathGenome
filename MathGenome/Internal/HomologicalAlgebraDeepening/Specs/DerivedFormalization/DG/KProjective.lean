import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomComplex

universe u v w

namespace Specs.DerivedFormalization.DG.KProjective

open _root_.DerivedFormalization

set_option linter.checkUnivs false in
def IsKProjectiveType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    RightDGModuleModel A → Prop

/-- The Hom complex out of a K-projective module is acyclic for every
objectwise acyclic right dg module. -/
def isKProjective {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (P : RightDGModuleModel A) : Prop :=
  ∀ N : RightDGModuleModel A,
    (∀ a, (N.complex a).Acyclic) → (HomComplex.homComplex P N).Acyclic

end Specs.DerivedFormalization.DG.KProjective
