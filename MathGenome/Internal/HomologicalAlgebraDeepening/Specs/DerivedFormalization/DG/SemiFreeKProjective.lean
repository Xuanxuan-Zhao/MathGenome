import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.KProjectiveClosure

universe u v w j

namespace Specs.DerivedFormalization.DG.SemiFreeKProjective

open _root_.DerivedFormalization

/-- Every right dg module with an exhaustive semi-free presentation is
K-projective, over any small dg category over a commutative ring. -/
def SemiFreeIsKProjective : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A},
    IndexedSemiFree.semiFree P → KProjective.isKProjective P

/-- The presentation may have a cell-index universe independent of the given module. -/
def IndexedSemiFreeIsKProjective : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A},
    IndexedSemiFree.Presentation.{u,v,w,j} P → KProjective.isKProjective P

/-- K-projective modules are closed under integer shifts, cones of strict
maps between them, and any existing strict coproduct with an arbitrary index type. -/
def Closure : Prop :=
  KProjectiveClosure.Shift.{u,v,w} ∧ KProjectiveClosure.Cone.{u,v,w} ∧
    KProjectiveClosure.Coproduct.{u,v,w,j}

end Specs.DerivedFormalization.DG.SemiFreeKProjective
