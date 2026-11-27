import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Yoneda
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CoefficientLift

open CategoryTheory

universe u v w t

namespace DerivedFormalization.DG.CoefficientLift

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

/-- Lift the arrow complexes along `ULift`, keeping the objects and the base ring. -/
abbrev liftCategory (A : DGCategory.{u,v,w} k) : DGCategory.{u,max v t,w} k :=
  Specs.DerivedFormalization.DG.CoefficientLift.liftCategory.{u,v,w,t} A

/-- Lift the module complexes degreewise, transporting the right action along
the same linear equivalences as for the arrows. -/
abbrev liftModule (M : RightDGModule A) :
    RightDGModule (liftCategory.{u,v,w,t} A) :=
  Specs.DerivedFormalization.DG.CoefficientLift.liftModule.{u,v,w,t} M

/-- Conjugate the components of a strict module map by the degreewise lift. -/
abbrev liftMap {M N : RightDGModule A} (f : M ⟶ N) :
    liftModule.{u,v,w,t} M ⟶ liftModule.{u,v,w,t} N :=
  Specs.DerivedFormalization.DG.CoefficientLift.liftMap.{u,v,w,t} f

/-- Coefficient enlargement on right dg modules and their strict maps. -/
abbrev liftFunctor (A : DGCategory.{u,v,w} k) :
    RightDGModule A ⥤ RightDGModule (liftCategory.{u,v,w,t} A) :=
  Specs.DerivedFormalization.DG.CoefficientLift.liftFunctor.{u,v,w,t} A

end DerivedFormalization.DG.CoefficientLift
