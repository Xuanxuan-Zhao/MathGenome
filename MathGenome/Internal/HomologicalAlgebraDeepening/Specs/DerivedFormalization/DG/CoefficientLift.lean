import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Yoneda

open CategoryTheory

universe u v w t

namespace Specs.DerivedFormalization.DG.CoefficientLift

open _root_.DerivedFormalization

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

set_option linter.checkUnivs false in
def LiftCategoryType :=
  ∀ {k : Type u} [CommRing k],
    DGCategoryModel.{u,v,w} k → DGCategoryModel.{u,max v t,w} k

/-- Enlarge the morphism complexes while retaining the objects and transporting composition. -/
@[reducible] def liftCategory (A : DGCategoryModel.{u,v,w} k) :
    DGCategoryModel.{u,max v t,w} k where
  Obj := A.Obj
  toData :=
    { hom := fun a b => Yoneda.liftComplex.{u,v,t} (A.hom a b)
      comp := fun i j n h =>
        ((A.comp i j n h).compl₁₂ ULift.moduleEquiv.toLinearMap ULift.moduleEquiv.toLinearMap)
          |>.compr₂ ULift.moduleEquiv.symm.toLinearMap
      id := fun a => ULift.up (A.id a)
      d_id := fun a => ULift.ext (A.toData.d_id a)
      id_comp := fun i f => ULift.ext (A.toData.id_comp i f.down)
      comp_id := fun i f => ULift.ext (A.toData.comp_id i f.down)
      assoc := fun i j l f g h => ULift.ext (A.toData.assoc i j l f.down g.down h.down)
      leibniz := fun i j n e f g => ULift.ext (A.toData.leibniz i j n e f.down g.down) }

set_option linter.checkUnivs false in
def LiftModuleType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    RightDGModuleModel A → RightDGModuleModel (liftCategory.{u,v,w,t} A)

/-- Enlarge a module's complexes over the transported action with the same elements. -/
@[reducible] def liftModule (M : RightDGModuleModel A) :
    RightDGModuleModel (liftCategory.{u,v,w,t} A) where
  complex a := Yoneda.liftComplex.{u,v,t} (M.complex a)
  act i j n h :=
    ((M.act i j n h).compl₁₂ ULift.moduleEquiv.toLinearMap ULift.moduleEquiv.toLinearMap)
      |>.compr₂ ULift.moduleEquiv.symm.toLinearMap
  act_id a i x := ULift.ext (M.act_id a i x.down)
  act_assoc i j l x f g := ULift.ext (M.act_assoc i j l x.down f.down g.down)
  leibniz i j n h x f := ULift.ext (M.leibniz i j n h x.down f.down)

private abbrev complexLift (k : Type u) [CommRing k] :
    ModuleCochain.{u,v} k ⥤ ModuleCochain.{u,max v t} k :=
  (ModuleCat.uliftFunctor.{t,v} k).mapHomologicalComplex (ComplexShape.up ℤ)

set_option linter.checkUnivs false in
def LiftMapType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A},
    (M ⟶ N) → (liftModule.{u,v,w,t} M ⟶ liftModule.{u,v,w,t} N)

/-- Transport a strict module map along the degreewise linear equivalences. -/
@[reducible] def liftMap {M N : RightDGModuleModel A} (f : M ⟶ N) :
    liftModule.{u,v,w,t} M ⟶ liftModule.{u,v,w,t} N where
  app a := (complexLift.{u,v,t} k).map (f.app a)
  comm_act i j n h x g := ULift.ext (f.comm_act i j n h x.down g.down)

set_option linter.checkUnivs false in
def LiftFunctorType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    RightDGModuleModel A ⥤ RightDGModuleModel (liftCategory.{u,v,w,t} A)

/-- Coefficient enlargement on the category of right dg modules and strict maps. -/
@[reducible] def liftFunctor (A : DGCategoryModel.{u,v,w} k) :
    RightDGModuleModel A ⥤ RightDGModuleModel (liftCategory.{u,v,w,t} A) where
  obj M := liftModule.{u,v,w,t} M
  map f := liftMap.{u,v,w,t} f
  map_id M := RightDGModuleModel.hom_ext fun a =>
    (complexLift.{u,v,t} k).map_id (M.complex a)
  map_comp f g := RightDGModuleModel.hom_ext fun a =>
    (complexLift.{u,v,t} k).map_comp (f.app a) (g.app a)

end Specs.DerivedFormalization.DG.CoefficientLift
