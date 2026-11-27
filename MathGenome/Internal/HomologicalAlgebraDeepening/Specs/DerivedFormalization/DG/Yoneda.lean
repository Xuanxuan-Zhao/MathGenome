import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Ulift

open CategoryTheory

universe u v w w'

namespace Specs.DerivedFormalization.DG.Yoneda

open _root_.DerivedFormalization
open HomComplex (component dgModuleCategory gradedHom homComplex)

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

/-- The right module represented by an object, with action given by composition. -/
@[reducible] def representable (a : A.Obj) : RightDGModuleModel A where
  complex b := A.hom b a
  act i j n h := A.comp i j n h
  act_id _ := A.toData.comp_id
  act_assoc := A.toData.assoc
  leibniz := A.toData.leibniz

set_option linter.checkUnivs false in
def RepresentableType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}, A.Obj → RightDGModuleModel A

/-- Regard a complex in a larger universe, with the same underlying elements via `ULift`. -/
abbrev liftComplex (C : ModuleCochain.{u,v} k) : ModuleCochain.{u,max v w'} k :=
  ((ModuleCat.uliftFunctor.{w'} k).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

/-- Realize the source of Yoneda in the Hom universe of the dg category of modules. -/
@[reducible] def liftCategory (A : DGCategoryModel.{u,v,w} k) :
    DGCategoryModel.{u,max v w,w} k where
  Obj := A.Obj
  toData :=
    { hom := fun a b => liftComplex.{u,v,w} (A.hom a b)
      comp := fun i j n h =>
        ((A.comp i j n h).compl₁₂ ULift.moduleEquiv.toLinearMap ULift.moduleEquiv.toLinearMap)
          |>.compr₂ ULift.moduleEquiv.symm.toLinearMap
      id := fun a => ULift.up (A.id a)
      d_id := fun a => ULift.ext (A.toData.d_id a)
      id_comp := fun i f => ULift.ext (A.toData.id_comp i f.down)
      comp_id := fun i f => ULift.ext (A.toData.comp_id i f.down)
      assoc := fun i j l f g h => ULift.ext (A.toData.assoc i j l f.down g.down h.down)
      leibniz := fun i j n e f g => ULift.ext (A.toData.leibniz i j n e f.down g.down) }

/-- The evaluation isomorphisms, in a common Hom universe. -/
abbrev EvaluationFamily (A : DGCategoryModel.{u,v,w} k) :=
  ∀ (a : A.Obj) (M : RightDGModuleModel A),
    homComplex (representable a) M ≅ liftComplex.{u,v,w} (M.complex a)

/-- Evaluation and its inverse on all homogeneous elements, including enriched naturality. -/
structure EvaluationLaws (E : EvaluationFamily A) : Prop where
  evaluation (a : A.Obj) (M : RightDGModuleModel A) (r : ℤ)
      (f : gradedHom (representable a) M r) :
    ((E a M).hom.f r f).down = component f a 0 r (zero_add r) (A.id a)
  inverse (a : A.Obj) (M : RightDGModuleModel A) (r j n : ℤ) (h : r+j = n)
      (m : (M.complex a).X r) (b : A.Obj) (x : (A.hom b a).X j) :
    component ((E a M).inv.f r (ULift.up m)) b j n (by omega) x = M.act r j n h m x
  natural_module (a : A.Obj) (M N : RightDGModuleModel A)
      (s r n : ℤ) (h : s+r = n) (g : gradedHom M N s)
      (f : gradedHom (representable a) M r) :
    ((E a N).hom.f n ((dgModuleCategory A).comp s r n h g f)).down =
      component g a r n (by omega) (((E a M).hom.f r f).down)
  natural_object (a b : A.Obj) (M : RightDGModuleModel A)
      (s r n : ℤ) (h : s+r = n) (f : gradedHom (representable b) M s)
      (x : (A.hom a b).X r) :
    ((E a M).hom.f n ((dgModuleCategory A).comp s r n h f
      ((E a (representable b)).inv.f r (ULift.up x)))).down =
        M.act s r n h (((E b M).hom.f s f).down) x

def EnrichedYoneda : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    ∃ E : EvaluationFamily A, EvaluationLaws E

/-- Yoneda sends a homogeneous arrow to the postcomposition map and is an isomorphism
on every Hom complex. The lift keeps the objects and transports composition via `ULift`. -/
def FullyFaithfulYoneda : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    ∃ E : EvaluationFamily A, EvaluationLaws E ∧
      ∃ F : DGFunctorModel (liftCategory A) (dgModuleCategory A),
        F.obj = representable (A := A) ∧
        (∀ a b, HEq (F.map a b) (E a (representable b)).inv) ∧
        (∀ a b, IsIso (F.map a b))

end Specs.DerivedFormalization.DG.Yoneda
