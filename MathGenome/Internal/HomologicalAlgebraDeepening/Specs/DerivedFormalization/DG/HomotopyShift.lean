import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Specs.DerivedFormalization.DG.HomotopyShift

open _root_.DerivedFormalization
open Basic (h0CategoryStruct h0Hom)
open HomComplex (dgModuleCategory homComplex homotopyCategory homotopyClass)
open ShiftCone (shift shiftMap)

/-- The signed strict shifts and the induced additive shifts on the fixed
degree-zero cohomology category. Cancellation is tested for every pair of
opposite integers, in both directions. -/
def ShiftCoherence : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    ∃ C : Category.{max v w} (homotopyCategory A),
      C.toCategoryStruct = h0CategoryStruct (dgModuleCategory A) ∧
      letI := C
      ∃ (P : Preadditive (homotopyCategory A)) (_Z : HasZeroObject (homotopyCategory A))
        (S : HasShift (RightDGModuleModel A) ℤ) (T : HasShift (homotopyCategory A) ℤ),
        letI := P
        letI := S
        letI := T
        (∀ (X Y : homotopyCategory A),
          HEq (P.homGroup X Y) (inferInstance : AddCommGroup (h0Hom (homComplex X Y)))) ∧
        (∀ (X : RightDGModuleModel A) (n : ℤ),
          (shiftFunctor (RightDGModuleModel A) n).obj X = shift X n) ∧
        (∀ {X Y : RightDGModuleModel A} (n : ℤ) (f : X ⟶ Y),
          HEq ((shiftFunctor (RightDGModuleModel A) n).map f) (shiftMap n f)) ∧
        (∀ (X : homotopyCategory A) (n : ℤ),
          (shiftFunctor (homotopyCategory A) n).obj X = shift X n) ∧
        (∀ n : ℤ, Functor.Additive (shiftFunctor (homotopyCategory A) n)) ∧
        (∀ (X : RightDGModuleModel A) (n m : ℤ) (h : n + m = 0) (a : A.Obj),
          HEq (((shiftFunctorCompIsoId (RightDGModuleModel A) n m h).hom.app X).app a)
            ((shiftFunctorCompIsoId (ModuleCochain.{u,v} k) n m h).hom.app (X.complex a)) ∧
          HEq (((shiftFunctorCompIsoId (RightDGModuleModel A) n m h).inv.app X).app a)
            ((shiftFunctorCompIsoId (ModuleCochain.{u,v} k) n m h).inv.app (X.complex a))) ∧
        ∃ Q : RightDGModuleModel A ⥤ homotopyCategory A,
          (∀ X, Q.obj X = X) ∧
          (∀ {X Y : RightDGModuleModel A} (f : X ⟶ Y), HEq (Q.map f) (homotopyClass f)) ∧
          (∀ X Y, Function.Surjective (Q.map (X := X) (Y := Y))) ∧
          Q.PreservesZeroMorphisms ∧
          (∀ {X Y : RightDGModuleModel A} (n : ℤ) (f : X ⟶ Y),
            HEq ((shiftFunctor (homotopyCategory A) n).map (Q.map f)) (Q.map (shiftMap n f))) ∧
          (∀ (X : RightDGModuleModel A) (n m : ℤ) (h : n + m = 0),
            HEq (Q.map ((shiftFunctorCompIsoId (RightDGModuleModel A) n m h).hom.app X))
              ((shiftFunctorCompIsoId (homotopyCategory A) n m h).hom.app (Q.obj X)) ∧
            HEq (Q.map ((shiftFunctorCompIsoId (RightDGModuleModel A) n m h).inv.app X))
              ((shiftFunctorCompIsoId (homotopyCategory A) n m h).inv.app (Q.obj X)))

end Specs.DerivedFormalization.DG.HomotopyShift
