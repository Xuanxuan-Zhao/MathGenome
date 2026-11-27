import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomotopyShift
import Mathlib.CategoryTheory.Triangulated.Rotate

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace Specs.DerivedFormalization.DG.ConeRotation

open _root_.DerivedFormalization
open Basic (h0CategoryStruct h0Hom)
open HomComplex (dgModuleCategory homComplex homotopyCategory homotopyClass gradedHom
  HomotopyEquation)
open ShiftCone (shift shiftMap cone coneInclusion coneProjection)

section Constructions

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {M N : RightDGModuleModel A}

section Quotient

variable [Category.{max v w} (homotopyCategory A)]
variable [HasShift (homotopyCategory A) ℤ]

/-- The shift of a quotient object is the quotient of the signed strict shift. -/
theorem quotientShiftObj (Q : RightDGModuleModel A ⥤ homotopyCategory A)
    (hQ : ∀ X, Q.obj X = X)
    (hT : ∀ (X : homotopyCategory A) (n : ℤ),
      (shiftFunctor (homotopyCategory A) n).obj X = shift X n)
    (X : RightDGModuleModel A) (n : ℤ) :
    (shiftFunctor (homotopyCategory A) n).obj (Q.obj X) = Q.obj (shift X n) :=
  (congrArg (shiftFunctor (homotopyCategory A) n).obj (hQ X)).trans
    ((hT X n).trans (hQ (shift X n)).symm)

variable [Preadditive (homotopyCategory A)]

/-- The cone triangle with arrows `[f]`, `[j_f]`, and `−[p_f]`. -/
noncomputable abbrev coneTriangle (Q : RightDGModuleModel A ⥤ homotopyCategory A)
    (hQT : ∀ X n, (shiftFunctor (homotopyCategory A) n).obj (Q.obj X) = Q.obj (shift X n))
    (f : M ⟶ N) : Triangle (homotopyCategory A) :=
  Triangle.mk (Q.map f) (Q.map (coneInclusion f))
    (-(Q.map (coneProjection f)) ≫ eqToHom (hQT M 1).symm)

end Quotient

/-- Identify two successive strict signed shifts with the successive functor objects. -/
theorem strictShiftCompObj [HasShift (RightDGModuleModel A) ℤ]
    (hS : ∀ (X : RightDGModuleModel A) (n : ℤ),
      (shiftFunctor (RightDGModuleModel A) n).obj X = shift X n)
    (X : RightDGModuleModel A) (n m : ℤ) :
    ((shiftFunctor (RightDGModuleModel A) n ⋙ shiftFunctor (RightDGModuleModel A) m).obj X) =
      shift (shift X n) m :=
  (hS ((shiftFunctor (RightDGModuleModel A) n).obj X) m).trans
    (congrArg (fun Y => shift Y m) (hS X n))

/-- The strict shifted projection followed by the coherent cancellation `[1][-1]`. -/
noncomputable abbrev inverseConeArrow [HasShift (RightDGModuleModel A) ℤ]
    (hS : ∀ (X : RightDGModuleModel A) (n : ℤ),
      (shiftFunctor (RightDGModuleModel A) n).obj X = shift X n)
    (f : M ⟶ N) : shift (cone f) (-1) ⟶ M :=
  shiftMap (-1) (coneProjection f) ≫ eqToHom (strictShiftCompObj hS M 1 (-1)).symm ≫
    (shiftFunctorCompIsoId (RightDGModuleModel A) 1 (-1) (by decide)).hom.app M

end Constructions

/-- Both rotations of the signed cone triangle, and the right-linear contraction of the
identity cone, using one coherent choice of shifts and quotient throughout. -/
def Rotations : Prop :=
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
        ∃ (hS : ∀ (X : RightDGModuleModel A) (n : ℤ),
            (shiftFunctor (RightDGModuleModel A) n).obj X = shift X n)
          (hT : ∀ (X : homotopyCategory A) (n : ℤ),
            (shiftFunctor (homotopyCategory A) n).obj X = shift X n),
          (∀ {X Y : RightDGModuleModel A} (n : ℤ) (f : X ⟶ Y),
            HEq ((shiftFunctor (RightDGModuleModel A) n).map f) (shiftMap n f)) ∧
          (∀ n : ℤ, Functor.Additive (shiftFunctor (homotopyCategory A) n)) ∧
          (∀ (X : RightDGModuleModel A) (n m : ℤ) (h : n + m = 0) (a : A.Obj),
            HEq (((shiftFunctorCompIsoId (RightDGModuleModel A) n m h).hom.app X).app a)
              ((shiftFunctorCompIsoId (ModuleCochain.{u,v} k) n m h).hom.app (X.complex a)) ∧
            HEq (((shiftFunctorCompIsoId (RightDGModuleModel A) n m h).inv.app X).app a)
              ((shiftFunctorCompIsoId (ModuleCochain.{u,v} k) n m h).inv.app (X.complex a))) ∧
          ∃ (Q : RightDGModuleModel A ⥤ homotopyCategory A) (hQ : ∀ X, Q.obj X = X),
            (∀ {X Y : RightDGModuleModel A} (f : X ⟶ Y), HEq (Q.map f) (homotopyClass f)) ∧
            (∀ X Y, Function.Surjective (Q.map (X := X) (Y := Y))) ∧
            Q.PreservesZeroMorphisms ∧
            (∀ {X Y : RightDGModuleModel A} (n : ℤ) (f : X ⟶ Y),
              HEq ((shiftFunctor (homotopyCategory A) n).map (Q.map f)) (Q.map (shiftMap n f))) ∧
            (∀ (X : RightDGModuleModel A) (n m : ℤ) (h : n + m = 0),
              HEq (Q.map ((shiftFunctorCompIsoId (RightDGModuleModel A) n m h).hom.app X))
                ((shiftFunctorCompIsoId (homotopyCategory A) n m h).hom.app (Q.obj X)) ∧
              HEq (Q.map ((shiftFunctorCompIsoId (RightDGModuleModel A) n m h).inv.app X))
                ((shiftFunctorCompIsoId (homotopyCategory A) n m h).inv.app (Q.obj X))) ∧
            let hQT := quotientShiftObj Q hQ hT
            (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
              ∃ (s : shift M 1 ⟶ cone (coneInclusion f))
                (r : cone (coneInclusion f) ⟶ shift M 1)
                (H : gradedHom (cone (coneInclusion f)) (cone (coneInclusion f)) (-1)),
                s ≫ r = 𝟙 _ ∧ HomotopyEquation (r ≫ s) (𝟙 (cone (coneInclusion f))) H ∧
                ∃ e : (coneTriangle Q hQT f).rotate ≅ coneTriangle Q hQT (coneInclusion f),
                  e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ ∧
                  e.hom.hom₃ = eqToHom (hQT M 1) ≫ Q.map s ∧
                  e.inv.hom₃ = Q.map r ≫ eqToHom (hQT M 1).symm) ∧
            (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
              ∃ e : (coneTriangle Q hQT f).invRotate ≅ coneTriangle Q hQT (inverseConeArrow hS f),
                e.hom.hom₁ = eqToHom (hQT (cone f) (-1)) ∧ e.hom.hom₂ = 𝟙 _) ∧
            (∀ M : RightDGModuleModel A,
              ∃ H : gradedHom (cone (𝟙 M)) (cone (𝟙 M)) (-1),
                HomotopyEquation (𝟙 (cone (𝟙 M))) (0 : cone (𝟙 M) ⟶ cone (𝟙 M)) H ∧
                IsZero (Q.obj (cone (𝟙 M))))

end Specs.DerivedFormalization.DG.ConeRotation
