import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ConeRotation
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace Specs.DerivedFormalization.DG.HomotopyPretriangulated

open _root_.DerivedFormalization
open Basic (h0CategoryStruct h0Hom)
open HomComplex (dgModuleCategory homComplex homotopyCategory homotopyClass)
open ShiftCone (shift shiftMap)
open ConeRotation (coneTriangle quotientShiftObj)

/-- The signed cone triangles and their isomorphism closure in the degree-zero
cohomology category of right dg modules give a pretriangulated structure. -/
def Pretriangulation : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    ∃ C : Category.{max v w} (homotopyCategory A),
      C.toCategoryStruct = h0CategoryStruct (dgModuleCategory A) ∧
      letI := C
      ∃ (P : Preadditive (homotopyCategory A)) (S : HasShift (homotopyCategory A) ℤ)
        (Z : HasZeroObject (homotopyCategory A)),
        letI := P
        letI := S
        letI := Z
        ∃ (L : ∀ n : ℤ, Functor.Additive (shiftFunctor (homotopyCategory A) n))
          (hShift : ∀ (X : homotopyCategory A) (n : ℤ),
            (shiftFunctor (homotopyCategory A) n).obj X = shift X n)
          (Q : RightDGModuleModel A ⥤ homotopyCategory A) (hObj : ∀ X, Q.obj X = X),
          letI := L
          (∀ X Y : homotopyCategory A,
            HEq (P.homGroup X Y) (inferInstance : AddCommGroup (h0Hom (homComplex X Y)))) ∧
          (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
            HEq (Q.map f) (homotopyClass f)) ∧
          (∀ M N, Function.Surjective (Q.map (X := M) (Y := N))) ∧
          (∀ {M N : RightDGModuleModel A} (n : ℤ) (f : M ⟶ N),
            HEq ((shiftFunctor (homotopyCategory A) n).map (Q.map f))
              (Q.map (shiftMap n f))) ∧
          ∃ T : Pretriangulated (homotopyCategory A),
            letI := T
            let hQT := quotientShiftObj Q hObj hShift
            (∀ X : Triangle (homotopyCategory A),
              X ∈ distTriang (homotopyCategory A) ↔
                ∃ (M N : RightDGModuleModel A) (f : M ⟶ N),
                  Nonempty (X ≅ coneTriangle Q hQT f)) ∧
            (∀ {M N : RightDGModuleModel A} (f g : M ⟶ N),
              homotopyClass f = homotopyClass g →
              ∃ e : coneTriangle Q hQT f ≅ coneTriangle Q hQT g,
                e.hom.hom₁ = 𝟙 (Q.obj M) ∧ e.hom.hom₂ = 𝟙 (Q.obj N))

end Specs.DerivedFormalization.DG.HomotopyPretriangulated
