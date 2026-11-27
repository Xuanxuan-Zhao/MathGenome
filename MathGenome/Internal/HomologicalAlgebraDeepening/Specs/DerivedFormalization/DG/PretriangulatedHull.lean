import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.FiniteCellConstructions
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedTriangles
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CompactFiniteCells

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open _root_.DerivedFormalization

universe u v w j t

namespace Specs.DerivedFormalization.DG.PretriangulatedHull

open AmbientDerived (category strictInput)
open Basic (h0Objects h0CategoryStruct h0Map classOf cyclesZero quasiEquivalence)
open CompactFiniteCells (CompactAt)
open CompactRepresentables (LocalizationMapAdditive)
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open DerivedTriangles (coneTriangle)
open FiniteCellConstructions
  (pretr pretrRepresentable WrittenObject writtenModule writtenSet WrittenObjectsLaws
    CanonicalFiniteCellLaws LiftedHullLaws finiteSum zeroModule FiniteIndex)
open HomComplex (homotopyCategory homotopyClass)
open KProjective (isKProjective)
open ShiftCone (shift cone)
open Yoneda (representable)

noncomputable section

variable {k : Type u} [CommRing k]

/-- The retract closure in the specified localization of the original written hull. -/
def perfect (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A)) :
    letI := derivedCategoryInstance (category.{u,v,w,t} A) h
    ObjectProperty (AmbientDerived.derivedCategory.{u,v,w,t} A h) :=
  let B := category.{u,v,w,t} A
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  let Q := AmbientDerived.quotient.{u,v,w,t} A h
  let U := strictInput.{u,v,w,t} A
  fun X => ∃ P : WrittenObject A, Nonempty (Retract X (Q.obj (U.obj (writtenModule A P))))

/-- The target supplies the distinguished triangles of the source via a
fully faithful embedding. -/
def InheritsTriangulation {C D : Type*} [Category* C] [Category* D]
    [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) : Prop :=
  ∃ (SC : HasShift C ℤ) (AC : Preadditive C) (ZC : HasZeroObject C),
    letI := SC
    letI := AC
    letI := ZC
    ∃ (LC : ∀ n : ℤ, (shiftFunctor C n).Additive) (e : F.CommShift ℤ),
      letI := LC
      letI := e
      ∃ TC : Pretriangulated C,
        letI := TC
        IsTriangulated C ∧ F.Additive ∧ F.IsTriangulated ∧
          ∀ T : Triangle C, T ∈ distTriang C ↔ F.mapTriangle.obj T ∈ distTriang D

/-- Lift a cycle of the original Hom complex to the coefficient realization
used to form the enriched Yoneda functor. -/
def liftCycle {A : DGCategoryModel.{u,v,w} k} {a b : A.Obj}
    (f : cyclesZero (A.hom a b)) :
    cyclesZero ((Yoneda.liftCategory A).hom a b) :=
  ⟨ULift.up f.val, ULift.ext f.property⟩

/-- The enriched Yoneda map uses the original arrows, represented by their
coefficient lifts in the common Hom universe. -/
def IsWrittenYoneda {A : DGCategoryModel.{u,v,w} k}
    (Y : DGFunctorModel (Yoneda.liftCategory A) (pretr A)) : Prop :=
  Y.obj = pretrRepresentable A ∧
    ∃ E : Yoneda.EvaluationFamily A, Yoneda.EvaluationLaws E ∧
      ∀ a b, HEq (Y.map a b) (E a (representable b)).inv ∧ IsIso (Y.map a b)

/-- Strict finite constructions in the original hull, interpreted by the
specified localization functor. -/
def FiniteConstructionsInDerived (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A))
    (SK : letI := Derived.homotopyCategory _ h; HasShift (AmbientDerived.homotopyCategory.{u,v,w,t} A) ℤ)
    (hS : letI := Derived.homotopyCategory _ h; letI := SK
      ∀ M n, (shiftFunctor (AmbientDerived.homotopyCategory.{u,v,w,t} A) n).obj M = shift M n)
    (SD : letI := derivedCategoryInstance _ h; HasShift (AmbientDerived.derivedCategory.{u,v,w,t} A h) ℤ)
    (qS :
      let B := category.{u,v,w,t} A
      let K := AmbientDerived.homotopyCategory.{u,v,w,t} A
      let D := AmbientDerived.derivedCategory.{u,v,w,t} A h
      letI := Derived.homotopyCategory B h
      letI := derivedCategoryInstance B h
      letI := SK
      letI := SD
      let Q : K ⥤ D := AmbientDerived.quotient.{u,v,w,t} A h
      Q.CommShift ℤ) :
    Prop :=
  let B := category.{u,v,w,t} A
  let K := AmbientDerived.homotopyCategory.{u,v,w,t} A
  let D := AmbientDerived.derivedCategory.{u,v,w,t} A h
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  letI := SK
  letI := SD
  letI := qS
  let Q : K ⥤ D := AmbientDerived.quotient.{u,v,w,t} A h
  let U := strictInput.{u,v,w,t} A
  let image (M : RightDGModuleModel A) := Q.obj (U.obj M)
  IsZero (image (zeroModule A)) ∧
    (∀ (X : WrittenObject A) (n : ℤ),
      Nonempty (image (shift (writtenModule A X) n) ≅
        (shiftFunctor D n).obj (image (writtenModule A X)))) ∧
    (∀ {n : ℕ} (F : Fin n → WrittenObject A),
      let M : Fin n → RightDGModuleModel A := writtenModule A ∘ F
      let FS : FiniteIndex.{v} n → RightDGModuleModel A := fun i => M i.down
      Nonempty (IsColimit (Cofan.mk (f := image ∘ FS) (image (finiteSum M))
        (fun i => Q.map (homotopyClass (U.map (SemiFree.sumInclusion FS i))))))) ∧
    (∀ {X Y : WrittenObject A} (f : writtenModule A X ⟶ writtenModule A Y),
      let T := Q.mapTriangle.obj (coneTriangle h SK (hS (U.obj (writtenModule A X)) 1) (U.map f))
      Nonempty (image (cone f) ≅ T.obj₃))

/-- The original Yoneda image represents every finite-cell module in the
original right-linear homotopy category. -/
def RepresentedUpToHomotopy (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws A) : Prop :=
  letI := Derived.homotopyCategory A h
  ∀ P : RightDGModuleModel A, IndexedSemiFree.finiteCell P →
    ∃ a : A.Obj, Nonempty (@Iso (homotopyCategory A) (Derived.homotopyCategory A h)
      (representable (A := A) a) P)

/-- The pretriangulated hull proposition, with all derived conclusions taken
in the common adequate localization. -/
def HullTheorem : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    let B := category.{u,v,w,t} A
    let U := strictInput.{u,v,w,t} A
    ∀ (h₀ : HomotopyCategoryLaws A) (h : HomotopyCategoryLaws B),
      let K := homotopyCategory B
      let D := AmbientDerived.derivedCategory.{u,v,w,t} A h
      letI := Derived.homotopyCategory B h
      letI := derivedCategoryInstance B h
      let Q : K ⥤ D := AmbientDerived.quotient.{u,v,w,t} A h
      WrittenObjectsLaws A ∧ CanonicalFiniteCellLaws.{u,v,w,j} A ∧
        LiftedHullLaws.{u,v,w,max w t} A ∧
      ∃ (Y : DGFunctorModel (Yoneda.liftCategory A) (pretr A)) (CH : Category.{max v w} (h0Objects (pretr A)))
        (CA : Category.{v} (h0Objects A)),
        CH.toCategoryStruct = h0CategoryStruct (pretr A) ∧ CA.toCategoryStruct = h0CategoryStruct A ∧
        IsWrittenYoneda Y ∧
        (quasiEquivalence Y ↔ RepresentedUpToHomotopy A h₀) ∧
        letI := CH
        letI := CA
        ∃ (G : h0Objects A ⥤ h0Objects (pretr A)) (E : h0Objects (pretr A) ⥤ D),
          G.obj = Y.obj ∧
          (∀ {a b : h0Objects A} (f : cyclesZero (A.hom a b)), ∃ g : a ⟶ b,
            HEq g (classOf f) ∧ HEq (G.map g) (h0Map Y (classOf (liftCycle f)))) ∧
          Nonempty E.FullyFaithful ∧
          (∀ X : WrittenObject A, E.obj X = Q.obj (U.obj (writtenModule A X))) ∧
          (∀ {X Y : h0Objects (pretr A)} (f : writtenModule A X ⟶ writtenModule A Y),
            ∃ g : X ⟶ Y,
              HEq g (homotopyClass f) ∧ HEq (E.map g) (Q.map (homotopyClass (U.map f)))) ∧
          (∀ X : WrittenObject A, isKProjective (U.obj (writtenModule A X))) ∧
        ∃ (SK : HasShift K ℤ) (AK : Preadditive K) (ZK : HasZeroObject K),
          letI := SK
          letI := AK
          letI := ZK
          ∃ (LK : ∀ n : ℤ, (shiftFunctor K n).Additive)
            (hS : ∀ M n, (shiftFunctor K n).obj M = shift M n) (TK : Pretriangulated K)
            (SD : HasShift D ℤ) (AD : Preadditive D) (ZD : HasZeroObject D),
            letI := LK
            letI := TK
            letI := SD
            letI := AD
            letI := ZD
            ∃ (LD : ∀ n : ℤ, (shiftFunctor D n).Additive) (qS : Q.CommShift ℤ)
              (TD : Pretriangulated D),
              letI := LD
              letI := qS
              letI := TD
              IsTriangulated D ∧ Q.IsTriangulated ∧ LocalizationMapAdditive h AD ∧
              (∀ {M N : RightDGModuleModel B} (f : M ⟶ N),
                Q.mapTriangle.obj (coneTriangle h SK (hS M 1) f) ∈ distTriang D) ∧
              FiniteConstructionsInDerived.{u,v,w,t} A h SK hS SD qS ∧
              E.essImage.IsTriangulated ∧ InheritsTriangulation E ∧
              (∀ X : D,
                (CompactAt.{u,w,max v w t,max v w t} h AD X ↔ perfect A h X) ∧
                  (perfect A h X → CompactAt.{u,w,j,max v w t} h AD X)) ∧
              (quasiEquivalence Y → G.IsEquivalence ∧ InheritsTriangulation (G ⋙ E))

end
end Specs.DerivedFormalization.DG.PretriangulatedHull
