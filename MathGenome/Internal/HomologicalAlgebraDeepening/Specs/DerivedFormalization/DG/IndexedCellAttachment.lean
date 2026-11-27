import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSums

open CategoryTheory CategoryTheory.Limits
open _root_.DerivedFormalization

universe u v w j t

namespace Specs.DerivedFormalization.DG.IndexedCellAttachment

open IndexedSemiFree
open CoefficientLift (liftCategory liftModule liftMap)

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {P : RightDGModuleModel A} {I : Type j}

/-- The same cell data over the coefficient enlargement, with the same index. -/
def liftFamily (C : CellFamily P I) : CellFamily (liftModule.{u,v,w,t} P) I where
  object := C.object
  degree := C.degree
  boundary i := ULift.up (C.boundary i)
  closed i := ULift.ext (C.closed i)

set_option linter.checkUnivs false in
def LiftFamilyType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type j}, CellFamily P I →
      CellFamily (liftModule.{u,v,w,t} P) I

def Realization : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type j} (C : CellFamily P I),
    IndexedSums.TermsSmall (cells C) →
      ∃ Q : RightDGModuleModel A, Nonempty (Attachment C Q)

/-- The strict projection to the cell sum is the graded second projection,
and its kernel is the preceding stage. -/
def Quotient : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P Q : RightDGModuleModel A} {I : Type j} {C : CellFamily P I} (E : Attachment C Q),
    ∃ (S : RightDGModuleModel A) (s : StrictSum (cells C) S) (p : Q ⟶ S)
      (h : E.inclusion ≫ p = 0),
      Nonempty (IsColimit (Cofan.mk S s.inclusion)) ∧
      Nonempty (IsColimit (CokernelCofork.ofπ p h)) ∧
      (∀ a n x, s.coordinates a n ((p.app a).f n x) = (E.coordinates a n x).2) ∧
      ∀ a n, Function.Injective ((E.inclusion.app a).f n) ∧
        Function.Surjective ((p.app a).f n) ∧
        ∀ x, (p.app a).f n x = 0 ↔ ∃ y, (E.inclusion.app a).f n y = x

def GeneratorFormula : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P Q : RightDGModuleModel A} {I : Type j} {C : CellFamily P I} (E : Attachment C Q)
    (s : I),
    let n := C.degree s
    let b := C.object s
    let e := E.generator s
    (Q.complex b).d n (n+1) e = (E.inclusion.app b).f (n+1) (C.boundary s) ∧
    ∀ (a : A.Obj) (i q : ℤ) (h : n+i = q) (f : (A.hom a b).X i),
      E.coordinates a q (Q.act n i q h e f) =
        (0, summand (cells C) a q s
          (((A.hom a b).XIsoOfEq (by omega : i = q + -n)).hom f)) ∧
      (Q.complex a).d q (q+1) (Q.act n i q h e f) =
        (E.inclusion.app a).f (q+1) (P.act (n+1) i (q+1) (by omega) (C.boundary s) f) +
          n.negOnePow • Q.act n (i+1) (q+1) (by omega) e ((A.hom a b).d i (i+1) f)

def DifferentialSquaresToZero : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P Q : RightDGModuleModel A} {I : Type j} {C : CellFamily P I} (_ : Attachment C Q)
    (a : A.Obj) (n : ℤ) (x : (Q.complex a).X n),
      (Q.complex a).d (n+1) (n+1+1) ((Q.complex a).d n (n+1) x) = 0

/-- Coordinate comparison of any two realizations of the same data. -/
def Comparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P Q R : RightDGModuleModel A} {I : Type j} {C : CellFamily P I}
    (E : Attachment C Q) (D : Attachment C R),
    ∃ e : Q ≅ R, E.inclusion ≫ e.hom = D.inclusion ∧
      ∀ a n x, D.coordinates a n ((e.hom.app a).f n x) = E.coordinates a n x

def AdequateRealization : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type j} (C : CellFamily P I),
    ∃ Q : RightDGModuleModel (liftCategory.{u,v,w,j} A),
      Nonempty (Attachment (liftFamily.{u,v,w,j,j} C) Q)

/-- Coefficient enlargement leaves every original coordinate unchanged after
applying down, and carries the original inclusion and named generators. -/
def LiftComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P Q : RightDGModuleModel A} {I : Type j} {C : CellFamily P I}
    (E : Attachment C Q),
    ∃ D : Attachment (liftFamily.{u,v,w,j,t} C) (liftModule.{u,v,w,t} Q),
      D.inclusion = liftMap.{u,v,w,t} E.inclusion ∧
      (∀ a n x, (D.coordinates a n x).1.down = (E.coordinates a n x.down).1) ∧
      (∀ a n x i, ((D.coordinates a n x).2 i).down = (E.coordinates a n x.down).2 i) ∧
      ∀ i, (D.generator i).down = E.generator i

/-- The original coefficient-small attachment already realizes these coordinates. -/
def NativeComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type v} (C : SemiFree.CellFamily P I),
    ∃ E : Attachment (⟨C.object, C.degree, C.boundary, C.closed⟩ : CellFamily P I)
        (SemiFree.attach C),
      E.inclusion = SemiFree.inclusion C ∧
      (∀ a n x, E.coordinates a n x = x) ∧
      ∀ i, E.generator i = SemiFree.attachedGenerator C i

end Specs.DerivedFormalization.DG.IndexedCellAttachment
