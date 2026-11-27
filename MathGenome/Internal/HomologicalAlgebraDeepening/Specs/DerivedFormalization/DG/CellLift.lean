import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedCellAttachment
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CellReindex

open CategoryTheory CategoryTheory.Limits
open _root_.DerivedFormalization
open scoped DirectSum

universe u v w j t

namespace Specs.DerivedFormalization.DG.CellLift

open IndexedSemiFree CoefficientLift
open IndexedCellAttachment (liftFamily)

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
  {M : RightDGModuleModel A}

/-- Each attachment is realized on the lift of its specified successor stage. -/
structure LiftedExtensions (F : Presentation.{u,v,w,j} M) where
  extension (l : ℕ) :
    Attachment (liftFamily.{u,v,w,j,t} (F.family l)) (liftModule.{u,v,w,t} (F.stage (l+1)))
  inclusion (l : ℕ) : (extension l).inclusion = liftMap.{u,v,w,t} (F.extension l).inclusion

@[reducible] def LiftedExtensions.toPresentation {F : Presentation.{u,v,w,j} M}
    (L : LiftedExtensions.{u,v,w,j,t} F) :
    Presentation.{u,max v t,w,j} (liftModule.{u,v,w,t} M) where
  stage l := liftModule.{u,v,w,t} (F.stage l)
  bottom a n x := ULift.ext (F.bottom a n x.down)
  index := F.index
  family l := liftFamily.{u,v,w,j,t} (F.family l)
  extension := L.extension
  into l := liftMap.{u,v,w,t} (F.into l)
  compatible l := by
    rw [L.inclusion l]
    exact ((liftFunctor.{u,v,w,t} A).map_comp _ _).symm.trans
      (congrArg (liftFunctor.{u,v,w,t} A).map (F.compatible l))
  injective l a n x y h :=
    ULift.ext (F.injective l a n (congrArg ULift.down h))
  exhaustive a n x := by
    obtain ⟨l, y, h⟩ := F.exhaustive a n x.down
    exact ⟨l, ULift.up y, ULift.ext h⟩

/-- The graded splitting, its named generators and the actual cell quotients
transport along the degreewise coefficient equivalences. -/
structure AttachmentLaws {F : Presentation.{u,v,w,j} M}
    (L : LiftedExtensions.{u,v,w,j,t} F) : Prop where
  previous (l : ℕ) (a : A.Obj) (n : ℤ) (x : ((L.toPresentation.stage (l+1)).complex a).X n) :
    ((L.extension l).coordinates a n x).1.down =
      ((F.extension l).coordinates a n x.down).1
  coordinate (l : ℕ) (a : A.Obj) (n : ℤ) (x : ((L.toPresentation.stage (l+1)).complex a).X n)
      (i : F.index l) :
    (((L.extension l).coordinates a n x).2 i).down =
      ((F.extension l).coordinates a n x.down).2 i
  generator (l : ℕ) (i : F.index l) :
    ((L.extension l).generator i).down = (F.extension l).generator i
  quotient (l : ℕ) :
    ∃ (S : RightDGModuleModel A) (s : StrictSum (cells (F.family l)) S)
      (r : StrictSum (cells (L.toPresentation.family l)) (liftModule.{u,v,w,t} S))
      (p : F.stage (l+1) ⟶ S)
      (h : (F.extension l).inclusion ≫ p = 0)
      (h' : (L.extension l).inclusion ≫ liftMap.{u,v,w,t} p = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ p h)) ∧
      Nonempty (IsColimit (Cofan.mk _ r.inclusion)) ∧
      Nonempty (IsColimit (CokernelCofork.ofπ (liftMap.{u,v,w,t} p) h')) ∧
      (∀ i, r.inclusion i = liftMap.{u,v,w,t} (s.inclusion i)) ∧
      (∀ a n x i, (r.coordinates a n x i).down = s.coordinates a n x.down i) ∧
      (∀ a n x, s.coordinates a n ((p.app a).f n x) = ((F.extension l).coordinates a n x).2) ∧
      (∀ a n x, r.coordinates a n (((liftMap.{u,v,w,t} p).app a).f n x) =
        ((L.extension l).coordinates a n x).2) ∧
      ∀ a n, Function.Injective (((L.extension l).inclusion.app a).f n) ∧
        Function.Surjective (((liftMap.{u,v,w,t} p).app a).f n) ∧
        ∀ x, ((liftMap.{u,v,w,t} p).app a).f n x = 0 ↔
          ∃ y, ((L.extension l).inclusion.app a).f n y = x

/-- The coordinates on the union and on each stage keep their original cell labels. -/
structure SupportLaws {F : Presentation.{u,v,w,j} M}
    (L : LiftedExtensions.{u,v,w,j,t} F) : Prop where
  decomposition :
    ∃ (D : CellReindex.GradedDecomposition F)
      (U : CellReindex.GradedDecomposition L.toPresentation),
      (∀ N a n x i, (U.stageCoordinates N a n x i).down = D.stageCoordinates N a n x.down i) ∧
      (∀ a n x i, (U.coordinates a n x i).down = D.coordinates a n x.down i) ∧
      ∀ a n x, Set.Finite {i | U.coordinates a n x i ≠ 0} ∧
        ∃ N : ℕ, ∀ i, N ≤ i.1 → U.coordinates a n x i = 0

def PresentationTransport : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M),
    ∃ L : LiftedExtensions.{u,v,w,j,t} F, AttachmentLaws L ∧ SupportLaws L

/-- Pull back specified attaching cycles through a strict stage isomorphism,
using the same objects and degrees with the chosen labels. -/
def pullbackFamily {P : RightDGModuleModel A}
    {Q : RightDGModuleModel (liftCategory.{u,v,w,t} A)}
    {I : Type j} {J : Type v} (C : CellFamily Q I) (r : J ≃ I)
    (e : liftModule.{u,v,w,t} P ≅ Q) : CellFamily P J where
  object i := C.object (r i)
  degree i := C.degree (r i)
  boundary i := ((e.inv.app (C.object (r i))).f (C.degree (r i)+1) (C.boundary (r i))).down
  closed i := by
    let b := C.object (r i)
    let n := C.degree (r i)+1
    have he := CategoryTheory.congr_fun ((e.inv.app b).comm n (n+1)) (C.boundary (r i))
    change ((liftModule.{u,v,w,t} P).complex b).d n (n+1)
      ((e.inv.app b).f n (C.boundary (r i))) =
        (e.inv.app b).f (n+1) ((Q.complex b).d n (n+1) (C.boundary (r i))) at he
    rw [C.closed (r i), map_zero] at he
    exact congrArg ULift.down he

/-- The finite filtration with its original attaching data, and the strict
comparison on every stage and at the terminal module. -/
structure DescentLaws {L : RightDGModuleModel (liftCategory.{u,v,w,t} A)}
    (F : Presentation.{u,max v t,w,j} L) (G : Presentation.{u,v,w,v} M) where
  labeling (l : ℕ) : G.index l ≃ F.index l
  stage (l : ℕ) : liftModule.{u,v,w,t} (G.stage l) ≅ F.stage l
  family (l : ℕ) : G.family l = pullbackFamily (F.family l) (labeling l) (stage l)
  inclusion (l : ℕ) :
    liftMap.{u,v,w,t} (G.extension l).inclusion ≫ (stage (l+1)).hom =
      (stage l).hom ≫ (F.extension l).inclusion
  terminal : liftModule.{u,v,w,t} M ≅ L
  into (l : ℕ) : liftMap.{u,v,w,t} (G.into l) ≫ terminal.hom = (stage l).hom ≫ F.into l

def FiniteDescent : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {L : RightDGModuleModel (liftCategory.{u,v,w,t} A)}
    (F : Presentation.{u,max v t,w,j} L), Finite (Σ l, F.index l) →
    ∃ (M : RightDGModuleModel A) (G : Presentation.{u,v,w,v} M),
      Finite (Σ l, G.index l) ∧ Nonempty (DescentLaws F G)

def SemiFreeTransport : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} (M : RightDGModuleModel A),
    semiFree M → semiFree (liftModule.{u,v,w,t} M)

def FiniteCellTransport : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (L : RightDGModuleModel (liftCategory.{u,v,w,t} A)),
    finiteCell L ↔ ∃ M : RightDGModuleModel A,
      finiteCell M ∧ Nonempty (liftModule.{u,v,w,t} M ≅ L)

end

end Specs.DerivedFormalization.DG.CellLift
