import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSemiFree
import Mathlib.Logic.Small.Basic

open CategoryTheory
open scoped DirectSum

universe u v w j t

namespace Specs.DerivedFormalization.DG.CellReindex

open _root_.DerivedFormalization
open IndexedSemiFree

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {P Q M : RightDGModuleModel A} {I : Type j} {J : Type t}

/-- The indices whose shifted representables have a nonzero identity generator. -/
abbrev NonzeroIndex (C : CellFamily P I) := {i : I // A.id (C.object i) ≠ 0}

/-- Pull back the objects, degrees, and actual attaching cycles along an index map. -/
def reindexFamily (C : CellFamily P I) (f : J → I) : CellFamily P J where
  object i := C.object (f i)
  degree i := C.degree (f i)
  boundary i := C.boundary (f i)
  closed i := C.closed (f i)

def ZeroCells : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type j} (C : CellFamily P I) (i : I),
    A.id (C.object i) = 0 →
      C.boundary i = 0 ∧
      ∀ (a : A.Obj) (n : ℤ) (x : ((cells C i).complex a).X n), x = 0

/-- The object and degree identify the type of a named generator. In each such
type the nonzero generators of distinct summands are distinct. -/
def GeneratorSeparation : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P Q : RightDGModuleModel A} {I : Type j} {C : CellFamily P I}
    (E : Attachment C Q),
    (∀ i, E.generator i = 0 ↔ A.id (C.object i) = 0) ∧
    Function.Injective (fun i : NonzeroIndex C =>
      (⟨C.object i, C.degree i, E.generator i⟩ :
        Σ a : A.Obj, Σ n : ℤ, (Q.complex a).X n))

/-- A reindexing realizes the same attachments on the same stages, keeping
the inclusions and all coordinates apart from the change of cell labels. -/
structure Reindexing (F : Presentation.{u,v,w,j} M) where
  index : ℕ → Type t
  original (l : ℕ) : index l ≃ NonzeroIndex (F.family l)
  extension (l : ℕ) :
    Attachment (reindexFamily (F.family l) (fun i => (original l i).val)) (F.stage (l + 1))
  inclusion (l : ℕ) : (extension l).inclusion = (F.extension l).inclusion
  previous_coordinate (l : ℕ) (a : A.Obj) (n : ℤ) (x : ((F.stage (l + 1)).complex a).X n) :
    ((extension l).coordinates a n x).1 = ((F.extension l).coordinates a n x).1
  cell_coordinate (l : ℕ) (a : A.Obj) (n : ℤ) (x : ((F.stage (l + 1)).complex a).X n)
      (i : index l) :
    ((extension l).coordinates a n x).2 i =
      ((F.extension l).coordinates a n x).2 (original l i).val
  generator (l : ℕ) (i : index l) :
    (extension l).generator i = (F.extension l).generator (original l i).val

def Reindexing.toPresentation {F : Presentation.{u,v,w,j} M} (R : Reindexing.{u,v,w,j,t} F) :
    Presentation.{u,v,w,t} M where
  stage := F.stage
  bottom := F.bottom
  index := R.index
  family l := reindexFamily (F.family l) (fun i => (R.original l i).val)
  extension := R.extension
  into := F.into
  compatible l := by rw [R.inclusion l]; exact F.compatible l
  injective := F.injective
  exhaustive := F.exhaustive

/-- A single construction works at every index universe containing the surviving cells. -/
def Reindex : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M),
    (∀ l, Small.{t} (NonzeroIndex (F.family l))) →
    ∃ R : Reindexing.{u,v,w,j,t} F, Finite (Σ l, F.index l) → Finite (Σ l, R.index l)

def Normalize : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M),
    ∃ R : Reindexing.{u,v,w,j,max v w} F, Finite (Σ l, F.index l) → Finite (Σ l, R.index l)

section Decomposition

variable (F : Presentation.{u,v,w,j} M)

/-- The graded map from a single cell to the stage where it was adjoined. -/
def cellToSuccessor (l : ℕ) (i : F.index l) (a : A.Obj) (n : ℤ) :
    ((cells (F.family l) i).complex a).X n →ₗ[k] ((F.stage (l+1)).complex a).X n :=
  ((F.extension l).coordinates a n).symm.toLinearMap.comp
    ((LinearMap.inr k _ _).comp (summand (cells (F.family l)) a n i))

/-- The strict inclusion from one stage into a later stage. -/
def stageInclusion {l N : ℕ} (h : l ≤ N) : F.stage l ⟶ F.stage N :=
  Functor.OfSequence.map (fun l => (F.extension l).inclusion) l N h

/-- The cells occurring strictly before the indicated stage. -/
abbrev StageIndex (N : ℕ) := Σ l : Fin N, F.index l.val

abbrev stageCells (N : ℕ) (s : StageIndex F N) := cells (F.family s.1.val) s.2

abbrev allCells (s : Σ l, F.index l) := cells (F.family s.1) s.2

def cellToStage (N : ℕ) (s : StageIndex F N) (a : A.Obj) (n : ℤ) :
    ((stageCells F N s).complex a).X n →ₗ[k] ((F.stage N).complex a).X n :=
  (((stageInclusion F (Nat.succ_le_of_lt s.1.isLt)).app a).f n).hom.comp
    (cellToSuccessor F s.1.val s.2 a n)

def cellToModule (s : Σ l, F.index l) (a : A.Obj) (n : ℤ) :
    ((allCells F s).complex a).X n →ₗ[k] (M.complex a).X n :=
  (((F.into (s.1+1)).app a).f n).hom.comp (cellToSuccessor F s.1 s.2 a n)

/-- Coordinates on the union and each stage, for the actual graded direct sums
along the named cell maps. The differential can have components in earlier stages. -/
structure GradedDecomposition where
  stageCoordinates (N : ℕ) (a : A.Obj) (n : ℤ) :
    ((F.stage N).complex a).X n ≃ₗ[k] SumTerm (stageCells F N) a n
  coordinates (a : A.Obj) (n : ℤ) : (M.complex a).X n ≃ₗ[k] SumTerm (allCells F) a n
  stage_cell (N : ℕ) (s : StageIndex F N) (a : A.Obj) (n : ℤ)
      (x : ((stageCells F N s).complex a).X n) :
    stageCoordinates N a n (cellToStage F N s a n x) = summand (stageCells F N) a n s x
  cell (s : Σ l, F.index l) (a : A.Obj) (n : ℤ) (x : ((allCells F s).complex a).X n) :
    coordinates a n (cellToModule F s a n x) = summand (allCells F) a n s x
  into (N : ℕ) (a : A.Obj) (n : ℤ) (x : ((F.stage N).complex a).X n)
      (s : Σ l, F.index l) :
    coordinates a n ((F.into N).app a |>.f n x) s =
      if h : s.1 < N then stageCoordinates N a n x ⟨⟨s.1, h⟩, s.2⟩ else 0
  stage_coordinate_act (N : ℕ) {a b : A.Obj} (m n q : ℤ) (h : m+n = q)
      (x : ((F.stage N).complex b).X m) (f : (A.hom a b).X n) (s : StageIndex F N) :
    stageCoordinates N a q ((F.stage N).act m n q h x f) s =
      (stageCells F N s).act m n q h (stageCoordinates N b m x s) f
  coordinate_act {a b : A.Obj} (m n q : ℤ) (h : m+n = q)
      (x : (M.complex b).X m) (f : (A.hom a b).X n) (s : Σ l, F.index l) :
    coordinates a q (M.act m n q h x f) s =
      (allCells F s).act m n q h (coordinates b m x s) f

end Decomposition

def CellMapFormula : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M)
    (l : ℕ) (i : F.index l) (a : A.Obj) (m n : ℤ) (h : (F.family l).degree i + m = n)
    (f : (A.hom a ((F.family l).object i)).X m),
    cellToSuccessor F l i a n ((A.hom a ((F.family l).object i)).XIsoOfEq
        (by omega : m = n + -(F.family l).degree i) |>.hom f) =
      (F.stage (l+1)).act ((F.family l).degree i) m n h ((F.extension l).generator i) f

def DirectSumDecomposition : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M),
    ∃ D : GradedDecomposition F,
      ∀ (a : A.Obj) (n : ℤ) (x : (M.complex a).X n),
        Set.Finite {s | D.coordinates a n x s ≠ 0} ∧
          ∃ N : ℕ, ∀ s, N ≤ s.1 → D.coordinates a n x s = 0

section SmallPresentations

/-- Forget that a family with coefficient-small indices had an independent index universe. -/
def smallFamily {I : Type v} (C : CellFamily P I) : SemiFree.CellFamily P I :=
  ⟨C.object, C.degree, C.boundary, C.closed⟩

def indexedFamily {I : Type v} (C : SemiFree.CellFamily P I) : CellFamily P I :=
  ⟨C.object, C.degree, C.boundary, C.closed⟩

/-- An indexed presentation at the coefficient bound, realized by the concrete
attachments. Inverses of the strict stage isomorphisms are the graded coordinates. -/
structure SmallRealization (F : Presentation.{u,v,w,v} M) where
  successor (l : ℕ) : SemiFree.attach (smallFamily (F.family l)) ≅ F.stage (l+1)
  inclusion (l : ℕ) :
    SemiFree.inclusion (smallFamily (F.family l)) ≫ (successor l).hom = (F.extension l).inclusion
  coordinate (l : ℕ) (a : A.Obj) (n : ℤ) (x : ((F.stage (l+1)).complex a).X n) :
    ((successor l).inv.app a).f n x = (F.extension l).coordinates a n x

def SmallRealization.toPresentation {F : Presentation.{u,v,w,v} M} (S : SmallRealization F) :
    SemiFree.Presentation M where
  stage := F.stage
  bottom := F.bottom
  index := F.index
  family l := smallFamily (F.family l)
  successor := S.successor
  into := F.into
  compatible l := by rw [← Category.assoc, S.inclusion l]; exact F.compatible l
  injective := F.injective
  exhaustive := F.exhaustive

def ToSmall : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M),
    (∀ l, Small.{v} (NonzeroIndex (F.family l))) →
    ∃ R : Reindexing.{u,v,w,j,v} F,
      Nonempty (SmallRealization R.toPresentation) ∧
        (Finite (Σ l, F.index l) → Finite (Σ l, R.index l))

/-- The concrete filtration also gives indexed attachments on those very stages,
with the original index types and the original strict inclusion composites. -/
def FromSmall : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : SemiFree.Presentation M),
    ∃ E : ∀ l, Attachment (indexedFamily (F.family l)) (F.stage (l+1)),
      (∀ l, (E l).inclusion = SemiFree.inclusion (F.family l) ≫ (F.successor l).hom) ∧
      ∀ l a n x, (E l).coordinates a n x = ((F.successor l).inv.app a).f n x

def indexedPresentation (F : SemiFree.Presentation M)
    (E : ∀ l, Attachment (indexedFamily (F.family l)) (F.stage (l+1)))
    (he : ∀ l, (E l).inclusion = SemiFree.inclusion (F.family l) ≫ (F.successor l).hom) :
    Presentation.{u,v,w,v} M where
  stage := F.stage
  bottom := F.bottom
  index := F.index
  family l := indexedFamily (F.family l)
  extension := E
  into := F.into
  compatible l := by rw [he l, Category.assoc]; exact F.compatible l
  injective := F.injective
  exhaustive := F.exhaustive

def FiniteCellComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} (M : RightDGModuleModel A),
    IndexedSemiFree.finiteCell M ↔ SemiFree.finiteCell M

end SmallPresentations

end

end Specs.DerivedFormalization.DG.CellReindex
