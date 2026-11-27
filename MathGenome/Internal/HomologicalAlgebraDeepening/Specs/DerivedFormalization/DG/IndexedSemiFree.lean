import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.SemiFree

open CategoryTheory
open scoped DirectSum

universe u v w j

namespace Specs.DerivedFormalization.DG.IndexedSemiFree

open _root_.DerivedFormalization

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {I : Type j}

/-- The raw finite-support sum, which can be larger than the coefficient universe. -/
abbrev SumTerm (F : I → RightDGModuleModel A) (a : A.Obj) (n : ℤ) :=
  ⨁ s : I, ((F s).complex a).X n

def summand (F : I → RightDGModuleModel A) (a : A.Obj) (n : ℤ) (s : I) :
    ((F s).complex a).X n →ₗ[k] SumTerm F a n := by
  classical
  exact DirectSum.lof k I (fun t => ((F t).complex a).X n) s

/-- Realization of an arbitrary-index, degreewise direct sum in the original
module universe. The coordinates record the differential, action, and summand maps. -/
structure StrictSum (F : I → RightDGModuleModel A) (S : RightDGModuleModel A) where
  inclusion : ∀ s, F s ⟶ S
  coordinates (a : A.Obj) (n : ℤ) : (S.complex a).X n ≃ₗ[k] SumTerm F a n
  coordinate_inclusion (s : I) (a : A.Obj) (n : ℤ) (x : ((F s).complex a).X n) :
    coordinates a n ((inclusion s).app a |>.f n x) = summand F a n s x
  coordinate_d (a : A.Obj) (n : ℤ) (x : (S.complex a).X n) (s : I) :
    coordinates a (n + 1) ((S.complex a).d n (n + 1) x) s =
      ((F s).complex a).d n (n + 1) (coordinates a n x s)
  coordinate_act {a b : A.Obj} (m n q : ℤ) (h : m + n = q)
      (x : (S.complex b).X m) (f : (A.hom a b).X n) (s : I) :
    coordinates a q (S.act m n q h x f) s = (F s).act m n q h (coordinates b m x s) f

/-- An arbitrary set of cells with closed attaching elements in the preceding stage. -/
structure CellFamily (P : RightDGModuleModel A) (I : Type j) where
  object : I → A.Obj
  degree : I → ℤ
  boundary (s : I) : (P.complex (object s)).X (degree s + 1)
  closed (s : I) :
    (P.complex (object s)).d (degree s + 1) (degree s + 1 + 1) (boundary s) = 0

variable {P Q : RightDGModuleModel A}

abbrev cells (C : CellFamily P I) (s : I) := SemiFree.cell (C.object s) (C.degree s)

abbrev CellTerm (C : CellFamily P I) (a : A.Obj) (n : ℤ) := SumTerm (cells C) a n

/-- The off-diagonal differential sends a multiple of a cell generator to
the same multiple of its attaching element. -/
def boundaryMap (C : CellFamily P I) (a : A.Obj) (n : ℤ) :
    CellTerm C a n →ₗ[k] (P.complex a).X (n + 1) := by
  classical
  exact DirectSum.toModule k I _ fun s =>
    P.act (C.degree s + 1) (n + -C.degree s) (n + 1) (by omega) (C.boundary s)

/-- A realization of the graded-split attachment on a specified next-stage
module. The coordinate laws prescribe the full graded right action and differential. -/
structure Attachment (C : CellFamily P I) (Q : RightDGModuleModel A) where
  inclusion : P ⟶ Q
  coordinates (a : A.Obj) (n : ℤ) :
    (Q.complex a).X n ≃ₗ[k] ((P.complex a).X n × CellTerm C a n)
  coordinate_inclusion (a : A.Obj) (n : ℤ) (x : (P.complex a).X n) :
    coordinates a n (inclusion.app a |>.f n x) = (x, 0)
  coordinate_d (a : A.Obj) (n : ℤ) (x : (Q.complex a).X n) :
    let y := coordinates a n x
    let z := coordinates a (n + 1) ((Q.complex a).d n (n + 1) x)
    z.1 = (P.complex a).d n (n + 1) y.1 + boundaryMap C a n y.2 ∧
      ∀ s, z.2 s = ((cells C s).complex a).d n (n + 1) (y.2 s)
  coordinate_act {a b : A.Obj} (m n q : ℤ) (h : m + n = q)
      (x : (Q.complex b).X m) (f : (A.hom a b).X n) :
    let y := coordinates b m x
    let z := coordinates a q (Q.act m n q h x f)
    z.1 = P.act m n q h y.1 f ∧ ∀ s, z.2 s = (cells C s).act m n q h (y.2 s) f

def Attachment.generator {C : CellFamily P I} (E : Attachment C Q) (s : I) :
    (Q.complex (C.object s)).X (C.degree s) :=
  (E.coordinates (C.object s) (C.degree s)).symm
    (0, summand (cells C) (C.object s) (C.degree s) s
      (SemiFree.generator (C.object s) (C.degree s)))

/-- Countable semi-free filtration, with an independent universe for the cell sets.
Stage zero denotes the zero module before the first attachment. -/
structure Presentation (M : RightDGModuleModel A) where
  stage : ℕ → RightDGModuleModel A
  bottom (a : A.Obj) (n : ℤ) (x : ((stage 0).complex a).X n) : x = 0
  index : ℕ → Type j
  family (l : ℕ) : CellFamily (stage l) (index l)
  extension (l : ℕ) : Attachment (family l) (stage (l + 1))
  into (l : ℕ) : stage l ⟶ M
  compatible (l : ℕ) : (extension l).inclusion ≫ into (l + 1) = into l
  injective (l : ℕ) (a : A.Obj) (n : ℤ) :
    Function.Injective ((into l).app a |>.f n)
  exhaustive (a : A.Obj) (n : ℤ) (x : (M.complex a).X n) :
    ∃ l y, ((into l).app a).f n y = x

/-- The canonical size for a semi-free presentation of the original module.
Arbitrary-index presentations can be reduced to this size by deleting zero cells
and using the distinct named generators to bound the size of each remaining set. -/
def semiFree (M : RightDGModuleModel A) : Prop :=
  Nonempty (Presentation.{u,v,w,max v w} M)

def finiteCell (M : RightDGModuleModel A) : Prop :=
  ∃ F : Presentation.{u,v,w,max v w} M, Finite (Σ l, F.index l)

abbrev strictSum := @StrictSum
abbrev cellFamily := @CellFamily
abbrev attachment := @Attachment
abbrev presentation := @Presentation

section BindingTypes

set_option linter.checkUnivs false

def StrictSumType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} {I : Type j},
    (I → RightDGModuleModel A) → RightDGModuleModel A → Type (max v w j)

def CellFamilyType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    RightDGModuleModel A → Type j → Type (max v w j)

def AttachmentType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} {P : RightDGModuleModel A},
    CellFamily P I → RightDGModuleModel A → Type (max v w j)

def PresentationType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    RightDGModuleModel A → Type (max u w (v + 1) (j + 1))

def AttachmentGeneratorType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} {P Q : RightDGModuleModel A} {C : CellFamily P I}
    (_ : Attachment C Q) (s : I), (Q.complex (C.object s)).X (C.degree s)

end BindingTypes

end

end Specs.DerivedFormalization.DG.IndexedSemiFree
