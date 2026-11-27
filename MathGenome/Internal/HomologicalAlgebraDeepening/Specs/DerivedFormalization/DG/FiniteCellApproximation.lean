import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CellReindex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CompactRepresentables
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

open CategoryTheory CategoryTheory.Limits

universe u v w j t z

namespace Specs.DerivedFormalization.DG.FiniteCellApproximation

open _root_.DerivedFormalization
open IndexedSemiFree CellReindex

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {M : RightDGModuleModel A} {F : Presentation.{u,v,w,j} M}

/-- Cells of the given presentation, with their original labels. -/
abbrev CellIndex (F : Presentation.{u,v,w,j} M) := Σ l : ℕ, F.index l

/-- The actual attaching cycle, embedded in the module whose filtration is given. -/
def attachmentValue (F : Presentation.{u,v,w,j} M) (s : CellIndex F) :
    (M.complex ((F.family s.1).object s.2)).X ((F.family s.1).degree s.2 + 1) :=
  ((F.into s.1).app ((F.family s.1).object s.2)).f
    ((F.family s.1).degree s.2 + 1) ((F.family s.1).boundary s.2)

/-- The support of the differential of a generator in the graded cell coordinates. -/
def differentialSupport (D : GradedDecomposition F) (s : CellIndex F) : Set (CellIndex F) :=
  {r | D.coordinates _ _ (attachmentValue F s) r ≠ 0}

/-- A finite choice of cells that contains the differential supports of its cells. -/
def IsClosed (D : GradedDecomposition F) (E : Finset (CellIndex F)) : Prop :=
  ∀ s ∈ E, ∀ r ∈ differentialSupport D s, r ∈ E

/-- The finite closed subsets of the cells occurring at stage `N`, ordered by inclusion. -/
abbrev ClosedCells (D : GradedDecomposition F) (N : ℕ) :=
  {E : Finset (CellIndex F) // IsClosed D E ∧ ∀ s ∈ E, s.1 < N}

/-- Membership in the graded submodule spanned by the selected cells. -/
def IsSupported (D : GradedDecomposition F) (E : Finset (CellIndex F))
    (a : A.Obj) (n : ℤ) (x : (M.complex a).X n) : Prop :=
  ∀ s, s ∉ E → D.coordinates a n x s = 0

/-- Finite selections admit finite closed enlargements at the same stage,
and finite closed subsets are a nonempty directed poset under inclusion. -/
def ClosedCellsDirected : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M)
    (D : GradedDecomposition F) (N : ℕ),
    (∀ E : Finset (CellIndex F), (∀ s ∈ E, s.1 < N) →
      ∃ U : ClosedCells D N, E ⊆ U.val) ∧
    Nonempty (ClosedCells D N) ∧
    Directed (· ≤ ·) (fun E : ClosedCells D N => E)

/-- The actual dg submodules at a stage, with their canonical inclusions.
The image condition identifies each term with the supported elements in the
given graded coordinates, including when the presentation's index universe is large. -/
structure StageSubmodules (D : GradedDecomposition F) (N : ℕ) where
  diagram : ClosedCells D N ⥤ RightDGModuleModel A
  inclusion : diagram ⟶ (Functor.const _).obj (F.stage N)
  injective (E : ClosedCells D N) (a : A.Obj) (n : ℤ) :
    Function.Injective (((inclusion.app E).app a).f n)
  image (E : ClosedCells D N) (a : A.Obj) (n : ℤ) (x : ((F.stage N).complex a).X n) :
    (∃ y, ((inclusion.app E).app a).f n y = x) ↔
      IsSupported D E.val a n (((F.into N).app a).f n x)

def StageSubmodulesExist : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M)
    (D : GradedDecomposition F) (N : ℕ),
    ∃ S : StageSubmodules D N, ∀ E, IndexedSemiFree.finiteCell (S.diagram.obj E)

/-- The additive Hom diagram from a compact object to the shifted finite
stage submodules, using the inclusions into the fixed stage for its cocone. -/
def homCocone (D : GradedDecomposition F) {N : ℕ} (S : StageSubmodules D N)
    {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
    (Q : RightDGModuleModel A ⥤ C) (X : C) (n : ℤ) :
    Cocone (S.diagram ⋙ Q ⋙ shiftFunctor C n ⋙ preadditiveCoyoneda.obj ⟨X⟩) :=
  (Q ⋙ shiftFunctor C n ⋙ preadditiveCoyoneda.obj ⟨X⟩).mapCocone
    { pt := F.stage N, ι := S.inclusion }

section DerivedComparison

variable {B : DGCategoryModel.{u,z,w} k}

/-- Comparison for a specified strict input to the localization. The shift on
the localization agrees, on these representatives, with the signed shift in
the homotopy category. -/
def StageHomComparisonAt (U : RightDGModuleModel A ⥤ RightDGModuleModel B)
    (h : Derived.HomotopyCategoryLaws B) : Prop :=
  let K := HomComplex.homotopyCategory B
  let R := Derived.derivedCategory B h
  letI := Derived.homotopyCategory B h
  letI := DerivedKProjective.derivedCategoryInstance B h
  let Q : K ⥤ R := Derived.quotient B h
  ∃ (T : RightDGModuleModel B ⥤ K) (SR : HasShift R ℤ) (PR : Preadditive R),
    letI := SR
    letI := PR
    (∀ M : RightDGModuleModel B, T.obj M = M) ∧
    (∀ {M N : RightDGModuleModel B} (f : M ⟶ N),
      HEq (T.map f) (HomComplex.homotopyClass f)) ∧
    CompactRepresentables.LocalizationMapAdditive h PR ∧
    (∃ SK : HasShift K ℤ,
      letI := SK
      (∀ (M : K) (n : ℤ), (shiftFunctor K n).obj M = ShiftCone.shift M n) ∧
      (∀ {M N : RightDGModuleModel B} (n : ℤ) (f : M ⟶ N),
        HEq ((shiftFunctor K n).map (show @Quiver.Hom K _ M N from HomComplex.homotopyClass f))
          (HomComplex.homotopyClass (ShiftCone.shiftMap n f))) ∧
      Nonempty (Q.CommShift ℤ)) ∧
    ∀ (X : R), CompactRepresentables.IsCompact.{j,_,_} X →
      ∀ {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M)
        (D : GradedDecomposition F) (N : ℕ) (S : StageSubmodules D N),
        ∀ n : ℤ, Nonempty (IsColimit (homCocone D S (C := R) (U ⋙ T ⋙ Q) X n))

end DerivedComparison

/-- For the native localization at an adequate bound and the common ambient
localization of an arbitrary original category, the inclusions of finite
closed cell submodules induce the canonical colimit of shifted Hom groups. -/
def StageHomComparison : Prop :=
  (∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w,w} k)
    (h : Derived.HomotopyCategoryLaws A),
    StageHomComparisonAt.{u,max v w,w,j,max v w} (𝟭 (RightDGModuleModel A)) h) ∧
  (∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (AmbientDerived.category.{u,v,w,t} A)),
    StageHomComparisonAt.{u,v,w,j,max v w t} (AmbientDerived.strictInput.{u,v,w,t} A) h)

end

end Specs.DerivedFormalization.DG.FiniteCellApproximation
