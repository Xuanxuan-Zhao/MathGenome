import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.EdgesAndFiveTerms

/-! HA-G05, notes/002/advanced-homological-algebra.tex:2705–2778.
The object specialization, canonical derived edges, filtered edge realization
and low-degree exactness are specified independently. Indices in RowDiagram
are (filtration degree, total degree), and page 0 denotes the source E₂. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₃} C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The actual HA-G04 sequence evaluated on stalk objects, as a functor. -/
abbrev objectSequence (P : Package F G) : A ⥤ RowDiagram C :=
  DerivedCategory.Plus.singleFunctor A 0 ⋙ sequence F G P.row

/-- Natural object-case second page, first-quadrant vanishing and abutment.
The complete pages, next-page maps, finite filtration and convergence are
retained from P, rather than replaced by an unrelated sequence. -/
structure ObjectCase (P : Package F G) where
  secondIso : ∀ p q : ℕ,
    objectSequence F G P ⋙ pageEval 0 (p : ℤ) ((p : ℤ)+(q : ℤ)) ≅
      rightValue F q ⋙ rightValue G p
  secondIso_eq : ∀ p q : ℕ, secondIso p q =
    associator _ _ _ ≪≫
      isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0) (P.secondIso p (q : ℤ)) ≪≫
      (associator (DerivedCategory.Plus.singleFunctor A 0)
        (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B (q : ℤ))
        (rightValue G p)).symm
  targetIso : ∀ n : ℕ,
    objectSequence F G P ⋙ targetEval (n : ℤ) ≅ rightValue (F ⋙ G) n
  targetIso_eq : ∀ n : ℕ, targetIso n =
    isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0) (P.targetIso (n : ℤ))
  quadrant : ∀ X : A, ∀ p n : ℤ, p < 0 ∨ n < p →
    IsZero (((objectSequence F G P).obj X).page 0 p n)

namespace Specs
/-- Right derivation preserves every cohomological lower bound. This is a
consequence of the same-bound injective representative theorem, and is used
for the object quadrant and the truncation edge comparison. -/
def PreservesLowerBounds : Prop :=
  ∀ (A : Type u₁) (B : Type u₂) [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (Y : DerivedCategory.Plus A) (a : ℤ),
    Y.IsGE a → (F.rightDerivedFunctorPlus.obj Y).IsGE a

/-- HA-G05 object specialization for every supplied HA-G04 package. -/
def ObjectStatement : Prop :=
  ∀ (A : Type u₁) (B : Type u₂) (C : Type u₃)
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    [HasDerivedCategory.{w₃} C] [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (P : Package F G), Nonempty (ObjectCase F G P)
end Specs
end AdvancedHomologicalAlgebra.GrothendieckEdges

end
noncomputable section
universe gu gv
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.G05FilteredEdges
open HypercohomologyDerivedNaturality GrothendieckSpectralSequence
variable {C : Type gu} [Category.{gv} C] [Abelian C]
@[ext] structure EdgeData (X : RowDiagram C) where
  row : ∀ n : ℕ, X.page 0 (n : ℤ) (n : ℤ) ⟶ X.target (n : ℤ)
  column : ∀ n : ℕ, X.target (n : ℤ) ⟶ X.page 0 0 (n : ℤ)

abbrev transgression (X : RowDiagram C) : X.page 0 0 1 ⟶ X.page 0 2 2 :=
  X.differential 0 0 1

structure FiveTermData {X : RowDiagram C} (E : EdgeData X) : Prop where
  row_mono : Mono (E.row 1)
  row_column : E.row 1 ≫ E.column 1 = 0
  column_d : E.column 1 ≫ transgression X = 0
  d_row : transgression X ≫ E.row 2 = 0
  exact_H1 : (ShortComplex.mk (E.row 1) (E.column 1) row_column).Exact
  exact_E01 : (ShortComplex.mk (E.column 1) (transgression X) column_d).Exact
  exact_E20 : (ShortComplex.mk (transgression X) (E.row 2) d_row).Exact


/-- Simultaneous naturality of both edge maps for a diagram morphism. -/
structure EdgeMap {X Y : RowDiagram C} (f : X ⟶ Y) (E : EdgeData X) (E' : EdgeData Y) : Prop where
  row : ∀ n : ℕ, f.page 0 n n ≫ E'.row n = E.row n ≫ f.target n
  column : ∀ n : ℕ, f.target n ≫ E'.column n = E.column n ≫ f.page 0 0 n


abbrev FirstQuadrant (X : RowDiagram C) : Prop :=
  ∀ p n : ℤ, p < 0 ∨ n < p → IsZero (X.page 0 p n)


end AdvancedHomologicalAlgebra.G05FilteredEdges

noncomputable section G05Statement

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality CartanEilenbergData
open G05FilteredEdges FiniteFiltrationConvergence
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₃} C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The ordinary degree-zero stalk, as a bounded below complex. -/
def stalkComplex (A : Type u₁) [Category.{v₁} A] [Abelian A] :
    A ⥤ CochainComplex.Plus A :=
  (CochainComplex.plus A).lift (CochainComplex.singleFunctor A 0)
    (fun _ => ⟨0, inferInstance⟩)

/-- The canonical identification of a mapped stalk with the stalk of its value. -/
def mappedStalkIso : F ⋙ DerivedCategory.Plus.singleFunctor B 0 ≅
    stalkComplex A ⋙ F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q := by
  apply ((FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight A).preimageIso
  change F ⋙ DerivedCategory.singleFunctor B 0 ≅
    CochainComplex.singleFunctor A 0 ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  exact isoWhiskerLeft F (DerivedCategory.singleFunctorIsoCompQ B 0) ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).symm _ ≪≫
    associator _ _ _

/-- The canonical map F(X)[0] → RF(X[0]), from the actual derived unit. -/
def stalkToDerived : F ⋙ DerivedCategory.Plus.singleFunctor B 0 ⟶
    DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus :=
  (mappedStalkIso F).hom ≫ whiskerLeft (stalkComplex A) F.rightDerivedFunctorPlusUnit



/-- The canonical degree-zero comparison induced by the derived unit. -/
def degreeZeroUnit : F ⟶ rightValue F 0 :=
  (isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0)).inv ≫
    whiskerRight (stalkToDerived F) (DerivedCategory.Plus.homologyFunctor B 0)

/-- The derived first edge, with the canonical inverse composition comparison. -/
def derivedFirstEdge (P : Package F G) (n : ℕ) :
    F ⋙ rightValue G n ⟶ rightValue (F ⋙ G) n := by
  letI := P.comparison_isIso
  letI : IsIso (Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G) :=
    NatIso.isIso_of_isIso_app _
  exact whiskerRight (stalkToDerived F)
      (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (n : ℤ)) ≫
    whiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
      (whiskerRight (asIso
        (Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G)).inv
        (DerivedCategory.Plus.homologyFunctor C (n : ℤ)))


/-- Shift the degree-`n` stalk to degree zero before computing cohomology. -/
def shiftedStalkValueIso (n : ℤ) :
    DerivedCategory.Plus.singleFunctor B n ⋙ G.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor C n ≅ rightValue G 0 := by
  by_cases h : n = 0
  · subst n
    exact Iso.refl _
  · let R := G.rightDerivedFunctorPlus
    let H := DerivedCategory.Plus.homologyFunctor C 0
    let S := DerivedCategory.Plus.singleFunctor B n
    change S ⋙ R ⋙ H.shift n ≅ rightValue G 0
    exact isoWhiskerLeft S (isoWhiskerLeft R (H.isoShift n).symm) ≪≫
      isoWhiskerRight (isoWhiskerLeft S (R.commShiftIso n).symm) H ≪≫
      isoWhiskerRight (isoWhiskerRight
        ((DerivedCategory.Plus.singleFunctors B).shiftIso n 0 n (by omega)) R) H

/-- The normalized data that make the truncation span a map on derived cohomology. -/
structure ColumnTruncation (n : ℤ) where
  lower : DerivedCategory.Plus.TStructure.t.truncLE n ⋙ G.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor C n ≅
    G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n
  lower_hom : lower.hom = whiskerRight (DerivedCategory.Plus.TStructure.t.truncLEι n)
    (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n)
  point : DerivedCategory.Plus.TStructure.t.truncLE n ⋙
      DerivedCategory.Plus.TStructure.t.truncGE n ≅
    DerivedCategory.Plus.homologyFunctor B n ⋙ DerivedCategory.Plus.singleFunctor B n
  point_normalization : ∀ Y : DerivedCategory.Plus B,
    (DerivedCategory.Plus.homologyFunctor B n).map
      ((DerivedCategory.Plus.TStructure.t.truncGEπ n).app
          ((DerivedCategory.Plus.TStructure.t.truncLE n).obj Y) ≫ point.hom.app Y) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app
        ((DerivedCategory.Plus.homologyFunctor B n).obj Y) =
    (DerivedCategory.Plus.homologyFunctor B n).map
      ((DerivedCategory.Plus.TStructure.t.truncLEι n).app Y)

/-- Apply `RG` and cohomology to the normalized truncation span. -/
def ColumnTruncation.edge {n : ℤ} (T : ColumnTruncation G n) (e₀ : rightValue G 0 ≅ G) :
    G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n ⟶
    DerivedCategory.Plus.homologyFunctor B n ⋙ G :=
  T.lower.inv ≫
    whiskerRight (whiskerLeft (DerivedCategory.Plus.TStructure.t.truncLE n)
      (DerivedCategory.Plus.TStructure.t.truncGEπ n) ≫ T.point.hom)
      (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n) ≫
    (associator _ _ _).hom ≫
    (isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor B n)
      (shiftedStalkValueIso G n ≪≫ e₀)).hom

/-- The column edge viewed on the classical composite derived functor. -/
def classicalColumn {n : ℕ} (T : ColumnTruncation G (n : ℤ)) (e₀ : rightValue G 0 ≅ G) :
    rightValue (F ⋙ G) n ⟶ rightValue F n ⋙ G :=
  whiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
    (whiskerRight
      (_root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G)
      (DerivedCategory.Plus.homologyFunctor C (n : ℤ))) ≫
    whiskerLeft (DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus)
      (T.edge G e₀)

/-- The complex chosen by essential surjectivity of the quotient. -/
noncomputable def modelComplex (Y : DerivedCategory.Plus B) : CochainComplex.Plus B :=
  letI := Localization.essSurj (DerivedCategory.Plus.Q (C := B))
    (CochainComplex.Plus.quasiIso B)
  DerivedCategory.Plus.Q.objPreimage Y

/-- The actual row model used in the localized sequence. -/
def modelData (R : DerivedRow G) (Y : DerivedCategory.Plus B) :
    Data G (modelComplex Y) (R.resolution (modelComplex Y)) :=
  R.system.data _ _

/-- Simultaneous identification of pages and filtered cohomology with the row model. -/
def modelIso (R : DerivedRow G) (Y : DerivedCategory.Plus B) :
    R.derived.obj Y ≅ diagram G (modelData G R Y) := by
  letI := Localization.essSurj (DerivedCategory.Plus.Q (C := B))
    (CochainComplex.Plus.quasiIso B)
  exact R.derived.mapIso (DerivedCategory.Plus.Q.objObjPreimageIso Y).symm ≪≫
    R.factors.app (modelComplex Y) ≪≫ eqToIso (R.obj_eq _)

/-- Transport of the two filtered edge equations through the model presentation. -/
structure FilteredEdgesOn (R : DerivedRow G) (Y : DerivedCategory.Plus B)
    (E : EdgeData (R.derived.obj Y)) : Prop where
  row : ∀ n : ℕ,
    let M := modelData G R Y
    let e := modelIso G R Y
    (closedToPage M.filtration M.pages 2 (n : ℤ) (n : ℤ) ≫ e.inv.page 0 n n) ≫ E.row n =
      EdgesAndFiveTerms.ambientClass M.filtration n n ≫ (M.targetIso n).hom ≫ e.inv.target n
  column : ∀ n : ℕ,
    let M := modelData G R Y
    let e := modelIso G R Y
    ((EdgesAndFiveTerms.ambientClass M.filtration 0 n ≫ (M.targetIso n).hom) ≫
        e.inv.target n) ≫ E.column n =
      closedToPage M.filtration M.pages 2 0 n ≫ e.inv.page 0 0 n

/-- Exactness at the four terms following the initial zero. -/
structure ClassicalFiveTerms {X₁ X₂ X₃ X₄ X₅ : C}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (h : X₄ ⟶ X₅) : Prop where
  mono : Mono f
  fg : f ≫ g = 0
  gd : g ≫ d = 0
  dh : d ≫ h = 0
  exact_f_g : (ShortComplex.mk f g fg).Exact
  exact_g_d : (ShortComplex.mk g d gd).Exact
  exact_d_h : (ShortComplex.mk d h dh).Exact

/-- Reindex the bottom row by total degree. -/
def rowIndexIso (P : Package F G) (n : ℕ) :
    objectSequence F G P ⋙ pageEval 0 (n : ℤ) ((n : ℤ) + 0) ≅
      objectSequence F G P ⋙ pageEval 0 (n : ℤ) (n : ℤ) :=
  eqToIso (by rw [add_zero])

/-- Reindex the left column by total degree. -/
def columnIndexIso (P : Package F G) (n : ℕ) :
    objectSequence F G P ⋙ pageEval 0 0 (0 + (n : ℤ)) ≅
      objectSequence F G P ⋙ pageEval 0 0 (n : ℤ) :=
  eqToIso (by rw [zero_add])

/-- All object-case identifications and edges of the Grothendieck sequence. -/
structure ObjectEdges (P : Package F G) where
  objectCase : ObjectCase F G P
  target_identification : ∀ n : ℕ, objectCase.targetIso n =
    isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0) (P.targetIso (n : ℤ))
  degreeZeroF : F ≅ rightValue F 0
  degreeZeroF_hom : degreeZeroF.hom = degreeZeroUnit F
  degreeZero : rightValue G 0 ≅ G
  degreeZero_hom : degreeZero.inv = degreeZeroUnit G
  zeroTruncation : F ⋙ DerivedCategory.Plus.singleFunctor B 0 ≅
    DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.TStructure.t.truncLE 0
  zeroTruncation_hom : stalkToDerived F = zeroTruncation.hom ≫
    whiskerLeft (DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus)
      (DerivedCategory.Plus.TStructure.t.truncLEι 0)
  truncation : ∀ n : ℕ, ColumnTruncation G (n : ℤ)
  rowPage : ∀ n : ℕ, objectSequence F G P ⋙ pageEval 0 (n : ℤ) (n : ℤ) ≅ F ⋙ rightValue G n
  columnPage : ∀ n : ℕ,
    objectSequence F G P ⋙ pageEval 0 0 (n : ℤ) ≅ rightValue F n ⋙ G
  row_identification : ∀ n : ℕ, objectCase.secondIso n 0 =
    rowIndexIso F G P n ≪≫ rowPage n ≪≫ isoWhiskerRight degreeZeroF (rightValue G n)
  column_identification : ∀ n : ℕ, objectCase.secondIso 0 n =
    columnIndexIso F G P n ≪≫ columnPage n ≪≫
      isoWhiskerLeft (rightValue F n) degreeZero.symm
  filtered : ∀ X : A, EdgeData ((objectSequence F G P).obj X)
  filtered_formulas : ∀ X : A,
    FilteredEdgesOn G P.row
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))
      (filtered X)
  first_comparison : ∀ (n : ℕ) (X : A),
    (rowPage n).hom.app X ≫ (derivedFirstEdge F G P n).app X =
      (filtered X).row n ≫ (objectCase.targetIso n).hom.app X
  second_comparison : ∀ (n : ℕ) (X : A),
    (objectCase.targetIso n).hom.app X ≫
      (classicalColumn F G (truncation n) degreeZero).app X =
      (filtered X).column n ≫ (columnPage n).hom.app X
  fiveTerms : ∀ X : A,
    ClassicalFiveTerms
      ((derivedFirstEdge F G P 1).app X)
      ((classicalColumn F G (truncation 1) degreeZero).app X)
      ((columnPage 1).inv.app X ≫ transgression ((objectSequence F G P).obj X) ≫
        (rowPage 2).hom.app X)
      ((derivedFirstEdge F G P 2).app X)

namespace Specs

/-- HA-G05 under the hypotheses of HA-G04. -/
def FullStatement : Prop :=
  ∀ (A : Type u₁) (B : Type u₂) (C : Type u₃)
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G],
    (∀ I : A, Injective I →
      _root_.Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue G (F.obj I)) →
    ∃ P : Package F G, Nonempty (ObjectEdges F G P)

end Specs
end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05Statement
