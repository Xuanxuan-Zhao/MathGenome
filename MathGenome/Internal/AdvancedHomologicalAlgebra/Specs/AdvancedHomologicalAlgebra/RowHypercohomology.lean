import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergTotalization
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexFirstPages
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexConvergence

/-! HA-G03-Row, notes/002/advanced-homological-algebra.tex:2565–2645.
Independent specifications for the actual row spectral sequence, its canonical
split-row comparison and signs, E₂ computation, finite derived target filtration,
and naturality and independence. Derived-category descent is allocated to HA-G03.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
namespace AdvancedHomologicalAlgebra.RowHypercohomology
open CartanEilenbergData CartanEilenbergTotalization

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]

/-- The simultaneous horizontal-cohomology resolution, with its actual
vertical differential induced from the bicomplex. -/
abbrev cohomologyColumn {K : CochainComplex A ℤ} (R : ResolutionData K) (q : ℤ) :=
  invariantColumn R.bicomplex (HomologicalComplex.homologyFunctor A (.up ℤ) q)

abbrev mappedCohomologyColumn (F : A ⥤ B) [F.Additive]
    {K : CochainComplex A ℤ} (R : ResolutionData K) (q : ℤ) :=
  invariantColumn ((mapDouble F).obj R.bicomplex)
    (HomologicalComplex.homologyFunctor B (.up ℤ) q)

abbrev cohomologyColumnMap {I J : DoubleComplex A} (a : I ⟶ J)
    (q : ℤ) : invariantColumn I (HomologicalComplex.homologyFunctor A (.up ℤ) q) ⟶
      invariantColumn J (HomologicalComplex.homologyFunctor A (.up ℤ) q) :=
  ((HomologicalComplex.homologyFunctor A (.up ℤ) q).mapHomologicalComplex
    (.up ℤ)).map (CartanEilenbergComparison.rowMap a)

/-- All integer horizontal degrees, including zero rows in negative vertical degree. -/
structure SplitRowComparison (F : A ⥤ B) [F.Additive] where
  iso : ∀ {K : CochainComplex A ℤ} (R : ResolutionData K) (p q : ℤ),
    (((mapDouble F).obj R.bicomplex).flip.X p).homology q ≅
      F.obj ((R.bicomplex.flip.X p).homology q)
  on_cycles : ∀ {K : CochainComplex A ℤ} (R : ResolutionData K) (p q : ℤ),
    let J := R.bicomplex.flip.X p
    let FJ := ((mapDouble F).obj R.bicomplex).flip.X p
    FJ.liftCycles (F.map (J.iCycles q)) (q + 1) (by simp) (by
      change F.map (J.iCycles q) ≫ F.map (J.d q (q + 1)) = 0
      rw [← F.map_comp, J.iCycles_d, F.map_zero]) ≫
        FJ.homologyπ q ≫ (iso R p q).hom =
      F.map (J.homologyπ q)
  naturality : ∀ {K L : CochainComplex A ℤ} (R : ResolutionData K)
    (S : ResolutionData L) (p q : ℤ)
    (a : R.bicomplex.flip.X p ⟶ S.bicomplex.flip.X p),
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map a) q ≫
        (iso S p q).hom =
      (iso R p q).hom ≫ F.map (HomologicalComplex.homologyMap a q)

section Transport
variable {H H' : A}
def transportPiece (e : H ≅ H') (P : Subobject H) : Subobject H' :=
  (Subobject.map e.hom).obj P
lemma transportPiece_eq_mk (e : H ≅ H') (P : Subobject H) :
    transportPiece e P = Subobject.mk (P.arrow ≫ e.hom) := by
  conv_lhs => rw [transportPiece, ← Subobject.mk_arrow P, Subobject.map_mk]
def transportStepIso (e : H ≅ H') (P : Subobject H) :
    (P : A) ≅ (transportPiece e P : A) :=
  Subobject.isoOfMkEq _ _ (transportPiece_eq_mk e P).symm
@[reassoc (attr := simp)]
lemma transportStepIso_arrow (e : H ≅ H') (P : Subobject H) :
    (transportStepIso e P).hom ≫ (transportPiece e P).arrow = P.arrow ≫ e.hom := by
  simp [transportStepIso, Subobject.isoOfMkEq]
lemma transportPiece_mono (e : H ≅ H') {P Q : Subobject H} (h : P ≤ Q) :
    transportPiece e P ≤ transportPiece e Q :=
  (Subobject.mapIsoToOrderIso e).monotone h
@[simp] lemma transportPiece_top (e : H ≅ H') : transportPiece e ⊤ = ⊤ :=
  (Subobject.mapIsoToOrderIso e).map_top
@[simp] lemma transportPiece_bot (e : H ≅ H') : transportPiece e ⊥ = ⊥ :=
  (Subobject.mapIsoToOrderIso e).map_bot
lemma transportStepIso_comm (e : H ≅ H') {P Q : Subobject H} (h : P ≤ Q) :
    Subobject.ofLE P Q h ≫ (transportStepIso e Q).hom =
      (transportStepIso e P).hom ≫
        Subobject.ofLE (transportPiece e P) (transportPiece e Q) (transportPiece_mono e h) := by
  apply (cancel_mono (transportPiece e Q).arrow).1
  simp [Category.assoc]
def transportGradedIso (e : H ≅ H') {P Q : Subobject H} (h : P ≤ Q) :
    cokernel (Subobject.ofLE P Q h) ≅
      cokernel (Subobject.ofLE (transportPiece e P) (transportPiece e Q)
        (transportPiece_mono e h)) :=
  cokernel.mapIso _ _ (transportStepIso e P) (transportStepIso e Q) (transportStepIso_comm e h)
@[reassoc (attr := simp)]
lemma transportGradedIso_π (e : H ≅ H') {P Q : Subobject H} (h : P ≤ Q) :
    cokernel.π (Subobject.ofLE P Q h) ≫ (transportGradedIso e h).hom =
      (transportStepIso e Q).hom ≫ cokernel.π _ := by
  simp [transportGradedIso]
end Transport

section SignedPages
open DoubleComplexFirstPages
variable (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ} (R : ResolutionData K)
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
  (D : F03Specs.PageData Fr)

abbrev mappedOriginalColumn (q : ℤ) :=
  (F.mapHomologicalComplex (.up ℤ)).obj (cohomologyColumn R q)

abbrev rawFirstIso
    (row : RowData ((mapDouble F).obj R.bicomplex) Fr hFr D)
    (split : SplitRowComparison F) (p q : ℤ) :
    page Fr D 1 p q ≅ (mappedOriginalColumn F R q).X p :=
  row.firstIso p q ≪≫ split.iso R p q

abbrev signedFirstIso
    (row : RowData ((mapDouble F).obj R.bicomplex) Fr hFr D)
    (split : SplitRowComparison F) (p q : ℤ) :
    page Fr D 1 p q ≅ (mappedOriginalColumn F R q).X p :=
  (p * q).negOnePow • rawFirstIso F R Fr hFr D row split p q

/-- The raw and signed comparisons use the same split row cohomology map
and the representatives of the fixed filtration. -/
structure FirstPageComputation where
  row : RowData ((mapDouble F).obj R.bicomplex) Fr hFr D
  split : SplitRowComparison F
  raw_d : ∀ p q, firstDifferential Fr D p q ≫
      (rawFirstIso F R Fr hFr D row split (p + 1) q).hom =
    (rawFirstIso F R Fr hFr D row split p q).hom ≫
      ((ComplexShape.up ℤ).ε q • (mappedOriginalColumn F R q).d p (p + 1))
  signed_d : ∀ p q, D.differential 1 (by omega) p (p + q) ≫
      eqToHom (congrArg (PageCohomology.object Fr D 1 (p + 1))
        (show p + q + 1 = p + 1 + q by omega)) ≫
      (signedFirstIso F R Fr hFr D row split (p + 1) q).hom =
    (signedFirstIso F R Fr hFr D row split p q).hom ≫
      (mappedOriginalColumn F R q).d p (p + 1)

  signedShortComplex : ∀ a q : ℤ,
    PageCohomology.shortComplex Fr D 1 (by omega) a (a + q) ≅
      (mappedOriginalColumn F R q).sc' a (a + 1) (a + 1 + 1)
  signedShortComplex_left : ∀ a q, (signedShortComplex a q).hom.τ₁ =
    (signedFirstIso F R Fr hFr D row split a q).hom
  signedShortComplex_middle : ∀ a q, (signedShortComplex a q).hom.τ₂ =
    eqToHom (congrArg (PageCohomology.object Fr D 1 (a + 1))
      (show a + q + 1 = a + 1 + q by omega)) ≫
        (signedFirstIso F R Fr hFr D row split (a + 1) q).hom
  signedShortComplex_right : ∀ a q, (signedShortComplex a q).hom.τ₃ =
    eqToHom (congrArg (PageCohomology.object Fr D 1 (a + 1 + 1))
      (show a + q + 1 + 1 = a + 1 + 1 + q by omega)) ≫
        (signedFirstIso F R Fr hFr D row split (a + 1 + 1) q).hom

/-- Second page obtained by taking homology of the signed first-page map. -/
def FirstPageComputation.secondPageIso (M : FirstPageComputation F R Fr hFr D)
    (N : PageCohomology.Data Fr D) (p q : ℤ) :
    page Fr D 2 p q ≅ (mappedOriginalColumn F R q).homology p := by
  let J := mappedOriginalColumn F R q
  let a := p - 1
  have ha : a + 1 = p := by dsimp [a]; omega
  have hn : a + q + 1 = p + q := by omega
  exact eqToIso (congrArg₂ (PageCohomology.object Fr D 2) ha.symm hn.symm) ≪≫
    N.nextIso 1 (by omega) a (a + q) ≪≫
    ShortComplex.homologyMapIso (M.signedShortComplex a q) ≪≫
    (J.homologyIsoSc' a (a + 1) (a + 1 + 1) (by simp) (by simp)).symm ≪≫
    eqToIso (congrArg (fun n : ℤ => (mappedOriginalColumn F R q).homology n) ha)

end SignedPages

namespace Specs
def SplitRows : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F],
  Nonempty (SplitRowComparison F)

/-- The first-page comparisons form an isomorphism of vertical complexes. -/
def InvariantColumns : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F],
  ∃ e : ∀ {K : CochainComplex A ℤ} (R : ResolutionData K) (q : ℤ),
      mappedCohomologyColumn F R q ≅
        (F.mapHomologicalComplex (.up ℤ)).obj (cohomologyColumn R q),
    ∀ {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
      (a : R.bicomplex ⟶ S.bicomplex) (q : ℤ),
      cohomologyColumnMap ((mapDouble F).map a) q ≫ (e S q).hom =
        (e R q).hom ≫ (F.mapHomologicalComplex (.up ℤ)).map (cohomologyColumnMap a q)

/-- The raw signs and signed first-page comparison for every row model. -/
def RowPages : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  {K : CochainComplex A ℤ} (R : ResolutionData K)
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
  (D : F03Specs.PageData Fr),
  ∃ M : FirstPageComputation F R Fr hFr D, ∃ (N : PageCohomology.Data Fr D)
    (second : ∀ p q, DoubleComplexFirstPages.page Fr D 2 p q ≅
      (mappedOriginalColumn F R q).homology p),
    ∀ p q, second p q = M.secondPageIso F R Fr hFr D N p q

end Specs
end AdvancedHomologicalAlgebra.RowHypercohomology

universe w w'
namespace AdvancedHomologicalAlgebra.RowHypercohomology
open CartanEilenbergData CartanEilenbergTotalization
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]

/-- Classical derived values, with integer indices. At a natural index this
is definitionally the accepted `ClassicalDerivedValues.rightValue`. -/
abbrev rightValueInt (F : A ⥤ B) [F.Additive] (p : ℤ) : A ⥤ B :=
  DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor B p

/-- The actual degree-zero stalk whose image in D⁺ defines the classical value. -/
abbrev cohomologyStalk (X : A) : CochainComplex.Plus A :=
  ⟨(CochainComplex.singleFunctor A 0).obj X, ⟨0, inferInstance⟩⟩

variable (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ} (R : ResolutionData K)
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
  (D : F03Specs.PageData Fr)

/-- The chosen resolution is the simultaneous cohomology column with its
augmentation induced by the resolution map of horizontal complexes. -/
structure CohomologyColumnComputation (q : ℤ) where
  bounded : (CochainComplex.plus A) (cohomologyColumn R q)
  augmentation : cohomologyStalk (K.homology q) ⟶
    (⟨cohomologyColumn R q, bounded⟩ : CochainComplex.Plus A)
  augmentation_eq : augmentation.hom.f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (K.homology q)).hom ≫
      HomologicalComplex.homologyMap R.augmentation q
  model : ReplacementComparison F _ _ augmentation

def CohomologyColumnComputation.homologyIso {q : ℤ}
    (M : CohomologyColumnComputation F R q) (p : ℤ) :
    (rightValueInt F p).obj (K.homology q) ≅ (mappedOriginalColumn F R q).homology p :=
  M.model.homologyIso p

/-- Both stages of the second-page identification, with their maps fixed
by the first-page representatives and the simultaneous augmentation. -/
structure SecondPageComputation (N : PageCohomology.Data Fr D) where
  first : FirstPageComputation F R Fr hFr D
  column : ∀ q, CohomologyColumnComputation F R q

def SecondPageComputation.iso {N : PageCohomology.Data Fr D}
    (M : SecondPageComputation F R Fr hFr D N) (p q : ℤ) :
    DoubleComplexFirstPages.page Fr D 2 p q ≅ (rightValueInt F p).obj (K.homology q) :=
  M.first.secondPageIso F R Fr hFr D N p q ≪≫ ((M.column q).homologyIso F R p).symm

/-- The actual row pages compute the canonical derived values. The same
comparison family is natural for all augmented lifts between resolutions;
all maps here act on the fixed HA-F03 page quotients. -/
structure ComputedRowSystem (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] where
  secondIso : ∀ {K : CochainComplex A ℤ} (R : ResolutionData K)
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
    (D : F03Specs.PageData Fr) (p q : ℤ),
    DoubleComplexFirstPages.page Fr D 2 p q ≅ (rightValueInt F p).obj (K.homology q)
  canonical : ∀ {K : CochainComplex A ℤ} (R : ResolutionData K)
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
    (D : F03Specs.PageData Fr) (N : PageCohomology.Data Fr D),
    ∃ M : SecondPageComputation F R Fr hFr D N,
      ∀ p q, secondIso R Fr hFr D p q = M.iso F R Fr hFr D p q
  negative : ∀ {K : CochainComplex A ℤ} (R : ResolutionData K)
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
    (D : F03Specs.PageData Fr) (p q : ℤ), p < 0 →
    IsZero (DoubleComplexFirstPages.page Fr D 2 p q)
  naturality : ∀ {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
    (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj S.bicomplex) Prod.snd Gr)
    (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f a)
    (g : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex), Fr⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex), Gr⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E) (p q : ℤ),
    M.map 2 p (p+q) ≫ (secondIso S Gr hGr E p q).hom =
      (secondIso R Fr hFr D p q).hom ≫ (rightValueInt F p).map (HomologicalComplex.homologyMap f q)
  lift_independent : ∀ {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
    (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj S.bicomplex) Prod.snd Gr)
    (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr)
    (f : K ⟶ L) (a b : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f a)
    (hb : CartanEilenbergComparison.IsLift R S f b)
    (g h : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex), Fr⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex), Gr⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ))
    (hh : h.hom = HomologicalComplex₂.total.map ((mapDouble F).map b) (.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E)
    (N : FilteredPageFunctoriality.MapData h D E) (r : ℤ), 2 ≤ r →
    ∀ p n, M.map r p n = N.map r p n
  quasiIso_comparison : ∀ {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
    (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj S.bicomplex) Prod.snd Gr)
    (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr)
    (f : K ⟶ L) (hf : QuasiIso f)
    (a : R.bicomplex ⟶ S.bicomplex) (ha : CartanEilenbergComparison.IsLift R S f a)
    (g : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex), Fr⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex), Gr⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E) (r : ℤ), 2 ≤ r →
    ∀ p n, IsIso (M.map r p n)

namespace Specs
/-- Canonical second-page computation, negative-index vanishing, naturality,
lift independence on every page r ≥ 2, and comparison for quasi-isomorphisms. -/
def ComputedRows : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F], Nonempty (ComputedRowSystem F)
end Specs
end AdvancedHomologicalAlgebra.RowHypercohomology

namespace AdvancedHomologicalAlgebra.RowHypercohomology
open CartanEilenbergData CartanEilenbergTotalization
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]

/-- A full actual row spectral sequence: its Cartan--Eilenberg resolution,
finite row filtration, all page differentials and successive homologies,
convergence, and the classical second-page computation. -/
structure RowRealization (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) where
  resolution : ResolutionData K
  [hasTotal : resolution.bicomplex.HasTotal (.up ℤ)]
  [hasMappedTotal : ((mapDouble F).obj resolution.bicomplex).HasTotal (.up ℤ)]
  filtration : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj resolution.bicomplex))
  formula : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj resolution.bicomplex) Prod.snd filtration
  pages : F03Specs.PageData filtration
  pageCohomology : PageCohomology.Data filtration pages
  convergence : DoubleComplexConvergence.Converges filtration
  secondComparison : SecondPageComputation F resolution filtration formula pages pageCohomology
  secondIso : ∀ p q : ℤ, DoubleComplexFirstPages.page filtration pages 2 p q ≅
    (rightValueInt F p).obj (K.homology q)
  secondIso_eq : ∀ p q, secondIso p q =
    secondComparison.iso F resolution filtration formula pages p q

namespace Specs
/-- Every bounded-below complex admits the actual row realization. -/
def RowRealizationsExist : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  (K : CochainComplex A ℤ),
  (∃ L : ℤ, ∀ p : ℤ, p < L → IsZero (K.X p)) → Nonempty (RowRealization F K)
end Specs
end AdvancedHomologicalAlgebra.RowHypercohomology

namespace AdvancedHomologicalAlgebra.RowHypercohomology
open CartanEilenbergData CartanEilenbergTotalization
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]

attribute [instance] RowRealization.hasTotal RowRealization.hasMappedTotal

/-- One functorial system of the actual row pages for all resolutions and all
complexes. Maps are induced by every comparison lift from E₂ onward. -/
structure RowPageFunctorialSystem (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] where
  map : ∀ {K L : CochainComplex A ℤ} (R : RowRealization F K) (S : RowRealization F L)
    (f : K ⟶ L) (r p n : ℤ),
    PageCohomology.object R.filtration R.pages r p n ⟶
      PageCohomology.object S.filtration S.pages r p n
  induced : ∀ {K L : CochainComplex A ℤ} (R : RowRealization F K) (S : RowRealization F L)
    (f : K ⟶ L) (a : R.resolution.bicomplex ⟶ S.resolution.bicomplex),
    CartanEilenbergComparison.IsLift R.resolution S.resolution f a →
    ∃ g : FilteredMap
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.resolution.bicomplex), R.filtration⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.resolution.bicomplex), S.filtration⟩,
      g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ) ∧
      ∃ M : FilteredPageFunctoriality.MapData g R.pages S.pages,
        ∀ r : ℤ, 2 ≤ r → ∀ p n, map R S f r p n = M.map r p n
  map_id : ∀ {K : CochainComplex A ℤ} (R : RowRealization F K)
    (r : ℤ), 2 ≤ r → ∀ p n, map R R (𝟙 K) r p n = 𝟙 _
  map_comp : ∀ {K L T : CochainComplex A ℤ}
    (R : RowRealization F K) (S : RowRealization F L) (U : RowRealization F T)
    (f : K ⟶ L) (g : L ⟶ T) (r : ℤ), 2 ≤ r → ∀ p n,
    map R U (f ≫ g) r p n = map R S f r p n ≫ map S U g r p n
  differential_comm : ∀ {K L : CochainComplex A ℤ}
    (R : RowRealization F K) (S : RowRealization F L) (f : K ⟶ L)
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ),
    map R S f r p n ≫ S.pages.differential r (by omega) p n =
      R.pages.differential r (by omega) p n ≫ map R S f r (p+r) (n+1)
  second_naturality : ∀ (C : ComputedRowSystem F) {K L : CochainComplex A ℤ}
    (R : RowRealization F K) (S : RowRealization F L) (f : K ⟶ L) (p q : ℤ),
    map R S f 2 p (p+q) ≫ (C.secondIso S.resolution S.filtration S.formula S.pages p q).hom =
      (C.secondIso R.resolution R.filtration R.formula R.pages p q).hom ≫
        (rightValueInt F p).map (HomologicalComplex.homologyMap f q)
  resolution_naturality : ∀ {K L : CochainComplex A ℤ}
    (R R' : RowRealization F K) (S S' : RowRealization F L)
    (f : K ⟶ L) (r : ℤ), 2 ≤ r → ∀ p n,
    map R R' (𝟙 K) r p n ≫ map R' S' f r p n =
      map R S f r p n ≫ map S S' (𝟙 L) r p n
  homotopy_invariant : ∀ {K L : CochainComplex A ℤ}
    (R : RowRealization F K) (S : RowRealization F L)
    (f g : K ⟶ L), Homotopy f g →
    ∀ r : ℤ, 2 ≤ r → ∀ p n, map R S f r p n = map R S g r p n
  inverts_quasiIso : ∀ {K L : CochainComplex A ℤ}
    (R : RowRealization F K) (S : RowRealization F L) (f : K ⟶ L),
    QuasiIso f → ∀ r : ℤ, 2 ≤ r → ∀ p n, IsIso (map R S f r p n)
  inverse_comparisons : ∀ {K : CochainComplex A ℤ} (R S : RowRealization F K)
    (r : ℤ), 2 ≤ r → ∀ p n,
    ∃ e : PageCohomology.object R.filtration R.pages r p n ≅
        PageCohomology.object S.filtration S.pages r p n,
      e.hom = map R S (𝟙 K) r p n ∧ e.inv = map S R (𝟙 K) r p n

namespace Specs
/-- Uniform functoriality, lift independence, resolution independence and
quasi-isomorphism invariance of the actual row spectral sequence from E₂. -/
def PageFunctoriality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F], Nonempty (RowPageFunctorialSystem F)
end Specs
end AdvancedHomologicalAlgebra.RowHypercohomology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace AdvancedHomologicalAlgebra.RowHypercohomology
open CartanEilenbergData CartanEilenbergTotalization FiniteFiltrationConvergence
attribute [instance] RowRealization.hasTotal RowRealization.hasMappedTotal
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]

abbrev derivedCohomology (F : A ⥤ B) [F.Additive] (X : CochainComplex.Plus A) (n : ℤ) :=
  (DerivedCategory.Plus.homologyFunctor B n).obj
    (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj X))

abbrev derivedCohomologyMap (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex.Plus A} (f : X ⟶ Y) (n : ℤ) :=
  (DerivedCategory.Plus.homologyFunctor B n).map
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f))

/-- The comparison has the stated RF target; its image filtration below is
transported from the actual total-complex filtration. -/
structure DerivedRowTarget (F : A ⥤ B) [F.Additive] (X : CochainComplex.Plus A)
    (W : RowRealization F X.obj) where
  targetComparison : DerivedTotalComparison F X W.resolution
  comparison : ∀ n, derivedCohomology F X n ≅
    (DoubleTotalization.sumTotal ((mapDouble F).obj W.resolution.bicomplex)).homology n
  comparison_eq : ∀ n, comparison n = targetComparison.homologyIso n

namespace DerivedRowTarget
variable {F : A ⥤ B} [F.Additive] {X : CochainComplex.Plus A}
  {W : RowRealization F X.obj} (T : DerivedRowTarget F X W)

abbrev piece (p n : ℤ) : Subobject (derivedCohomology F X n) :=
  transportPiece (T.comparison n).symm (cohomologyPiece W.filtration p n)

lemma decreasing (p n : ℤ) : T.piece (p+1) n ≤ T.piece p n :=
  transportPiece_mono _ (cohomologyPiece_decreasing W.filtration p n)

abbrev graded (p n : ℤ) : B :=
  cokernel (Subobject.ofLE _ _ (T.decreasing p n))
end DerivedRowTarget

/-- Simultaneous finite filtered derived targets, with naturality on every
filtration step and the actual stable-page comparison. -/
structure DerivedTargetSystem (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] where
  target : ∀ (X : CochainComplex.Plus A) (W : RowRealization F X.obj), DerivedRowTarget F X W
  finite : ∀ (X : CochainComplex.Plus A) (W : RowRealization F X.obj) (n : ℤ), ∃ a b : ℤ,
    (∀ p, p ≤ a → (target X W).piece p n = ⊤) ∧
    (∀ p, b ≤ p → (target X W).piece p n = ⊥)
  limitIso : ∀ (X : CochainComplex.Plus A) (W : RowRealization F X.obj) (r p n : ℤ) (_h : Stabilized W.filtration r p n),
    PageCohomology.object W.filtration W.pages r p n ≅ (target X W).graded p n
  representative : ∀ (X : CochainComplex.Plus A) (W : RowRealization F X.obj) (r p n : ℤ) (h : Stabilized W.filtration r p n),
    closedToPage W.filtration W.pages r p n ≫ (limitIso X W r p n h).hom =
      closedClass W.filtration p n ≫
        (transportStepIso ((target X W).comparison n).symm
          (cohomologyPiece W.filtration p n)).hom ≫
        cokernel.π (Subobject.ofLE _ _ ((target X W).decreasing p n))
  stepMap : ∀ {X Y : CochainComplex.Plus A}
    (W : RowRealization F X.obj) (V : RowRealization F Y.obj) (f : X ⟶ Y) p n,
    ((target X W).piece p n : B) ⟶ ((target Y V).piece p n : B)
  step_arrow : ∀ {X Y : CochainComplex.Plus A}
    (W : RowRealization F X.obj) (V : RowRealization F Y.obj) (f : X ⟶ Y) p n,
    stepMap W V f p n ≫ ((target Y V).piece p n).arrow =
      ((target X W).piece p n).arrow ≫ derivedCohomologyMap F f n
  step_id : ∀ (X : CochainComplex.Plus A) (W : RowRealization F X.obj) (p n : ℤ), stepMap W W (𝟙 X) p n = 𝟙 _
  step_comp : ∀ {X Y Z : CochainComplex.Plus A}
    (W : RowRealization F X.obj) (V : RowRealization F Y.obj)
    (U : RowRealization F Z.obj) (f : X ⟶ Y) (g : Y ⟶ Z) p n,
    stepMap W U (f ≫ g) p n = stepMap W V f p n ≫ stepMap V U g p n
  step_comm : ∀ {X Y : CochainComplex.Plus A}
    (W : RowRealization F X.obj) (V : RowRealization F Y.obj) (f : X ⟶ Y) p n,
    Subobject.ofLE _ _ ((target X W).decreasing p n) ≫ stepMap W V f p n =
      stepMap W V f (p+1) n ≫ Subobject.ofLE _ _ ((target Y V).decreasing p n)
  inverts_quasiIso : ∀ {X Y : CochainComplex.Plus A} W V (f : X ⟶ Y),
    QuasiIso f.hom → ∀ p n, IsIso (stepMap W V f p n)
  resolution_independent : ∀ X (W V : RowRealization F X.obj) p n,
    (target X W).piece p n = (target X V).piece p n
  lift_step_formula : ∀ {X Y : CochainComplex.Plus A}
    (W : RowRealization F X.obj) (V : RowRealization F Y.obj) (f : X ⟶ Y)
    (a : W.resolution.bicomplex ⟶ V.resolution.bicomplex)
    (ha : CartanEilenbergComparison.IsLift W.resolution V.resolution f.hom a)
    (g : FilteredMap
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj W.resolution.bicomplex), W.filtration⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj V.resolution.bicomplex), V.filtration⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)) p n,
    stepMap W V f p n =
      (transportStepIso ((target X W).comparison n).symm
        (cohomologyPiece W.filtration p n)).inv ≫ cohomologyStepMap g p n ≫
      (transportStepIso ((target Y V).comparison n).symm
        (cohomologyPiece V.filtration p n)).hom
  limit_naturality : ∀ {X Y : CochainComplex.Plus A}
    (W : RowRealization F X.obj) (V : RowRealization F Y.obj) (f : X ⟶ Y)
    (a : W.resolution.bicomplex ⟶ V.resolution.bicomplex)
    (ha : CartanEilenbergComparison.IsLift W.resolution V.resolution f.hom a)
    (g : FilteredMap
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj W.resolution.bicomplex), W.filtration⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj V.resolution.bicomplex), V.filtration⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ))
    (M : FilteredPageFunctoriality.MapData g W.pages V.pages) r p n
    (hW : Stabilized W.filtration r p n) (hV : Stabilized V.filtration r p n),
    M.map r p n ≫ (limitIso Y V r p n hV).hom =
      (limitIso X W r p n hW).hom ≫
        cokernel.map _ _ (stepMap W V f (p+1) n) (stepMap W V f p n)
          (step_comm W V f p n)
end AdvancedHomologicalAlgebra.RowHypercohomology

namespace AdvancedHomologicalAlgebra.RowHypercohomology.Specs

/-- Finite convergence to the specified total derived cohomology, with
canonical limiting representatives, natural filtered targets and resolution
independence. Quasi-isomorphisms give isomorphisms on every target step. -/
def DerivedTargets : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F], Nonempty (DerivedTargetSystem F)

/-- HA-G03-Row: construction, split first page and signs, classical E₂,
finite convergence to H(RF K), and naturality/independence of all pages
from E₂ onward and of the finite filtered target. The actual localization
of the row construction to D⁺ is allocated to HA-G03. -/
def FullStatement : Prop :=
  SplitRows.{v,u,v',u'} ∧ InvariantColumns.{v,u,v',u'} ∧ RowPages.{v,u,v',u'} ∧
    ComputedRows.{v,u,v',u',w,w'} ∧ RowRealizationsExist.{v,u,v',u',w,w'} ∧
    PageFunctoriality.{v,u,v',u',w,w'} ∧ DerivedTargets.{v,u,v',u',w,w'}

end AdvancedHomologicalAlgebra.RowHypercohomology.Specs
