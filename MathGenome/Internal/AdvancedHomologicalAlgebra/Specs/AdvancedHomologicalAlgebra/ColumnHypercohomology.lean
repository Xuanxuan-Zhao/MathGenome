import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergTotalization
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

/-! HA-G03, column assertions, source 2565–2602 and 2626–2645.
The category of inputs consists of bounded-below cochain complexes and actual
cochain maps. No passage of the first page to the derived category is asserted.
The filtered pages are the fixed subquotients of HA-F03, with their canonical
next-page identifications. The total target is the canonical HA-R06 functor.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.unusedVariables false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.ColumnHypercohomology
open CartanEilenbergData CartanEilenbergTotalization DoubleTotalization
open FiniteDiagonalFiltrations FiniteFiltrationConvergence DoubleComplexFirstPages
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B]

/-- A realization by the column filtration of the actual image double complex.
Finiteness, every page, the first two page calculations, and convergence are
all conclusions; no certificate of them is assumed of the input. -/
structure ColumnModel (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    (R : ResolutionData K) where
  total : ((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)
  filtration : @Filtration B _ _ (sumTotal ((mapDouble F).obj R.bicomplex))
  formula : HasFiltrationFormula ((mapDouble F).obj R.bicomplex) Prod.fst filtration
  pages : F03Specs.PageData filtration
  next : PageCohomology.Data filtration pages
  column : ColumnData ((mapDouble F).obj R.bicomplex) filtration formula pages
  convergence : DoubleComplexConvergence.Converges filtration

abbrev term (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    {R : ResolutionData K} (M : ColumnModel F R) (r p q : ℤ) : B :=
  letI := M.total
  page M.filtration M.pages r p q

abbrev modelComplex (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    {R : ResolutionData K} (M : ColumnModel F R) : CochainComplex B ℤ :=
  letI := M.total
  sumTotal ((mapDouble F).obj R.bicomplex)

abbrev modelFiltered (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    {R : ResolutionData K} (M : ColumnModel F R) : FilteredComplex B :=
  ⟨modelComplex F M, M.filtration⟩

section Derived
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]

/-- The abutment is Hⁿ of the fixed total right derived functor of K. -/
abbrev target (K : CochainComplex.Plus A) (n : ℤ) : B :=
  (DerivedCategory.Plus.homologyFunctor B n).obj
    (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))

abbrev targetMap {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    target F K n ⟶ target F L n :=
  (DerivedCategory.Plus.homologyFunctor B n).map
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f))

/-- The injective column uses the degree-zero map of the given
Cartan–Eilenberg augmentation. -/
structure TermColumnComparison {K : CochainComplex A ℤ} (R : ResolutionData K) (p : ℤ) where
  bounded : (CochainComplex.plus A) (R.bicomplex.X p)
  augmentation :
    (⟨(CochainComplex.singleFunctor A 0).obj (K.X p), ⟨0, inferInstance⟩⟩ :
      CochainComplex.Plus A) ⟶
    (⟨R.bicomplex.X p, bounded⟩ : CochainComplex.Plus A)
  augmentation_eq : augmentation.hom.f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (K.X p)).hom ≫ R.augmentation.f p
  model : ReplacementComparison F _ _ augmentation

/-- The first-page comparison includes its differential, and the target
comparison identifies the actual finite image filtration with a filtration
on the stated RF target by transport along `targetIso`. Negative vertical
indices have zero first page; R^qF uses its usual natural-number index. -/
structure Data (K : CochainComplex.Plus A) (R : ResolutionData K.obj)
    extends ColumnModel F R where
  termComparison : ∀ p : ℤ, TermColumnComparison F R p
  firstIso : ∀ (p : ℤ) (q : ℕ), term F toColumnModel 1 p (q : ℤ) ≅
    (rightValue F q).obj (K.obj.X p)
  firstIso_eq : ∀ (p : ℤ) (q : ℕ), firstIso p q =
    column.firstIso p (q : ℤ) ≪≫ ((termComparison p).model.homologyIso (q : ℤ)).symm
  first_d : ∀ (p : ℤ) (q : ℕ),
    firstDifferential filtration pages p (q : ℤ) ≫ (firstIso (p+1) q).hom =
      (firstIso p q).hom ≫ (rightValue F q).map (K.obj.d p (p+1))
  negative : ∀ p q : ℤ, q < 0 → IsZero (term F toColumnModel 1 p q)
  [sourceTotal : R.bicomplex.HasTotal (.up ℤ)]
  targetComparison : DerivedTotalComparison F K R
  targetIso : ∀ n : ℤ,
    (sumTotal ((mapDouble F).obj R.bicomplex)).homology n ≅ target F K n
  targetIso_eq : ∀ n, targetIso n = (targetComparison.homologyIso n).symm

/-- The actual image filtration transported to Hⁿ(RF K). -/
def targetPiece {K : CochainComplex.Plus A} {R : ResolutionData K.obj}
    (M : Data F K R) (p n : ℤ) : Subobject (target F K n) :=
  (Subobject.map (M.targetIso n).hom).obj (cohomologyPiece M.filtration p n)

/-- Maps induced by a double-complex lift, on the actual filtered complexes. -/
structure LiftData {K L : CochainComplex.Plus A}
    {R : ResolutionData K.obj} {S : ResolutionData L.obj}
    (M : Data F K R) (N : Data F L S) (a : R.bicomplex ⟶ S.bicomplex) where
  filtered : FilteredMap (modelFiltered F M.toColumnModel) (modelFiltered F N.toColumnModel)
  hom_eq : letI := M.total; letI := N.total
    filtered.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)
  maps : FilteredPageFunctoriality.MapData filtered M.pages N.pages

/-- A simultaneous system, for every resolution of every bounded-below K.
`lift` is not a hypothesis on inputs: the construction must supply it for all
maps of double complexes. Independence of the chosen lift starts at E₁;
identity and composition for double-complex maps hold on every page. -/
structure System where
  data : ∀ (K : CochainComplex.Plus A) (R : ResolutionData K.obj), Data F K R
  resolution : ∀ K : CochainComplex.Plus A, Nonempty (ResolutionData K.obj)
  comparison : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (f : K ⟶ L),
    ∃ a : R.bicomplex ⟶ S.bicomplex, CartanEilenbergComparison.IsLift R S f.hom a
  lift : ∀ {K L : CochainComplex.Plus A} (R : ResolutionData K.obj)
    (S : ResolutionData L.obj) (a : R.bicomplex ⟶ S.bicomplex),
    LiftData F (data K R) (data L S) a
  first_naturality : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex),
    CartanEilenbergComparison.IsLift R S f.hom a → ∀ (p : ℤ) (q : ℕ),
      ((lift R S a).maps.map 1 p (p+(q : ℤ))) ≫ ((data L S).firstIso p q).hom =
        ((data K R).firstIso p q).hom ≫ (rightValue F q).map (f.hom.f p)
  next_naturality : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (a : R.bicomplex ⟶ S.bicomplex) r (hr : 0 ≤ r) p n,
    ((lift R S a).maps.map (r+1) (p+r) (n+1)) ≫
        ((data L S).next.nextIso r hr p n).hom =
      ((data K R).next.nextIso r hr p n).hom ≫ ShortComplex.homologyMap
        (FilteredPageFunctoriality.shortComplexMap (lift R S a).maps r hr p n)
  target_naturality : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex),
    CartanEilenbergComparison.IsLift R S f.hom a → ∀ n,
      HomologicalComplex.homologyMap (lift R S a).filtered.hom n ≫
        ((data L S).targetIso n).hom =
      ((data K R).targetIso n).hom ≫ targetMap F f n
  limit_naturality : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (a : R.bicomplex ⟶ S.bicomplex) r p n
    (I : LimitIso (data K R).filtration (data K R).pages r p n)
    (J : LimitIso (data L S).filtration (data L S).pages r p n),
    Stabilized (data K R).filtration r p n →
    Stabilized (data L S).filtration r p n →
    (lift R S a).maps.map r p n ≫ J.iso.hom =
      I.iso.hom ≫ gradedCohomologyMap (lift R S a).filtered p n
  target_decreasing : ∀ (K : CochainComplex.Plus A) (R : ResolutionData K.obj) p n,
    targetPiece F (data K R) (p+1) n ≤ targetPiece F (data K R) p n
  target_finite : ∀ (K : CochainComplex.Plus A) (R : ResolutionData K.obj) n,
    ∃ a b : ℤ,
      (∀ p, p ≤ a → targetPiece F (data K R) p n = ⊤) ∧
      (∀ p, b ≤ p → targetPiece F (data K R) p n = ⊥)
  target_preserves : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (f : K ⟶ L) p n,
    (targetPiece F (data L S) p n).Factors
      ((targetPiece F (data K R) p n).arrow ≫ targetMap F f n)
  target_resolution_independent : ∀ (K : CochainComplex.Plus A)
    (R S : ResolutionData K.obj) p n,
    targetPiece F (data K R) p n = targetPiece F (data K S) p n
  independent : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a b : R.bicomplex ⟶ S.bicomplex),
    CartanEilenbergComparison.IsLift R S f.hom a →
    CartanEilenbergComparison.IsLift R S f.hom b → ∀ r, 1 ≤ r → ∀ p n,
      (lift R S a).maps.map r p n = (lift R S b).maps.map r p n
  map_id : ∀ (K : CochainComplex.Plus A) (R : ResolutionData K.obj) r p n,
    (lift R R (𝟙 R.bicomplex)).maps.map r p n = 𝟙 _
  map_comp : ∀ {K L T : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (U : ResolutionData T.obj)
    (a : R.bicomplex ⟶ S.bicomplex) (b : S.bicomplex ⟶ U.bicomplex) r p n,
    (lift R U (a ≫ b)).maps.map r p n =
      (lift R S a).maps.map r p n ≫ (lift S U b).maps.map r p n
  resolution_independence : ∀ (K : CochainComplex.Plus A)
    (R S : ResolutionData K.obj),
    ∃ (a : R.bicomplex ⟶ S.bicomplex) (b : S.bicomplex ⟶ R.bicomplex),
      CartanEilenbergComparison.IsLift R S (𝟙 K.obj) a ∧
      CartanEilenbergComparison.IsLift S R (𝟙 K.obj) b ∧
      (∀ r, 1 ≤ r → ∀ p n, IsIso ((lift R S a).maps.map r p n)) ∧
      S03Specs.TargetIsomorphisms (lift R S a).filtered
end Derived

namespace Specs
/-- Incremental construction of the actual column pages and finite convergence,
for every supplied resolution and every additive functor. -/
def ColumnModels : Prop :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] (F : A ⥤ B) [F.Additive]
    {K : CochainComplex A ℤ} (R : ResolutionData K), Nonempty (ColumnModel F R)

/-- Full column half of HA-G03. Left exactness means preservation of finite
limits; additivity is the standing convention for the derived constructions.
No injectives or infinite coproducts are required in the target category. -/
def FullStatement : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F],
    Nonempty (System F)
end Specs
end AdvancedHomologicalAlgebra.ColumnHypercohomology
