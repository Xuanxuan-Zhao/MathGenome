import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ColumnHypercohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CartanEilenbergExistence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CartanEilenbergTotalization
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleComplexConvergence

/-! HA-G03, column half. Canonical comparisons through the derived unit give
the value, differential and target naturality. Equality on E₁ propagates via
canonical next-page homology, while finite convergence transports the actual
image filtration to the fixed total derived target. -/
noncomputable section
set_option linter.style.haveILetI false
set_option linter.checkUnivs false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.ColumnHypercohomology
open CartanEilenbergData CartanEilenbergTotalization DoubleTotalization
open FiniteDiagonalFiltrations FiniteFiltrationConvergence DoubleComplexFirstPages
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B]

/-- The column filtration, pages, first two calculations and finite convergence
come from the actual finite-diagonal image bicomplex. -/
def columnModel (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    (R : ResolutionData K) : ColumnModel F R := by
  let hI := (additiveSupport F R).1
  let ht := (additiveSupport F R).2
  letI := ht
  let hf := filtrations ((mapDouble F).obj R.bicomplex) hI
  let Fc := Classical.choose hf
  let hc := (Classical.choose_spec (Classical.choose_spec hf)).1
  let hp := filtered_page_cohomology Fc
  let D := Classical.choose hp
  let C := Classical.choice (Classical.choose_spec hp)
  exact ⟨ht, Fc, hc, D, C, columnData _ Fc hc D,
    DoubleComplexConvergence.converges_of_finite Fc
      (DoubleComplexConvergence.formula_finite _ hI _ (Or.inl rfl) Fc hc)⟩

theorem columnModels : Specs.ColumnModels.{u, v, u', v'} := by
  intro A B _ _ _ _ F _ K R
  exact ⟨columnModel F R⟩

/-- Any double-complex map induces a representative-compatible map of these
column spectral sequences. This construction does not choose a CE lift. -/
def modelLift (F : A ⥤ B) [F.Additive] {K L : CochainComplex A ℤ}
    {R : ResolutionData K} {S : ResolutionData L}
    (M : ColumnModel F R) (N : ColumnModel F S) (a : R.bicomplex ⟶ S.bicomplex) :
    letI := M.total; letI := N.total
    {g : FilteredMap (modelFiltered F M) (modelFiltered F N) //
      g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)} := by
  letI := M.total
  letI := N.total
  exact ⟨Classical.choose (formula_filteredMap _ _ Prod.fst _ _ M.formula N.formula
    ((mapDouble F).map a)), Classical.choose_spec (formula_filteredMap _ _ Prod.fst _ _
      M.formula N.formula ((mapDouble F).map a))⟩

section OrdinaryResolutions
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]

/-- The actual augmentation of an integer-indexed ordinary injective resolution. -/
def resolutionMap {X : A} {I : CochainComplex A ℤ} {i : X ⟶ I.X 0}
    (hI : IsInjectiveResolution X I i) : (CochainComplex.singleFunctor A 0).obj X ⟶ I :=
  HomologicalComplex.mkHomFromSingle i (by
    intro q hq
    have : q = 1 := by simpa using hq.symm
    subst q
    exact hI.augmentation_d)

lemma resolutionMap_quasiIso {X : A} {I : CochainComplex A ℤ} {i : X ⟶ I.X 0}
    (hI : IsInjectiveResolution X I i) : QuasiIso (resolutionMap hI) := by
  rw [quasiIso_iff]
  intro q
  by_cases hq : q = 0
  · subst q
    apply (quasiIsoAt_iff_isIso_homologyMap _ 0).2
    exact resolution_homology_zero_iso hI _
  · apply (quasiIsoAt_iff_isIso_homologyMap _ q).2
    have hsrc := HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 X q hq
    exact (IsZero.isIso (X := ((CochainComplex.singleFunctor A 0).obj X).homology q)
      (Y := I.homology q) hsrc (resolution_homology_zero hI q hq) _)

lemma resolution_injective {X : A} {I : CochainComplex A ℤ} {i : X ⟶ I.X 0}
    (hI : IsInjectiveResolution X I i) : ∀ q, Injective (I.X q) := by
  intro q
  by_cases hq : 0 ≤ q
  · exact hI.injective q hq
  · exact (hI.zero_neg q (by omega)).injective

/-- The universal comparison is invertible on any termwise injective model. -/
lemma model_unit_isIso (F : A ⥤ B) [F.Additive] (I : CochainComplex.Plus A)
    (hI : ∀ q, Injective (I.obj.X q)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app I) := by
  letI := hI
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  infer_instance

/-- A canonical comparison, chosen by the augmentation and the derived unit. -/
def replacementIso (F : A ⥤ B) [F.Additive] (X I : CochainComplex.Plus A)
    (i : X ⟶ I) (hi : QuasiIso i.hom) (hI : ∀ q, Injective (I.obj.X q)) :
    F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj X) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I) :=
  (replacementComparison F i hi hI).iso

lemma replacementComparison_naturality (F : A ⥤ B) [F.Additive]
    {X Y I J : CochainComplex.Plus A} {i : X ⟶ I} {j : Y ⟶ J}
    (M : ReplacementComparison F X I i) (N : ReplacementComparison F Y J j)
    (f : X ⟶ Y) (a : I ⟶ J) (ha : i ≫ a = f ≫ j) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        N.iso.hom =
      M.iso.hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map a) := by
  letI := model_unit_isIso F J N.injective
  apply (cancel_mono (F.rightDerivedFunctorPlusUnit.app J)).1
  simp only [Category.assoc, ReplacementComparison.unit_eq]
  rw [show DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map a) ≫
      F.rightDerivedFunctorPlusUnit.app J =
    F.rightDerivedFunctorPlusUnit.app I ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map a) from
        F.rightDerivedFunctorPlusUnit.naturality a]
  rw [← Category.assoc, ReplacementComparison.unit_eq]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ha]

lemma replacementIso_naturality (F : A ⥤ B) [F.Additive]
    {X Y I J : CochainComplex.Plus A} (i : X ⟶ I) (j : Y ⟶ J)
    (hi : QuasiIso i.hom) (hj : QuasiIso j.hom)
    (hI : ∀ q, Injective (I.obj.X q)) (hJ : ∀ q, Injective (J.obj.X q))
    (f : X ⟶ Y) (a : I ⟶ J) (ha : i ≫ a = f ≫ j) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        (replacementIso F Y J j hj hJ).hom =
      (replacementIso F X I i hi hI).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map a) :=
  replacementComparison_naturality F (replacementComparison F i hi hI)
    (replacementComparison F j hj hJ) f a ha

/-- Package an ordinary resolution using its actual zero lower bound. -/
def resolutionPlus {X : A} {I : CochainComplex A ℤ} {i : X ⟶ I.X 0}
    (hI : IsInjectiveResolution X I i) : CochainComplex.Plus A :=
  ⟨I, 0, (CochainComplex.isStrictlyGE_iff I 0).2 hI.zero_neg⟩

private def singlePlus (A : Type u) [Category.{v} A] [Abelian A] :
    A ⥤ CochainComplex.Plus A :=
  (CochainComplex.plus A).lift (CochainComplex.singleFunctor A 0)
    (fun _ => ⟨0, inferInstance⟩)

def resolutionPlusMap {X : A} {I : CochainComplex A ℤ} {i : X ⟶ I.X 0}
    (hI : IsInjectiveResolution X I i) :
    (singlePlus A).obj X ⟶ resolutionPlus hI :=
  (CochainComplex.plus A).homMk (resolutionMap hI)

/-- The bounded injective model of a term, with the given column augmentation. -/
def termColumnComparison (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    (R : ResolutionData K) (p : ℤ) : TermColumnComparison F R p where
  bounded := (resolutionPlus (R.terms p)).property
  augmentation := resolutionPlusMap (R.terms p)
  augmentation_eq := by
    change (resolutionMap (R.terms p)).f 0 = _
    simp only [resolutionMap, HomologicalComplex.mkHomFromSingle_f]
  model := replacementComparison F (resolutionPlusMap (R.terms p))
    (resolutionMap_quasiIso (R.terms p)) (resolution_injective (R.terms p))

/-- The value comparison is chosen canonically, so it can be used for the
horizontal differential and for arbitrary comparison maps of resolutions. -/
def resolutionValueIso (F : A ⥤ B) [F.Additive]
    {X : A} {I : CochainComplex A ℤ} {i : X ⟶ I.X 0}
    (hI : IsInjectiveResolution X I i) (q : ℕ) :
    (rightValue F q).obj X ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj I).homology (q : ℤ) :=
  (replacementComparison F (resolutionPlusMap hI) (resolutionMap_quasiIso hI)
    (resolution_injective hI)).homologyIso (q : ℤ)

lemma resolutionMap_naturality
    {X Y : A} {I J : CochainComplex A ℤ} {i : X ⟶ I.X 0} {j : Y ⟶ J.X 0}
    (hI : IsInjectiveResolution X I i) (hJ : IsInjectiveResolution Y J j)
    (f : X ⟶ Y) (a : I ⟶ J) (ha : i ≫ a.f 0 = f ≫ j) :
    resolutionMap hI ≫ a = (CochainComplex.singleFunctor A 0).map f ≫
      resolutionMap hJ := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, resolutionMap,
      HomologicalComplex.mkHomFromSingle_f]
    change _ = ((HomologicalComplex.single A (.up ℤ) 0).map f).f 0 ≫ _
    simp only [HomologicalComplex.single_map_f_self, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [ha]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X n hn).eq_of_src _ _

lemma resolutionValueIso_naturality (F : A ⥤ B) [F.Additive]
    {X Y : A} {I J : CochainComplex A ℤ} {i : X ⟶ I.X 0} {j : Y ⟶ J.X 0}
    (hI : IsInjectiveResolution X I i) (hJ : IsInjectiveResolution Y J j)
    (f : X ⟶ Y) (a : I ⟶ J) (ha : i ≫ a.f 0 = f ≫ j) (q : ℕ) :
    (rightValue F q).map f ≫ (resolutionValueIso F hJ q).hom =
      (resolutionValueIso F hI q).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map a) (q : ℤ) := by
  let aa : resolutionPlus hI ⟶ resolutionPlus hJ := (CochainComplex.plus A).homMk a
  have hs : resolutionPlusMap hI ≫ aa =
      (singlePlus A).map f ≫ resolutionPlusMap hJ := by
    apply (CochainComplex.plus A).hom_ext
    exact resolutionMap_naturality hI hJ f a ha
  have hsingle : DerivedCategory.Plus.Q.map ((singlePlus A).map f) =
      (DerivedCategory.Plus.singleFunctor A 0).map f := by
    apply DerivedCategory.Plus.ι.map_injective
    rfl
  have h := congrArg ((DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map)
    (replacementIso_naturality F (resolutionPlusMap hI) (resolutionPlusMap hJ)
      (resolutionMap_quasiIso hI) (resolutionMap_quasiIso hJ)
      (resolution_injective hI) (resolution_injective hJ)
      ((singlePlus A).map f) aa hs)
  simp only [Functor.map_comp, hsingle] at h
  have h' := congrArg (fun k => k ≫
    ((DerivedCategory.homologyFunctorFactors B (q : ℤ)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom) h
  dsimp only [resolutionValueIso, ReplacementComparison.homologyIso,
    Iso.trans_hom, Functor.mapIso_hom]
  calc
    _ = (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
        (replacementIso F ((singlePlus A).obj X)
          (resolutionPlus hI) (resolutionPlusMap hI) (resolutionMap_quasiIso hI)
          (resolution_injective hI)).hom ≫
        (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
          (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map aa)) ≫
        ((DerivedCategory.homologyFunctorFactors B (q : ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom := by
      simpa only [Category.assoc, rightValue, Functor.comp_map, replacementIso] using! h'
    _ = _ := by
      rw [show (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
          (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map aa)) ≫
          ((DerivedCategory.homologyFunctorFactors B (q : ℤ)).app
            ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom =
        ((DerivedCategory.homologyFunctorFactors B (q : ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
          HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map a)
            (q : ℤ) from
          (DerivedCategory.homologyFunctorFactors B (q : ℤ)).hom.naturality
            ((F.mapHomologicalComplex (.up ℤ)).map a)]
      simp only [Category.assoc, replacementIso]
      rfl

section Total
variable {K : CochainComplex.Plus A} (R : ResolutionData K.obj)
  [R.bicomplex.HasTotal (.up ℤ)]

variable (F : A ⥤ B) [F.Additive]
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]

/-- Comparison in the direction RF(K) → Tot(FI), before transporting the
finite target filtration in the opposite direction. -/
def totalValueIso (n : ℤ) : target F K n ≅
    (sumTotal ((mapDouble F).obj R.bicomplex)).homology n :=
  (derivedTotalComparison F K R).homologyIso n

end Total

/-- First-page values and differential for every specified CE resolution. -/
def data (F : A ⥤ B) [F.Additive] (K : CochainComplex.Plus A)
    (R : ResolutionData K.obj) : Data F K R := by
  let M := columnModel F R
  letI := M.total
  letI := (finiteSupport R).2
  refine { M with
    termComparison := termColumnComparison F R
    firstIso := fun p q => M.column.firstIso p (q : ℤ) ≪≫
      (resolutionValueIso F (R.terms p) q).symm
    firstIso_eq := by intros; rfl
    first_d := ?_
    negative := ?_
    targetComparison := derivedTotalComparison F K R
    targetIso := fun n => (totalValueIso R F n).symm
    targetIso_eq := fun _ => rfl }
  · intro p q
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, M.column.first_d]
    rw [Category.assoc]
    have h := resolutionValueIso_naturality F (R.terms p) (R.terms (p+1))
      (K.obj.d p (p+1)) (R.bicomplex.d p (p+1)) (R.augmentation.comm p (p+1)) q
    have hh : HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.up ℤ)).map (R.bicomplex.d p (p+1))) (q : ℤ) ≫
          (resolutionValueIso F (R.terms (p+1)) q).inv =
        (resolutionValueIso F (R.terms p) q).inv ≫
          (rightValue F q).map (K.obj.d p (p+1)) := by
      apply (cancel_epi (resolutionValueIso F (R.terms p) q).hom).1
      simp only [Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ← h]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [Category.assoc, mapDouble, Functor.mapHomologicalComplex_obj_d] using
      congrArg (fun k => (M.column.firstIso p (q : ℤ)).hom ≫ k) hh
  · intro p q hq
    apply (M.column.firstIso p q).isZero_iff.mpr
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    apply ShortComplex.exact_of_isZero_X₂
    exact F.map_isZero ((R.terms p).zero_neg q hq)

end OrdinaryResolutions

/-- Equality on one page propagates under the canonical next-page comparisons,
without a convergence assumption or a filtered homotopy hypothesis. -/
lemma page_maps_eq_from_one {X Y : FilteredComplex B}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    {f g : FilteredMap X Y} (M : FilteredPageFunctoriality.MapData f D E)
    (N : FilteredPageFunctoriality.MapData g D E)
    (C : PageCohomology.Data X.filtration D) (C' : PageCohomology.Data Y.filtration E)
    (h : ∀ p n, M.map 1 p n = N.map 1 p n) (r : ℤ) (hr : 1 ≤ r) :
    ∀ p n, M.map r p n = N.map r p n := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hr
  clear hr
  induction k with
  | zero => simpa using h
  | succ k ih =>
    intro p n
    let r : ℤ := 1 + (k : ℤ)
    have hr : 0 ≤ r := by dsimp [r]; omega
    have hh (p n : ℤ) : M.map (r+1) (p+r) (n+1) = N.map (r+1) (p+r) (n+1) := by
      apply (cancel_mono (C'.nextIso r hr p n).hom).1
      rw [FilteredPageFunctoriality.next_naturality M C C',
        FilteredPageFunctoriality.next_naturality N C C']
      have hs : FilteredPageFunctoriality.shortComplexMap M r hr p n =
          FilteredPageFunctoriality.shortComplexMap N r hr p n := by
        ext <;> apply ih
      rw [hs]
    rw [show 1 + (↑(k+1) : ℤ) = r+1 by dsimp [r]; omega]
    have transport {a b c d : ℤ} (ha : a = c) (hb : b = d)
        (h : M.map (r+1) a b = N.map (r+1) a b) :
        M.map (r+1) c d = N.map (r+1) c d := by
      subst c; subst d; exact h
    exact transport (by omega) (by omega) (hh (p-r) (n-1))

section Naturality
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]

def lift {K L : CochainComplex.Plus A} (R : ResolutionData K.obj)
    (S : ResolutionData L.obj) (a : R.bicomplex ⟶ S.bicomplex) :
    LiftData F (data F K R) (data F L S) a :=
  let g := modelLift F (data F K R).toColumnModel (data F L S).toColumnModel a
  ⟨g.val, g.property, FilteredPageFunctoriality.mapData g.val _ _⟩

lemma lift_first_naturality {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a) (p : ℤ) (q : ℕ) :
    (lift F R S a).maps.map 1 p (p+(q : ℤ)) ≫ ((data F L S).firstIso p q).hom =
      ((data F K R).firstIso p q).hom ≫ (rightValue F q).map (f.hom.f p) := by
  let M := data F K R
  let N := data F L S
  letI := M.total
  letI := N.total
  have hc := columnFirstIso_naturality
    ((mapDouble F).obj R.bicomplex) M.filtration M.formula N.filtration N.formula
    M.pages N.pages ((mapDouble F).map a) (lift F R S a).filtered
    (lift F R S a).hom_eq (lift F R S a).maps p (q : ℤ)
  have ha0 : R.augmentation.f p ≫ (a.f p).f 0 = f.hom.f p ≫ S.augmentation.f p :=
    HomologicalComplex.congr_hom ha p
  have h := resolutionValueIso_naturality F (R.terms p) (S.terms p)
    (f.hom.f p) (a.f p) ha0 q
  have hh : HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map (a.f p)) (q : ℤ) ≫
        (resolutionValueIso F (S.terms p) q).inv =
      (resolutionValueIso F (R.terms p) q).inv ≫ (rightValue F q).map (f.hom.f p) := by
    apply (cancel_epi (resolutionValueIso F (R.terms p) q).hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (lift F R S a).maps.map 1 p (p+(q : ℤ)) ≫
      ((columnModel F S).column.firstIso p (q : ℤ)).hom ≫
        (resolutionValueIso F (S.terms p) q).inv =
    (((columnModel F R).column.firstIso p (q : ℤ)).hom ≫
      (resolutionValueIso F (R.terms p) q).inv) ≫ (rightValue F q).map (f.hom.f p)
  change (lift F R S a).maps.map 1 p (p+(q : ℤ)) ≫
      ((columnModel F S).column.firstIso p (q : ℤ)).hom =
    ((columnModel F R).column.firstIso p (q : ℤ)).hom ≫
      HomologicalComplex.homologyMap (((mapDouble F).map a).f p) (q : ℤ) at hc
  rw [← Category.assoc, hc, Category.assoc]
  simpa only [Category.assoc, mapDouble, Functor.mapHomologicalComplex_map_f] using
    congrArg (fun k => ((columnModel F R).column.firstIso p (q : ℤ)).hom ≫ k) hh

lemma lift_independent {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a b : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a)
    (hb : CartanEilenbergComparison.IsLift R S f.hom b)
    (r : ℤ) (hr : 1 ≤ r) : ∀ p n,
    (lift F R S a).maps.map r p n = (lift F R S b).maps.map r p n := by
  apply page_maps_eq_from_one (lift F R S a).maps (lift F R S b).maps
    (data F K R).next (data F L S).next _ r hr
  intro p n
  let q : ℤ := n-p
  have transport {q q' : ℤ} (hq : q = q')
      (h : (lift F R S a).maps.map 1 p (p+q) = (lift F R S b).maps.map 1 p (p+q)) :
      (lift F R S a).maps.map 1 p (p+q') = (lift F R S b).maps.map 1 p (p+q') := by
    subst q'; exact h
  have hh : (lift F R S a).maps.map 1 p (p+q) =
      (lift F R S b).maps.map 1 p (p+q) := by
    by_cases hq : 0 ≤ q
    · have hn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
      have hn' := transport hn (by
        apply (cancel_mono ((data F L S).firstIso p q.toNat).hom).1
        rw [lift_first_naturality F R S f a ha, lift_first_naturality F R S f b hb])
      exact hn'
    · exact ((data F K R).negative p q (by omega)).eq_of_src _ _
  have hn : p+q=n := by dsimp [q]; omega
  exact hn ▸ hh

/-- Filtered maps with the same underlying cochain map are equal. -/
lemma filteredMap_ext {X Y : FilteredComplex B} {f g : FilteredMap X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; cases h; rfl

lemma lift_id (K : CochainComplex.Plus A) (R : ResolutionData K.obj) (r p n : ℤ) :
    (lift F R R (𝟙 R.bicomplex)).maps.map r p n = 𝟙 _ := by
  letI := (data F K R).total
  have h : (lift F R R (𝟙 R.bicomplex)).filtered =
      FilteredMap.id (modelFiltered F (data F K R).toColumnModel) := by
    apply filteredMap_ext
    rw [(lift F R R (𝟙 R.bicomplex)).hom_eq, CategoryTheory.Functor.map_id]
    exact HomologicalComplex₂.total.map_id _ _
  change FilteredPageFunctoriality.pageMap (lift F R R (𝟙 R.bicomplex)).filtered
    (data F K R).pages (data F K R).pages r p n = _
  rw [h, FilteredPageFunctoriality.pageMap_id]

lemma lift_comp {K L T : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (U : ResolutionData T.obj)
    (a : R.bicomplex ⟶ S.bicomplex) (b : S.bicomplex ⟶ U.bicomplex) (r p n : ℤ) :
    (lift F R U (a ≫ b)).maps.map r p n =
      (lift F R S a).maps.map r p n ≫ (lift F S U b).maps.map r p n := by
  letI := (data F K R).total
  letI := (data F L S).total
  letI := (data F T U).total
  have h : (lift F R U (a ≫ b)).filtered =
      (lift F R S a).filtered.comp (lift F S U b).filtered := by
    apply filteredMap_ext
    change _ = (lift F R S a).filtered.hom ≫ (lift F S U b).filtered.hom
    rw [(lift F R U (a ≫ b)).hom_eq, (lift F R S a).hom_eq, (lift F S U b).hom_eq,
      Functor.map_comp, HomologicalComplex₂.total.map_comp]
  change FilteredPageFunctoriality.pageMap (lift F R U (a ≫ b)).filtered
      (data F K R).pages (data F T U).pages r p n =
    FilteredPageFunctoriality.pageMap (lift F R S a).filtered
      (data F K R).pages (data F L S).pages r p n ≫
    FilteredPageFunctoriality.pageMap (lift F S U b).filtered
      (data F L S).pages (data F T U).pages r p n
  rw [h, FilteredPageFunctoriality.pageMap_comp]

lemma totalValueIso_naturality {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    [R.bicomplex.HasTotal (.up ℤ)] [S.bicomplex.HasTotal (.up ℤ)]
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a) (n : ℤ) :
    targetMap F f n ≫ (totalValueIso S F n).hom =
      (totalValueIso R F n).hom ≫ HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)) n := by
  let M := derivedTotalComparison F K R
  let N := derivedTotalComparison F L S
  let aa : (⟨sumTotal R.bicomplex, M.totalBound⟩ : CochainComplex.Plus A) ⟶
      (⟨sumTotal S.bicomplex, N.totalBound⟩ : CochainComplex.Plus A) :=
    (CochainComplex.plus A).homMk (HomologicalComplex₂.total.map a (.up ℤ))
  have hs : M.augmentation ≫ aa = f ≫ N.augmentation := by
    apply (CochainComplex.plus A).hom_ext
    exact augmentationComparison R S f.hom a ha _ _
      M.augmentation_eq N.augmentation_eq
  let H := DerivedCategory.Plus.homologyFunctor B n
  let eR := M.model.iso
  let eS := N.model.iso
  let b := (F.mapHomologicalComplex (.up ℤ)).map
    (HomologicalComplex₂.total.map a (.up ℤ))
  let cR := ((DerivedCategory.homologyFunctorFactors B n).app
    ((F.mapHomologicalComplex (.up ℤ)).obj (sumTotal R.bicomplex))).hom
  let cS := ((DerivedCategory.homologyFunctorFactors B n).app
    ((F.mapHomologicalComplex (.up ℤ)).obj (sumTotal S.bicomplex))).hom
  let tR := HomologicalComplex.homologyMap M.additivity.hom n
  let tS := HomologicalComplex.homologyMap N.additivity.hom n
  let b' := H.map (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map aa))
  let t := HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)) n
  have hc : targetMap F f n ≫ H.map eS.hom = H.map eR.hom ≫ b' := by
    have h := congrArg H.map (replacementComparison_naturality F M.model N.model f aa hs)
    simpa only [Functor.map_comp] using h
  have hfac : b' ≫ cS = cR ≫ HomologicalComplex.homologyMap b n :=
    (DerivedCategory.homologyFunctorFactors B n).hom.naturality b
  have ht : HomologicalComplex.homologyMap b n ≫ tS = tR ≫ t := by
    have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
      (additiveNaturality F R S M.additivity N.additivity M.summands N.summands a)
    simpa only [HomologicalComplex.homologyMap_comp] using h
  simp only [totalValueIso, DerivedTotalComparison.homologyIso,
    ReplacementComparison.homologyIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change targetMap F f n ≫ H.map eS.hom ≫ cS ≫ tS =
    H.map eR.hom ≫ cR ≫ tR ≫ t
  calc
    _ = (targetMap F f n ≫ H.map eS.hom) ≫ cS ≫ tS := by simp only [Category.assoc]
    _ = H.map eR.hom ≫ (b' ≫ cS) ≫ tS := by rw [hc]; simp only [Category.assoc]
    _ = H.map eR.hom ≫ cR ≫ (HomologicalComplex.homologyMap b n ≫ tS) := by
      rw [hfac]; simp only [Category.assoc]
    _ = _ := by rw [ht]

lemma lift_target_naturality {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a) (n : ℤ) :
    HomologicalComplex.homologyMap (lift F R S a).filtered.hom n ≫
        ((data F L S).targetIso n).hom =
      ((data F K R).targetIso n).hom ≫ targetMap F f n := by
  letI := (finiteSupport R).2
  letI := (finiteSupport S).2
  letI := (data F K R).total
  letI := (data F L S).total
  simp only [Data.targetIso_eq, Iso.symm_hom]
  change HomologicalComplex.homologyMap (lift F R S a).filtered.hom n ≫
      (totalValueIso S F n).inv = (totalValueIso R F n).inv ≫ targetMap F f n
  rw [(lift F R S a).hom_eq]
  apply (cancel_epi (totalValueIso R F n).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← totalValueIso_naturality F R S f a ha n]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma lift_resolution_independence (K : CochainComplex.Plus A)
    (R S : ResolutionData K.obj) :
    ∃ (a : R.bicomplex ⟶ S.bicomplex) (b : S.bicomplex ⟶ R.bicomplex),
      CartanEilenbergComparison.IsLift R S (𝟙 K.obj) a ∧
      CartanEilenbergComparison.IsLift S R (𝟙 K.obj) b ∧
      (∀ r, 1 ≤ r → ∀ p n, IsIso ((lift F R S a).maps.map r p n)) ∧
      S03Specs.TargetIsomorphisms (lift F R S a).filtered := by
  obtain ⟨a, b, ha, hb, hab, hba⟩ := CartanEilenbergComparison.verticalInverseComparisons R S
  have hiso (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
      IsIso ((lift F R S a).maps.map r p n) := by
    let e : PageCohomology.object (data F K R).filtration (data F K R).pages r p n ≅
        PageCohomology.object (data F K S).filtration (data F K S).pages r p n := {
      hom := (lift F R S a).maps.map r p n
      inv := (lift F S R b).maps.map r p n
      hom_inv_id := by
        rw [← lift_comp]
        have h := lift_independent F R R (𝟙 K) (a ≫ b) (𝟙 R.bicomplex)
          (by simpa using CartanEilenbergComparison.isLift_comp R S R ha hb)
          (CartanEilenbergComparison.isLift_id R) r hr p n
        rw [h, lift_id]
      inv_hom_id := by
        rw [← lift_comp]
        have h := lift_independent F S S (𝟙 K) (b ≫ a) (𝟙 S.bicomplex)
          (by simpa using CartanEilenbergComparison.isLift_comp S R S hb ha)
          (CartanEilenbergComparison.isLift_id S) r hr p n
        rw [h, lift_id] }
    exact e.isIso_hom
  exact ⟨a, b, ha, hb, hiso,
    FiniteTargetComparison.target_isomorphisms (lift F R S a).filtered
      (data F K R).convergence.finite (data F K S).convergence.finite
      (data F K R).pages (data F K S).pages (lift F R S a).maps 1 (by omega)
      (hiso 1 (by omega))⟩

lemma targetPiece_eq_mk {K : CochainComplex.Plus A} {R : ResolutionData K.obj}
    (M : Data F K R) (p n : ℤ) :
    targetPiece F M p n = Subobject.mk
      ((cohomologyPiece M.filtration p n).arrow ≫ (M.targetIso n).hom) := by
  unfold targetPiece
  calc
    _ = (Subobject.map (M.targetIso n).hom).obj
        (Subobject.mk (cohomologyPiece M.filtration p n).arrow) :=
      congrArg (Subobject.map (M.targetIso n).hom).obj
        (Subobject.mk_arrow (cohomologyPiece M.filtration p n)).symm
    _ = _ := Subobject.map_mk _ _

lemma target_decreasing {K : CochainComplex.Plus A} {R : ResolutionData K.obj}
    (M : Data F K R) (p n : ℤ) :
    targetPiece F M (p+1) n ≤ targetPiece F M p n :=
  (Subobject.map (M.targetIso n).hom).monotone (cohomologyPiece_decreasing M.filtration p n)

lemma target_finite {K : CochainComplex.Plus A} {R : ResolutionData K.obj}
    (M : Data F K R) (n : ℤ) :
    ∃ a b : ℤ,
      (∀ p, p ≤ a → targetPiece F M p n = ⊤) ∧
      (∀ p, b ≤ p → targetPiece F M p n = ⊥) := by
  obtain ⟨a,b,ha,hb⟩ := M.convergence.target.finite n
  refine ⟨a,b,?_,?_⟩
  · intro p hp
    rw [targetPiece, ha p hp, Subobject.map_top, Subobject.mk_eq_top_of_isIso]
  · intro p hp
    rw [targetPiece, hb p hp, Subobject.map_bot]

lemma target_preserves {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (f : K ⟶ L) (p n : ℤ) :
    (targetPiece F (data F L S) p n).Factors
      ((targetPiece F (data F K R) p n).arrow ≫ targetMap F f n) := by
  obtain ⟨a,ha⟩ := CartanEilenbergComparison.liftExists R S f.hom
  let M := data F K R
  let N := data F L S
  let i := (cohomologyPiece M.filtration p n).arrow ≫ (M.targetIso n).hom
  let j := (cohomologyPiece N.filtration p n).arrow ≫ (N.targetIso n).hom
  have hs : cohomologyStepMap (lift F R S a).filtered p n ≫ j =
      i ≫ targetMap F f n := by
    dsimp only [i,j]
    rw [← Category.assoc, cohomologyStepMap_arrow, Category.assoc,
      lift_target_naturality F R S f a ha n, ← Category.assoc]
  rw [targetPiece_eq_mk F M, targetPiece_eq_mk F N]
  apply (Subobject.factors_iff _ _).2
  refine ⟨(Subobject.underlyingIso i).hom ≫
    cohomologyStepMap (lift F R S a).filtered p n ≫ (Subobject.underlyingIso j).inv, ?_⟩
  change (_ ≫ _ ≫ (Subobject.underlyingIso j).inv) ≫ (Subobject.mk j).arrow = _
  simp only [Category.assoc, Subobject.underlyingIso_arrow]
  rw [hs, ← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]

lemma target_resolution_independent (K : CochainComplex.Plus A)
    (R S : ResolutionData K.obj) (p n : ℤ) :
    targetPiece F (data F K R) p n = targetPiece F (data F K S) p n := by
  obtain ⟨a,b,ha,hb,hpage,htarget⟩ := lift_resolution_independence F K R S
  obtain ⟨e,he,hsteps⟩ := htarget n
  obtain ⟨eStep,hStep,hStepInv⟩ := hsteps p
  rw [targetPiece_eq_mk F (data F K R), targetPiece_eq_mk F (data F K S)]
  apply Subobject.mk_eq_mk_of_comm _ _ eStep
  rw [hStep, ← Category.assoc, cohomologyStepMap_arrow, Category.assoc,
    lift_target_naturality F R S (𝟙 K) a ha n]
  simp only [targetMap, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The entire column construction. Different resolutions are inputs to the
same system; comparisons lift actual cochain maps and are independent from E₁. -/
def system : System F where
  data := data F
  resolution K := by
    obtain ⟨L, hL⟩ := K.property
    exact CartanEilenbergExistence.existsResolution K.obj
      ⟨L, fun p hp => (CochainComplex.isStrictlyGE_iff K.obj L).1 hL p hp⟩
  comparison R S f := CartanEilenbergComparison.liftExists R S f.hom
  lift := lift F
  first_naturality := lift_first_naturality F
  next_naturality R S a r hr p n :=
    FilteredPageFunctoriality.next_naturality (lift F R S a).maps
      (data F _ R).next (data F _ S).next r hr p n
  target_naturality := lift_target_naturality F
  limit_naturality R S a r p n I J hI hJ :=
    limitIso_naturality (lift F R S a).filtered (data F _ R).pages (data F _ S).pages
      (lift F R S a).maps r p n I J hI
  target_decreasing K R := target_decreasing F (data F K R)
  target_finite K R := target_finite F (data F K R)
  target_preserves := target_preserves F
  target_resolution_independent := target_resolution_independent F
  independent := lift_independent F
  map_id := lift_id F
  map_comp := lift_comp F
  resolution_independence := lift_resolution_independence F

end Naturality

theorem column_hypercohomology : Specs.FullStatement.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ F _ _
  exact ⟨system F⟩
end AdvancedHomologicalAlgebra.ColumnHypercohomology
