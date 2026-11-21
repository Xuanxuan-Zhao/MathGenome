import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechToCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveCechExactness
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory AdvancedHomologicalAlgebra.Cech
universe u v w u' v' w'

namespace AdvancedHomologicalAlgebra.CechToCohomology

/-- The independent full-product complex is definitionally the HA-H02 complex. -/
lemma cechComplex_eq {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {A : Type v}
    (c : Cover U A) (F : PresheafOfModules.{u} R.obj) :
    cechComplex R c F = CechCochains.complex R F c := rfl

variable (S : Type u) [Ring S] (J : Type v)

/-- A cycle in a full product has a primitive by choosing one in each component. -/
instance moduleProduct_preservesHomology : (moduleProduct S J).PreservesHomology := by
  apply ((Functor.exact_tfae (moduleProduct S J)).out 2 3).1
  intro C hC
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro z hz
  have component (j : J) : ∃ x : C.X₁.obj ⟨j⟩, C.f.app ⟨j⟩ x = z j := by
    let E := (evaluation (Discrete J) (ModuleCat.{u} S)).obj ⟨j⟩
    exact (ShortComplex.moduleCat_exact_iff (C.map E)).1 (hC.map E)
      (z j) (congrFun hz j)
  choose x hx using component
  exact ⟨x, funext hx⟩

instance moduleProduct_preservesFiniteLimits : PreservesFiniteLimits (moduleProduct S J) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance moduleProduct_preservesFiniteColimits : PreservesFiniteColimits (moduleProduct S J) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

theorem product_exactness :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.productExactness.{u, v} := by
  intro S _ J
  infer_instance

def productHomologyIso (K : CochainComplex (Discrete J ⥤ ModuleCat.{u} S) ℕ) (q : ℕ) :
    (((moduleProduct S J).mapHomologicalComplex (.up ℕ)).obj K).homology q ≅
      ModuleCat.of S (∀ j : J,
        ((((evaluation (Discrete J) (ModuleCat.{u} S)).obj ⟨j⟩).mapHomologicalComplex
          (.up ℕ)).obj K).homology q) :=
  (K.sc q).mapHomologyIso (moduleProduct S J) ≪≫
    (LinearEquiv.piCongrRight fun j : J ↦
      ((K.sc q).mapHomologyIso ((evaluation (Discrete J) (ModuleCat.{u} S)).obj ⟨j⟩)).symm.toLinearEquiv).toModuleIso
variable {X : TopCat.{u}} (R : RingSheaf X)
variable {U : Opens X} {I : Type v} (c : Cover U I)

theorem local_resolution :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.localResolution.{u} := by
  intro X R M I q
  exact ⟨I.isoRightDerivedObj (SheafOfModules.forget R) q⟩

theorem local_resolution_naturality :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.localResolutionNaturality.{u} := by
  intro X R M N f I J φ hφ q
  exact I.isoRightDerivedObj_hom_naturality f J φ hφ (SheafOfModules.forget R) q

/-- Each tuple's sections, with scalar restriction from the covered open. -/
def tupleDiagram (p : ℕ) : PresheafOfModules.{u} R.obj ⥤
    Discrete (Fin (p + 1) → I) ⥤ ModuleCat.{u} (sectionRing R U) where
  obj F := Discrete.functor fun t ↦ localSections R F U (tupleOpen c t) (tupleOpen_le c t)
  map f := Discrete.natTrans fun t ↦
    (ModuleCat.restrictScalars (R.obj.map (homOfLE (tupleOpen_le c t.as)).op).hom).map
      (f.app (op (tupleOpen c t.as)))

instance tupleDiagram_additive (p : ℕ) : (tupleDiagram R c p).Additive where
  map_add := by intros; ext; rfl

instance tupleDiagram_preservesFiniteLimits (p : ℕ) :
    PreservesFiniteLimits (tupleDiagram R c p) where
  preservesFiniteLimits J _ _ := by
    apply preservesLimitsOfShape_of_evaluation
    intro t
    change PreservesLimitsOfShape J
      (PresheafOfModules.evaluation R.obj (op (tupleOpen c t.as)) ⋙
        ModuleCat.restrictScalars (R.obj.map (homOfLE (tupleOpen_le c t.as)).op).hom)
    infer_instance

instance tupleDiagram_preservesFiniteColimits (p : ℕ) :
    PreservesFiniteColimits (tupleDiagram R c p) where
  preservesFiniteColimits J _ _ := by
    apply preservesColimitsOfShape_of_evaluation
    intro t
    change PreservesColimitsOfShape J
      (PresheafOfModules.evaluation R.obj (op (tupleOpen c t.as)) ⋙
        ModuleCat.restrictScalars (R.obj.map (homOfLE (tupleOpen_le c t.as)).op).hom)
    infer_instance

abbrev termFunctor (p : ℕ) := tupleDiagram R c p ⋙ moduleProduct (sectionRing R U) (Fin (p+1) → I)

instance cochainFunctor_preservesFiniteLimits : PreservesFiniteLimits (cochainFunctor R c) where
  preservesFiniteLimits J _ _ := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro p
    change PreservesLimitsOfShape J (termFunctor R c p)
    infer_instance

instance cochainFunctor_preservesFiniteColimits : PreservesFiniteColimits (cochainFunctor R c) where
  preservesFiniteColimits J _ _ := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro p
    change PreservesColimitsOfShape J (termFunctor R c p)
    infer_instance

/-- Vertical cohomology of the Čech resolution double complex, as a whole
horizontal complex, is Čech cochains of the actual cohomology presheaf. -/
def verticalCohomologyIso (K : CochainComplex (PresheafOfModules.{u} R.obj) ℕ) (q : ℕ) :
    (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).obj K).homology q ≅
      cechComplex R c (K.homology q) :=
  (K.sc q).mapHomologyIso (cochainFunctor R c)

/-- In particular this computes every injective resolution, without sheafifying. -/
def resolutionVerticalIso (M : Modules R) (I : InjectiveResolution M) (q : ℕ) :
    (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).obj
      (underlyingComplex R I.cocomplex)).homology q ≅
        cechComplex R c ((localCohomology R q).obj M) :=
  verticalCohomologyIso R c _ q ≪≫
    (cochainFunctor R c).mapIso (I.isoRightDerivedObj (SheafOfModules.forget R) q).symm


@[reassoc]
lemma verticalCohomologyIso_naturality
    {K L : CochainComplex (PresheafOfModules.{u} R.obj) ℕ} (φ : K ⟶ L) (q : ℕ) :
    HomologicalComplex.homologyMap
      (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).map φ) q ≫
        (verticalCohomologyIso R c L q).hom =
      (verticalCohomologyIso R c K q).hom ≫
        (cochainFunctor R c).map (HomologicalComplex.homologyMap φ q) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map φ) (cochainFunctor R c)

@[reassoc]
lemma resolutionVerticalIso_naturality (M N : Modules R) (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    HomologicalComplex.homologyMap
      (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).map
        (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ)) q ≫
          (resolutionVerticalIso R c N J q).hom =
      (resolutionVerticalIso R c M I q).hom ≫
        (cochainFunctor R c).map ((localCohomology R q).map f) := by
  have h := I.isoRightDerivedObj_inv_naturality f J φ hφ (SheafOfModules.forget R) q
  change (I.isoRightDerivedObj (SheafOfModules.forget R) q).inv ≫
      (localCohomology R q).map f =
    HomologicalComplex.homologyMap
      (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ) q ≫
        (J.isoRightDerivedObj (SheafOfModules.forget R) q).inv at h
  dsimp only [resolutionVerticalIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, verticalCohomologyIso_naturality, Category.assoc,
    ← Functor.map_comp, ← h, Functor.map_comp]
  rfl

lemma resolution_vertical_lift_independent (M N : Modules R) (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    HomologicalComplex.homologyMap
      (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).map
        (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ)) q =
    HomologicalComplex.homologyMap
      (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).map
        (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map ψ)) q := by
  apply (cancel_mono (resolutionVerticalIso R c N J q).hom).1
  rw [resolutionVerticalIso_naturality R c M N f I J φ hφ,
    resolutionVerticalIso_naturality R c M N f I J ψ hψ]

/-- Local cohomology computed over an open, with its original section ring. -/
def localEvaluationIso (M : Modules R) (I : InjectiveResolution M) (V : Opens X) (q : ℕ) :
    ((localCohomology R q).obj M).obj (op V) ≅
      (evaluateComplex R V (underlyingComplex R I.cocomplex)).homology q :=
  (PresheafOfModules.evaluation R.obj (op V)).mapIso
    (I.isoRightDerivedObj (SheafOfModules.forget R) q) ≪≫
      (((underlyingComplex R I.cocomplex).sc q).mapHomologyIso
        (PresheafOfModules.evaluation R.obj (op V))).symm

theorem product_cohomology :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.productCohomology.{u, v} := by
  intro S _ J K q
  exact ⟨productHomologyIso S J K q⟩

theorem cech_exactness :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.cechExactness.{u, v} := by
  intro X R U I c
  infer_instance

theorem resolution_vertical :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.resolutionVertical.{u, v} := by
  intro X R U A c M I q
  exact ⟨resolutionVerticalIso R c M I q⟩

lemma augmented_zero_quasiIso (M : Modules R) : QuasiIsoAt (augmentationFromSingle R c M) 0 := by
  rw [quasiIsoAt_iff]
  let φ := (HomologicalComplex.shortComplexFunctor _ (.up ℕ) 0).map
    (augmentationFromSingle R c M)
  change ShortComplex.QuasiIso φ
  rw [ShortComplex.quasiIso_iff_of_zeros φ (by simp)
    (by simp) (by simp)]
  constructor
  · apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz
    change (CechCochains.complex R M.val c).d 0 ((ComplexShape.up ℕ).next 0) z = 0 at hz
    rw [CochainComplex.next] at hz
    rw [CechCochains.complex_d] at hz
    obtain ⟨s, hs⟩ := (InjectiveCechExactness.augmentation_exact c M).2 z hz
    exact ⟨ULift.up s, hs⟩
  · apply (ModuleCat.mono_iff_injective _).2
    intro s t h
    apply ULift.ext
    exact (InjectiveCechExactness.augmentation_exact c M).1 h

lemma augmented_quasiIso (M : Modules R) [Injective M] : QuasiIso (augmentationFromSingle R c M) := by
  rw [quasiIso_iff]
  intro q
  cases q with
  | zero => exact augmented_zero_quasiIso R c M
  | succ q =>
    apply (quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ q)).2
    apply (HomologicalComplex.exactAt_iff' _ q (q+1) (q+2) (by simp) (by simp)).2
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz
    change (CechCochains.complex R M.val c).d (q+1) (q+2) z = 0 at hz
    rw [CechCochains.complex_d] at hz
    obtain ⟨y, hy⟩ := (InjectiveCechExactness.injective_exact R c M inferInstance).2.2 q z hz
    refine ⟨y, ?_⟩
    change (CechCochains.complex R M.val c).d q (q+1) y = z
    rw [CechCochains.complex_d]
    exact hy

theorem injective_augmentation :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.injectiveAugmentation.{u, v} := by
  intro X R U A c M hM
  let := hM
  exact augmented_quasiIso R c M

theorem resolution_vertical_natural :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.resolutionVerticalNaturality.{u, v} := by
  intro X R U A c
  refine ⟨resolutionVerticalIso R c, ?_⟩
  intro M N f I J φ hφ q
  exact resolutionVerticalIso_naturality R c M N f I J φ hφ q

@[reassoc]
lemma localEvaluationIso_naturality (V : Opens X) (M N : Modules R) (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    ((localCohomology R q).map f).app (op V) ≫ (localEvaluationIso R N J V q).hom =
      (localEvaluationIso R M I V q).hom ≫ HomologicalComplex.homologyMap
        (((SheafOfModules.evaluation R (op V)).mapHomologicalComplex (.up ℕ)).map φ) q := by
  have h := I.isoRightDerivedObj_hom_naturality f J φ hφ (SheafOfModules.forget R) q
  change (localCohomology R q).map f ≫ (J.isoRightDerivedObj (SheafOfModules.forget R) q).hom =
    (I.isoRightDerivedObj (SheafOfModules.forget R) q).hom ≫
      HomologicalComplex.homologyMap
        (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ) q at h
  have hh := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map
      (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ))
        (PresheafOfModules.evaluation R.obj (op V))
  change (PresheafOfModules.evaluation R.obj (op V)).map
      (HomologicalComplex.homologyMap
        (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ) q) ≫
        (((underlyingComplex R J.cocomplex).sc q).mapHomologyIso
          (PresheafOfModules.evaluation R.obj (op V))).inv =
    (((underlyingComplex R I.cocomplex).sc q).mapHomologyIso
      (PresheafOfModules.evaluation R.obj (op V))).inv ≫
        HomologicalComplex.homologyMap
          (((SheafOfModules.evaluation R (op V)).mapHomologicalComplex (.up ℕ)).map φ) q at hh
  dsimp only [localEvaluationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change (PresheafOfModules.evaluation R.obj (op V)).map _ ≫
    ((PresheafOfModules.evaluation R.obj (op V)).map _ ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  rw [hh]
  rfl

/-- Evaluation of the cohomology presheaf is the ordinary right derived section
functor, naturally in the coefficient sheaf. -/
def localSectionsIso (V : Opens X) (q : ℕ) :
    localCohomology R q ⋙ PresheafOfModules.evaluation R.obj (op V) ≅
      (SheafOfModules.evaluation R (op V)).rightDerived q :=
  NatIso.ofComponents (fun M ↦
    localEvaluationIso R M (injectiveResolution M) V q ≪≫
      ((injectiveResolution M).isoRightDerivedObj (SheafOfModules.evaluation R (op V)) q).symm)
    (by
      intro M N f
      let I := injectiveResolution M
      let J := injectiveResolution N
      let φ := InjectiveResolution.desc f J I
      have hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 := InjectiveResolution.desc_commutes_zero f J I
      have h := I.isoRightDerivedObj_inv_naturality f J φ hφ
        (SheafOfModules.evaluation R (op V)) q
      change (I.isoRightDerivedObj (SheafOfModules.evaluation R (op V)) q).inv ≫
        ((SheafOfModules.evaluation R (op V)).rightDerived q).map f =
          HomologicalComplex.homologyMap
            (((SheafOfModules.evaluation R (op V)).mapHomologicalComplex (.up ℕ)).map φ) q ≫
              (J.isoRightDerivedObj (SheafOfModules.evaluation R (op V)) q).inv at h
      change ((localCohomology R q).map f).app (op V) ≫
        ((localEvaluationIso R N J V q).hom ≫
          (J.isoRightDerivedObj (SheafOfModules.evaluation R (op V)) q).inv) =
        ((localEvaluationIso R M I V q).hom ≫
          (I.isoRightDerivedObj (SheafOfModules.evaluation R (op V)) q).inv) ≫
            ((SheafOfModules.evaluation R (op V)).rightDerived q).map f
      rw [← Category.assoc, localEvaluationIso_naturality R V M N f I J φ hφ,
        Category.assoc, ← h]
      simp only [Category.assoc])

theorem local_sections :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.localSections.{u} := by
  intro X R V q
  exact ⟨localSectionsIso R V q⟩

/-- The model has exactly the source's full-product entries, for every tuple. -/
lemma resolutionDoubleComplex_X (M : Modules R) (I : InjectiveResolution M) (p q : ℕ) :
    ((resolutionDoubleComplex R c M I).X p).X q =
      ModuleCat.of (sectionRing R U) (Cochains R (I.cocomplex.X q).val c p) := rfl

/-- The horizontal map is exactly the alternating restriction differential. -/
lemma resolutionDoubleComplex_horizontal (M : Modules R) (I : InjectiveResolution M) (p q : ℕ) :
    ((resolutionDoubleComplex R c M I).d p (p+1)).f q =
      ModuleCat.ofHom (differential R (I.cocomplex.X q).val c p) :=
  CechCochains.complex_d R _ c p

/-- The vertical map applies the actual resolution differential componentwise. -/
lemma resolutionDoubleComplex_vertical (M : Modules R) (I : InjectiveResolution M) (p q : ℕ) :
    ((resolutionDoubleComplex R c M I).X p).d q (q+1) =
      ModuleCat.ofHom (cochainMap R c (I.cocomplex.d q (q+1)).val p) := rfl

/-- Iterated cohomology comparison, prior to the filtered-page identification. -/
def resolutionSecondIso (M : Modules R) (I : InjectiveResolution M) (p q : ℕ) :
    ((((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).obj
      (underlyingComplex R I.cocomplex)).homology q).homology p ≅
        (localCechCohomology R c p q).obj M :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} (sectionRing R U)) (.up ℕ) p).mapIso
    (resolutionVerticalIso R c M I q)

theorem resolution_second :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.resolutionSecond.{u, v} := by
  intro X R U A c M I p q
  exact ⟨resolutionSecondIso R c M I p q⟩

open DoubleTotalization FiniteDiagonalFiltrations

section SpectralData
variable {A : Type w} [Category.{v} A] [Abelian A]

/-- All filtered pages are subquotients of the same associated graded term. -/
lemma page_isZero_of_graded {T : CochainComplex A ℤ} (F : Filtration T)
    (D : F03Specs.PageData F) (r p n : ℤ) (h : IsZero ((F.graded p).X n)) :
    IsZero (PageCohomology.object F D r p n) := by
  apply IsZero.of_epi (cokernel.π (Subobject.ofLE _ _ (D.containment r p n)))
  exact IsZero.of_mono (FilteredPage.cycles F r p n).arrow h

/-- The actual column spectral sequence on a finite-diagonal total complex. -/
def columnSpectralData (K : Bicomplex A) (hK : FiniteDiagonals K)
    [K.HasTotal (.up ℤ)] : ColumnSpectralData K :=
  let hs := FiniteDiagonalFiltrations.filtrations K hK
  let Fc := hs.choose
  let Fr := hs.choose_spec.choose
  let hc := hs.choose_spec.choose_spec.1
  let hr := hs.choose_spec.choose_spec.2.1
  let D := FilteredPage.pageData Fc
  ⟨Fc, hc, D, PageCohomology.data Fc D,
    DoubleComplexFirstPages.columnData K Fc hc D,
    (DoubleComplexConvergence.double_complex_convergence K hK Fc Fr hc hr).1⟩

lemma columnSpectralData_firstQuadrant (K : Bicomplex A) (hK : FiniteDiagonals K)
    [K.HasTotal (.up ℤ)] (hQ : InQuadrant K 0 0) (r p q : ℤ)
    (h : p < 0 ∨ q < 0) :
    IsZero (DoubleComplexFirstPages.page (columnSpectralData K hK).filtration
      (columnSpectralData K hK).pages r p q) := by
  apply page_isZero_of_graded
  exact (hQ p q (by omega)).of_iso
    ((columnSpectralData K hK).firstPages.gradedIso p q)


/-- Equality of induced maps on a page propagates to all later pages. -/
lemma pageMap_eq_of_page_eq {X Y : FilteredComplex A} (f g : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E)
    (N : FilteredPageFunctoriality.MapData g D E)
    (r : ℤ) (hr : 0 ≤ r) (h : ∀ p n, M.map r p n = N.map r p n)
    (s : ℤ) (hs : r ≤ s) : ∀ p n, M.map s p n = N.map s p n := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hs
  clear hs
  induction k with
  | zero =>
    rw [Int.natCast_zero, add_zero]
    exact h
  | succ k ih =>
    intro p n
    have hk : 0 ≤ r + (k : ℤ) := by omega
    let C := PageCohomology.data X.filtration D
    let C' := PageCohomology.data Y.filtration E
    have heq : FilteredPageFunctoriality.shortComplexMap M (r + (k : ℤ)) hk
        (p-(r+(k : ℤ))) (n-1) =
      FilteredPageFunctoriality.shortComplexMap N (r + (k : ℤ)) hk
        (p-(r+(k : ℤ))) (n-1) := by
      ext <;> apply ih
    have hM := FilteredPageFunctoriality.next_naturality M C C' (r+(k : ℤ)) hk
      (p-(r+(k : ℤ))) (n-1)
    have hN := FilteredPageFunctoriality.next_naturality N C C' (r+(k : ℤ)) hk
      (p-(r+(k : ℤ))) (n-1)
    rw [heq] at hM
    have hh := (cancel_mono (C'.nextIso (r+(k : ℤ)) hk
      (p-(r+(k : ℤ))) (n-1)).hom).1 (hM.trans hN.symm)
    rw [sub_add_cancel, sub_add_cancel] at hh
    rw [show r + (↑(k+1) : ℤ) = r + (k : ℤ) + 1 by omega]
    exact hh

variable {K L : Bicomplex A} [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)]

/-- A bicomplex map acts on the actual column filtration of its total. -/
def columnFilteredMap (D : ColumnSpectralData K) (E : ColumnSpectralData L) (f : K ⟶ L) :
    FilteredMap ⟨sumTotal K, D.filtration⟩ ⟨sumTotal L, E.filtration⟩ :=
  (FiniteDiagonalFiltrations.formula_filteredMap K L Prod.fst D.filtration E.filtration
    D.formula E.formula f).choose

lemma columnFilteredMap_hom (D : ColumnSpectralData K) (E : ColumnSpectralData L) (f : K ⟶ L) :
    (columnFilteredMap D E f).hom = HomologicalComplex₂.total.map f (.up ℤ) :=
  (FiniteDiagonalFiltrations.formula_filteredMap K L Prod.fst D.filtration E.filtration
    D.formula E.formula f).choose_spec

/-- Canonical morphisms of every column page, with their differential equations. -/
def columnPageMapData (D : ColumnSpectralData K) (E : ColumnSpectralData L) (f : K ⟶ L) :=
  FilteredPageFunctoriality.mapData (columnFilteredMap D E f) D.pages E.pages

lemma columnPageMap_lift_independent (D : ColumnSpectralData K) (E : ColumnSpectralData L)
    (f g : K ⟶ L)
    (h : ∀ p q, HomologicalComplex.homologyMap (f.f p) q =
      HomologicalComplex.homologyMap (g.f p) q)
    (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    (columnPageMapData D E f).map r p n = (columnPageMapData D E g).map r p n := by
  apply pageMap_eq_of_page_eq (columnFilteredMap D E f) (columnFilteredMap D E g)
    D.pages E.pages (columnPageMapData D E f) (columnPageMapData D E g) 1 (by omega) _ r hr p n
  intro p n
  let q := n-p
  have h₁ := DoubleComplexFirstPages.columnFirstIsoAt_naturality K D.filtration D.formula
    E.filtration E.formula D.pages E.pages f (columnFilteredMap D E f)
    (columnFilteredMap_hom D E f) (columnPageMapData D E f) p q n (by dsimp [q]; omega)
  have h₂ := DoubleComplexFirstPages.columnFirstIsoAt_naturality K D.filtration D.formula
    E.filtration E.formula D.pages E.pages g (columnFilteredMap D E g)
    (columnFilteredMap_hom D E g) (columnPageMapData D E g) p q n (by dsimp [q]; omega)
  apply (cancel_mono (DoubleComplexFirstPages.columnFirstIsoAt L E.filtration E.formula
    E.pages p q n (by dsimp [q]; omega)).hom).1
  rw [h₁, h₂, h p q]


lemma filteredMap_eq_of_hom_eq {X Y : FilteredComplex A} (f g : FilteredMap X Y)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl
variable {K L N : Bicomplex A}
  [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)] [N.HasTotal (.up ℤ)]
lemma columnFilteredMap_id (D : ColumnSpectralData K) :
    columnFilteredMap D D (𝟙 K) = FilteredMap.id ⟨sumTotal K, D.filtration⟩ := by
  apply filteredMap_eq_of_hom_eq
  rw [columnFilteredMap_hom, HomologicalComplex₂.total.map_id]
  rfl
lemma columnFilteredMap_comp (D : ColumnSpectralData K) (E : ColumnSpectralData L)
    (G : ColumnSpectralData N) (f : K ⟶ L) (g : L ⟶ N) :
    columnFilteredMap D G (f ≫ g) = (columnFilteredMap D E f).comp (columnFilteredMap E G g) := by
  apply filteredMap_eq_of_hom_eq
  change (columnFilteredMap D G (f ≫ g)).hom =
    (columnFilteredMap D E f).hom ≫ (columnFilteredMap E G g).hom
  rw [columnFilteredMap_hom, columnFilteredMap_hom, columnFilteredMap_hom,
    HomologicalComplex₂.total.map_comp]
lemma columnPageMap_id (D : ColumnSpectralData K) (r p n : ℤ) :
    (columnPageMapData D D (𝟙 K)).map r p n = 𝟙 _ := by
  change FilteredPageFunctoriality.pageMap _ _ _ _ _ _ = _
  rw [columnFilteredMap_id]
  exact FilteredPageFunctoriality.pageMap_id _ _ _ _ _
lemma columnPageMap_comp (D : ColumnSpectralData K) (E : ColumnSpectralData L)
    (G : ColumnSpectralData N) (f : K ⟶ L) (g : L ⟶ N) (r p n : ℤ) :
    (columnPageMapData D G (f ≫ g)).map r p n =
      (columnPageMapData D E f).map r p n ≫ (columnPageMapData E G g).map r p n := by
  change FilteredPageFunctoriality.pageMap _ _ _ _ _ _ = _
  rw [columnFilteredMap_comp D E G f g]
  exact FilteredPageFunctoriality.pageMap_comp _ _ _ _ _ _ _ _

/-- The second filtered page with its canonical iterated cohomology identification. -/
def columnSecondPageIso (D : ColumnSpectralData K) (p q : ℤ) :
    DoubleComplexFirstPages.page D.filtration D.pages 2 p q ≅
      (DoubleComplexFirstPages.verticalHomology K q).homology p :=
  DoubleComplexFirstPages.columnSecondIso K D.filtration D.formula D.pages p q
@[reassoc]
lemma columnSecondPageIso_naturality (D : ColumnSpectralData K) (E : ColumnSpectralData L)
    (f : K ⟶ L) (p q : ℤ) :
    (columnPageMapData D E f).map 2 p (p+q) ≫ (columnSecondPageIso E p q).hom =
      (columnSecondPageIso D p q).hom ≫ HomologicalComplex.homologyMap
        (DoubleComplexFirstPages.verticalHomologyMap K f q) p :=
  DoubleComplexFirstPages.columnSecondIso_naturality K D.filtration D.formula
    E.filtration E.formula D.pages E.pages f (columnFilteredMap D E f)
      (columnFilteredMap_hom D E f) (columnPageMapData D E f) p q

/-- Naturality of a horizontal augmentation follows from its actual axis formula. -/
lemma rowTotalAugmentation_naturality {P Q : CochainComplex A ℤ}
    (a : P ⟶ K.X 0) (b : Q ⟶ L.X 0)
    (α : P ⟶ sumTotal K) (β : Q ⟶ sumTotal L)
    (hα : ∀ n, α.f n = a.f n ≫ sumInjection K 0 n n (zero_add n))
    (hβ : ∀ n, β.f n = b.f n ≫ sumInjection L 0 n n (zero_add n))
    (f : P ⟶ Q) (g : K ⟶ L) (h : f ≫ b = a ≫ g.f 0) :
    f ≫ β = α ≫ HomologicalComplex₂.total.map g (.up ℤ) := by
  ext n
  simp only [HomologicalComplex.comp_f, hα, hβ, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun t => t ≫ sumInjection L 0 n n (zero_add n))
      (congrArg (fun t => t.f n) h)

/-- A quasi-isomorphic augmentation detects equality of the maps on its total cohomology. -/
lemma total_homologyMap_eq_of_augmentation {P Q : CochainComplex A ℤ}
    (α : P ⟶ sumTotal K) (β : Q ⟶ sumTotal L) [QuasiIso α]
    (f f' : P ⟶ Q) (g g' : K ⟶ L)
    (h : f ≫ β = α ≫ HomologicalComplex₂.total.map g (.up ℤ))
    (h' : f' ≫ β = α ≫ HomologicalComplex₂.total.map g' (.up ℤ))
    (n : ℤ) (hn : HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap f' n) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map g (.up ℤ)) n =
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map g' (.up ℤ)) n := by
  apply (cancel_epi (HomologicalComplex.homologyMap α n)).1
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← h, ← h', HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, hn]

variable {T : CochainComplex A ℤ} (F : Filtration T) {H : A} (n : ℤ)
    (e : T.homology n ≅ H)
open FiniteFiltrationConvergence
lemma abutmentPiece_finite (hF : CohomologyFiltrationData F) :
    ∃ a b : ℤ, (∀ p, p ≤ a → abutmentPiece F n e p = ⊤) ∧
      (∀ p, b ≤ p → abutmentPiece F n e p = ⊥) := by
  obtain ⟨a,b,ha,hb⟩ := hF.finite n
  have heq (p : ℤ) : abutmentPiece F n e p =
      (Subobject.mapIsoToOrderIso e) (cohomologyPiece F p n) := by
    change Subobject.mk ((cohomologyPiece F p n).arrow ≫ e.hom) =
      (Subobject.map e.hom).obj (cohomologyPiece F p n)
    rw [← Subobject.map_mk, Subobject.mk_arrow]
  refine ⟨a,b,?_,?_⟩
  · intro p hp
    rw [heq, ha p hp]
    exact (Subobject.mapIsoToOrderIso e).map_top
  · intro p hp
    rw [heq, hb p hp]
    exact (Subobject.mapIsoToOrderIso e).map_bot
/-- Transport identifies the graded object with the source's image-filtration quotient. -/
def abutmentGradedIso (p : ℤ) :
    cokernel (Subobject.ofLE _ _ (abutmentPiece_decreasing F n e p)) ≅
      gradedCohomology F p n := by
  apply cokernel.mapIso (f := Subobject.ofLE _ _ (abutmentPiece_decreasing F n e p))
    (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))
    (Subobject.underlyingIso ((cohomologyPiece F (p+1) n).arrow ≫ e.hom))
    (Subobject.underlyingIso ((cohomologyPiece F p n).arrow ≫ e.hom))
  apply (cancel_mono ((cohomologyPiece F p n).arrow ≫ e.hom)).1
  dsimp only [abutmentPiece]
  simp only [Category.assoc, Subobject.ofLE_arrow_assoc]
  rw [Subobject.underlyingIso_hom_comp_eq_mk,
    Subobject.underlyingIso_hom_comp_eq_mk]
  exact Subobject.ofLE_arrow _


lemma natToIntDoubleComplex_inQuadrant
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) :
    InQuadrant (natToIntDoubleComplex K) 0 0 := by
  intro p q h
  by_cases hp : 0 ≤ p
  · have hq : ¬ 0 ≤ q := by tauto
    obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
    let J := (((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapHomologicalComplex (.up ℕ)).obj K
    let e : (natToIntDoubleComplex K).X (p' : ℤ) ≅ (K.X p').extend
        (ComplexShape.embeddingUpIntGE 0) :=
      J.extendXIso (ComplexShape.embeddingUpIntGE 0) (by simp)
    exact ((K.X p').isZero_extend_X (ComplexShape.embeddingUpIntGE 0) q
      (by intro n hn; simp at hn; omega)).of_iso
        ((HomologicalComplex.eval A (.up ℤ) q).mapIso e)
  · have hz := ((((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
      (ComplexShape.embeddingUpIntGE 0) p (by intro n hn; simp at hn; omega)
    exact (HomologicalComplex.eval A (.up ℤ) q).map_isZero hz

lemma natToIntDoubleComplex_finiteDiagonals
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) :
    FiniteDiagonals (natToIntDoubleComplex K) :=
  FiniteDiagonalFiltrations.quadrantFinite _ 0 0 (natToIntDoubleComplex_inQuadrant K)

/-- Finite convergence survives the identification of total cohomology with the abutment. -/
def columnAbutmentLimitIso (D : ColumnSpectralData K) {H : A} (n : ℤ)
    (e : (sumTotal K).homology n ≅ H) (r p : ℤ)
    (hs : Stabilized D.filtration r p n) :
    PageCohomology.object D.filtration D.pages r p n ≅
      cokernel (Subobject.ofLE _ _ (abutmentPiece_decreasing D.filtration n e p)) :=
  (FiniteFiltrationConvergence.limitIso D.filtration D.pages r p n hs).iso ≪≫
    (abutmentGradedIso D.filtration n e p).symm

lemma columnAbutmentLimitIso_representative (D : ColumnSpectralData K) {H : A} (n : ℤ)
    (e : (sumTotal K).homology n ≅ H) (r p : ℤ)
    (hs : Stabilized D.filtration r p n) :
    closedToPage D.filtration D.pages r p n ≫ (columnAbutmentLimitIso D n e r p hs).hom =
      closedClass D.filtration p n ≫
        (Subobject.underlyingIso ((cohomologyPiece D.filtration p n).arrow ≫ e.hom)).inv ≫
        cokernel.π (Subobject.ofLE _ _ (abutmentPiece_decreasing D.filtration n e p)) := by
  rw [columnAbutmentLimitIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    (FiniteFiltrationConvergence.limitIso D.filtration D.pages r p n hs).representative_formula]
  unfold gradedClass
  simp [abutmentGradedIso, Category.assoc]


@[simp] lemma natToIntDoubleComplexMap_id
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) :
    natToIntDoubleComplexMap (𝟙 K) = 𝟙 _ := by
  simp [natToIntDoubleComplexMap, natToIntDoubleComplex, HomologicalComplex.extendMap_id]

@[simp] lemma natToIntDoubleComplexMap_comp
    {K L M : HomologicalComplex₂ A (.up ℕ) (.up ℕ)} (f : K ⟶ L) (g : L ⟶ M) :
    natToIntDoubleComplexMap (f ≫ g) =
      natToIntDoubleComplexMap f ≫ natToIntDoubleComplexMap g := by
  simp [natToIntDoubleComplexMap, HomologicalComplex.extendMap_comp]

section GeneralMapExtend
variable {B : Type*} [Category* B] [HasZeroMorphisms B] [HasZeroObject B]
    {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (F : B ⥤ C) [F.PreservesZeroMorphisms] (K : HomologicalComplex B c)
    (e : c.Embedding c')

noncomputable def mapExtendXIso (o : Option ι) :
    F.obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) o :=
  match o with
  | some _ => Iso.refl _
  | none => F.mapZeroObject

noncomputable def mapExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun i => mapExtendXIso F K (e.r i)) (by
    intro i j h
    change (mapExtendXIso F K (e.r i)).hom ≫
        HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) (e.r i) (e.r j) =
      F.map (HomologicalComplex.extend.d K (e.r i) (e.r j)) ≫
        (mapExtendXIso F K (e.r j)).hom
    cases hi : e.r i <;> cases hj : e.r j <;>
      simp [mapExtendXIso, HomologicalComplex.extend.d])

end GeneralMapExtend
section DoubleTransport
variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable def natToIntDoubleComplexRowIso
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) (q : ℕ) :
    (natToIntDoubleComplex K).flip.X (q : ℤ) ≅
      (K.flip.X q).extend (ComplexShape.embeddingUpIntGE 0) :=
  mapExtendIso (HomologicalComplex.eval A (.up ℤ) (q : ℤ))
    ((((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapHomologicalComplex (.up ℕ)).obj K)
    (ComplexShape.embeddingUpIntGE 0) ≪≫
  ((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapIso
    ((NatIso.mapHomologicalComplex
      ((ComplexShape.embeddingUpIntGE 0).extendFunctorCompEvalIso A (by simp :
        (ComplexShape.embeddingUpIntGE 0).f q = (q : ℤ))) (.up ℕ)).app K)

noncomputable def natExtendHomologyIso (q : ℕ) :
    (ComplexShape.embeddingUpIntGE 0).extendFunctor A ⋙
      HomologicalComplex.homologyFunctor A (.up ℤ) (q : ℤ) ≅
        HomologicalComplex.homologyFunctor A (.up ℕ) q :=
  NatIso.ofComponents (fun K => K.extendHomologyIso (ComplexShape.embeddingUpIntGE 0) (by simp))
    (by intro K L f; exact HomologicalComplex.extendHomologyIso_hom_naturality _ _ _)

noncomputable def natToIntDoubleComplexVerticalHomologyIso
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) (q : ℕ) :
    DoubleComplexFirstPages.verticalHomology (natToIntDoubleComplex K) (q : ℤ) ≅
      (((HomologicalComplex.homologyFunctor A (.up ℕ) q).mapHomologicalComplex (.up ℕ)).obj K).extend
        (ComplexShape.embeddingUpIntGE 0) :=
  mapExtendIso (HomologicalComplex.homologyFunctor A (.up ℤ) (q : ℤ))
    ((((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapHomologicalComplex (.up ℕ)).obj K)
    (ComplexShape.embeddingUpIntGE 0) ≪≫
  ((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapIso
    ((NatIso.mapHomologicalComplex (natExtendHomologyIso (A := A) q) (.up ℕ)).app K)

end DoubleTransport

end SpectralData

section
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C] (S : ShortComplex A)
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

@[reassoc]
lemma homologyπ_mapHomologyIso :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  have hh : h.homologyIso.hom = 𝟙 _ := by
    change (S.leftHomologyIso.symm ≪≫ S.leftHomologyIso).hom = 𝟙 _
    simp
  have hp : S.homologyπ = h.cyclesIso.hom ≫ h.π := by
    simpa only [hh, Category.comp_id] using h.homologyπ_comp_homologyIso_hom S
  have hi : (h.map F).cyclesIso.hom = (S.mapCyclesIso F).hom ≫ F.map h.cyclesIso.hom := by
    apply (cancel_mono (F.map h.i)).1
    rw [Category.assoc, ← Functor.map_comp, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      ShortComplex.mapCyclesIso_hom_iCycles]
    exact (h.map F).cyclesIso_hom_comp_i
  change (S.map F).homologyπ ≫ (h.map F).homologyIso.hom = _
  rw [(h.map F).homologyπ_comp_homologyIso_hom, hi, hp, Functor.map_comp, Category.assoc]
  rfl

lemma mapHomologyIso_comp_hom (G : B ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  apply (cancel_epi ((S.map F).map G).homologyπ).1
  have hc : (S.mapCyclesIso (F ⋙ G)).hom =
      ((S.map F).mapCyclesIso G).hom ≫ G.map (S.mapCyclesIso F).hom := by
    apply (cancel_mono ((F ⋙ G).map S.iCycles)).1
    rw [ShortComplex.mapCyclesIso_hom_iCycles, Category.assoc]
    change _ = _ ≫ G.map (S.mapCyclesIso F).hom ≫ G.map (F.map S.iCycles)
    rw [← Functor.map_comp, ShortComplex.mapCyclesIso_hom_iCycles,
      ShortComplex.mapCyclesIso_hom_iCycles]
    rfl
  change (S.map (F ⋙ G)).homologyπ ≫ _ = _
  rw [homologyπ_mapHomologyIso, hc, Category.assoc]
  change _ ≫ G.map (S.mapCyclesIso F).hom ≫ G.map (F.map S.homologyπ) = _
  rw [← Functor.map_comp, ← homologyπ_mapHomologyIso, Functor.map_comp]
  rw [homologyπ_mapHomologyIso_assoc]
end

section IntegerSecondPage
variable {A : Type w} [Category.{v} A] [Abelian A]
noncomputable def verticalHomologyNatIso
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) (q : ℕ) :
    ((HomologicalComplex.homologyFunctor A (.up ℕ) q).mapHomologicalComplex (.up ℕ)).obj K ≅
      K.flip.homology q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (K.flip.sc q).mapHomologyIso (HomologicalComplex.eval A (.up ℕ) p)) (by
      intro p p' h
      have hh := congrArg (fun f => f ≫
        ((K.flip.sc q).mapHomologyIso (HomologicalComplex.eval A (.up ℕ) p')).hom)
        (CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.flip.sc q)
          (HomologicalComplex.dNatTrans A (.up ℕ) p p'))
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
      convert hh.symm using 1 <;> rfl)

section
variable {B : Type*} [Category* B] [HasZeroMorphisms B] [HasZeroObject B]
    {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
    {ι ι' : Type*} {d : ComplexShape ι} {d' : ComplexShape ι'}
    (F : B ⥤ C) [F.PreservesZeroMorphisms] (K : HomologicalComplex B d)
    (e : d.Embedding d')
lemma mapExtendXIso_hom (o : Option ι) {i : ι} (h : o = some i) :
    (mapExtendXIso F K o).hom ≫
      (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex d).obj K) h).hom =
    F.map (HomologicalComplex.extend.XIso K h).hom := by
  subst o
  simp [mapExtendXIso, HomologicalComplex.extend.XIso]
lemma mapExtendIso_hom_f {i : ι} {i' : ι'} (h : e.f i = i') :
    (mapExtendIso F K e).hom.f i' ≫
      (((F.mapHomologicalComplex d).obj K).extendXIso e h).hom =
    F.map (K.extendXIso e h).hom :=
  mapExtendXIso_hom F K (e.r i') (e.r_eq_some h)
end


lemma natToIntDoubleComplexVerticalHomologyIso_hom_f
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) (p q : ℕ) :
    (natToIntDoubleComplexVerticalHomologyIso K q).hom.f (p : ℤ) ≫
      ((((HomologicalComplex.homologyFunctor A (.up ℕ) q).mapHomologicalComplex
        (.up ℕ)).obj K).extendXIso (ComplexShape.embeddingUpIntGE 0)
        (by simp : (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))).hom =
    (HomologicalComplex.homologyMapIso
      (((((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapHomologicalComplex (.up ℕ)).obj K).extendXIso
        (ComplexShape.embeddingUpIntGE 0)
        (by simp : (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))) (q : ℤ)).hom ≫
      ((K.X p).extendHomologyIso (ComplexShape.embeddingUpIntGE 0) (j := q) (j' := (q : ℤ)) (by simp)).hom := by
  simp only [natToIntDoubleComplexVerticalHomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.comp_f, ComplexShape.Embedding.extendFunctor_map]
  rw [HomologicalComplex.extendMap_f _ _ (by simp :
    (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, mapExtendIso_hom_f]
  rfl

open TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory AdvancedHomologicalAlgebra.Cech
variable {X : TopCat.{u}} (R : RingSheaf X)
variable {U : Opens X} {B : Type v} (c : Cover U B)

def resolutionVerticalIntIso (M : Modules R) (I : InjectiveResolution M) (q : ℕ) :
    DoubleComplexFirstPages.verticalHomology (resolutionDoubleComplexInt R c M I) (q : ℤ) ≅
      (cechComplex R c ((localCohomology R q).obj M)).extend
        (ComplexShape.embeddingUpIntGE 0) :=
  natToIntDoubleComplexVerticalHomologyIso (resolutionDoubleComplex R c M I) q ≪≫
    ((ComplexShape.embeddingUpIntGE 0).extendFunctor _).mapIso
      (verticalHomologyNatIso (resolutionDoubleComplex R c M I) q ≪≫
        resolutionVerticalIso R c M I q)

def resolutionSecondIntIso (M : Modules R) (I : InjectiveResolution M) (p q : ℕ) :
    (DoubleComplexFirstPages.verticalHomology (resolutionDoubleComplexInt R c M I)
      (q : ℤ)).homology (p : ℤ) ≅ (localCechCohomology R c p q).obj M :=
  (HomologicalComplex.homologyFunctor _ (.up ℤ) (p : ℤ)).mapIso
    (resolutionVerticalIntIso R c M I q) ≪≫
      (cechComplex R c ((localCohomology R q).obj M)).extendHomologyIso
        (ComplexShape.embeddingUpIntGE 0) (by simp)

set_option maxHeartbeats 1000000 in
lemma resolutionVerticalIntIso_component (M : Modules R) (I : InjectiveResolution M)
    (p q : ℕ) :
    (resolutionVerticalIntIso R c M I q).hom.f (p : ℤ) ≫
      ((cechComplex R c ((localCohomology R q).obj M)).extendXIso
        (ComplexShape.embeddingUpIntGE 0) (i := p) (i' := (p : ℤ)) (by simp)).hom =
      (resolutionVerticalComponent R c M I p q).hom := by
  rw [resolutionVerticalIntIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f,
    ComplexShape.Embedding.extendFunctor_map]
  rw [HomologicalComplex.extendMap_f _ _ (by simp :
    (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, natToIntDoubleComplexVerticalHomologyIso_hom_f]
  simp only [Category.assoc, resolutionVerticalComponent, Iso.trans_hom,
    resolutionVerticalIso, HomologicalComplex.comp_f, Functor.mapIso_hom]
  let F := cochainFunctor R c
  let E := HomologicalComplex.eval (ModuleCat.{max u v} (sectionRing R U)) (.up ℕ) p
  let S := (underlyingComplex R I.cocomplex).sc q
  have he := mapHomologyIso_comp_hom S F E
  simp only [verticalHomologyNatIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    verticalCohomologyIso]
  rw [he]
  rfl

def resolutionVerticalComparison (M : Modules R) (I : InjectiveResolution M) :
    ResolutionVerticalComparison R c M I where
  exactTerm _ := inferInstance
  iso := resolutionVerticalIntIso R c M I
  component := resolutionVerticalIntIso_component R c M I

end IntegerSecondPage

def resolutionSpectralData (M : Modules R) (J : InjectiveResolution M) : ColumnSpectralData (resolutionDoubleComplexInt R c M J) :=
  columnSpectralData _ (natToIntDoubleComplex_finiteDiagonals _)

lemma resolutionSpectralData_firstQuadrant (M : Modules R) (J : InjectiveResolution M) (r p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero (DoubleComplexFirstPages.page (resolutionSpectralData R c M J).filtration
      (resolutionSpectralData R c M J).pages r p q) :=
  columnSpectralData_firstQuadrant _ (natToIntDoubleComplex_finiteDiagonals _)
    (natToIntDoubleComplex_inQuadrant _) r p q h

theorem resolution_spectral_core :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.resolutionSpectralCore := by
  intro X R U A c M J
  exact ⟨resolutionSpectralData R c M J, resolutionSpectralData_firstQuadrant R c M J⟩
lemma resolutionAugmentationNat_closed (M : Modules R) (I : InjectiveResolution M) :
    resolutionAugmentationNat R c M I ≫ (resolutionDoubleComplex R c M I).d 0 1 = 0 := by
  apply HomologicalComplex.hom_ext
  intro q
  change liftedAugmentation R c (I.cocomplex.X q).val ≫
    (cechComplex R c (I.cocomplex.X q).val).d 0 1 = 0
  rw [cechComplex_d]
  apply ModuleCat.hom_ext
  ext s
  obtain ⟨s⟩ := s
  change differential R (I.cocomplex.X q).val c 0
    (augmentation R (I.cocomplex.X q).val c s) = 0
  have h := CechCochains.augmentation_closed R (I.cocomplex.X q).val c
  exact congr($(h) s)

lemma resolutionAugmentation_closed (M : Modules R) (I : InjectiveResolution M)
    (q p : ℤ) (hp : (ComplexShape.up ℤ).Rel 0 p) :
    (resolutionAugmentation R c M I).f q ≫
      ((resolutionDoubleComplexInt R c M I).d 0 p).f q = 0 := by
  have hp' : p = 1 := by change 0 + 1 = p at hp; omega
  subst p
  let D := resolutionDoubleComplex R c M I
  let E := (((ComplexShape.embeddingUpIntGE 0).extendFunctor _).mapHomologicalComplex (.up ℕ)).obj D
  have h : resolutionAugmentation R c M I ≫
      (resolutionDoubleComplexInt R c M I).d 0 1 = 0 := by
    change (HomologicalComplex.extendMap (resolutionAugmentationNat R c M I) _ ≫
      (E.extendXIso (ComplexShape.embeddingUpIntGE 0) (by simp :
        (ComplexShape.embeddingUpIntGE 0).f 0 = 0)).inv) ≫
      (E.extend (ComplexShape.embeddingUpIntGE 0)).d 0 1 = 0
    rw [E.extend_d_eq (ComplexShape.embeddingUpIntGE 0)
      (by simp : (ComplexShape.embeddingUpIntGE 0).f 0 = 0)
      (by simp : (ComplexShape.embeddingUpIntGE 0).f 1 = 1)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change HomologicalComplex.extendMap (resolutionAugmentationNat R c M I) _ ≫
      HomologicalComplex.extendMap (D.d 0 1) _ ≫ _ = 0
    have hz : HomologicalComplex.extendMap (resolutionAugmentationNat R c M I)
        (ComplexShape.embeddingUpIntGE 0) ≫
        HomologicalComplex.extendMap (D.d 0 1) (ComplexShape.embeddingUpIntGE 0) = 0 := by
      rw [← HomologicalComplex.extendMap_comp]
      change HomologicalComplex.extendMap (resolutionAugmentationNat R c M I ≫
        (resolutionDoubleComplex R c M I).d 0 1) _ = 0
      rw [resolutionAugmentationNat_closed, HomologicalComplex.extendMap_zero]
    rw [← Category.assoc, hz, zero_comp]
  exact congrArg (fun t => t.f q) h


section AugmentationNaturality
variable {M N : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution N)
variable (φ : I.cocomplex ⟶ J.cocomplex)
lemma resolutionAugmentationNat_naturality :
    ((sectionLift R c).mapHomologicalComplex (.up ℕ)).map (sectionComplexMap R I J φ) ≫
      resolutionAugmentationNat R c N J =
      resolutionAugmentationNat R c M I ≫ (resolutionDoubleComplexMap R c I J φ).f 0 := by
  apply HomologicalComplex.hom_ext
  intro q
  exact (augmentation_cochainMap R c (φ.f q)).symm
lemma resolutionZeroColumnIso_naturality :
    (resolutionDoubleComplexIntMap R c I J φ).f 0 ≫ (resolutionZeroColumnIso R c N J).hom =
      (resolutionZeroColumnIso R c M I).hom ≫
        HomologicalComplex.extendMap ((resolutionDoubleComplexMap R c I J φ).f 0)
          (ComplexShape.embeddingUpIntGE 0) := by
  change (HomologicalComplex.extendMap _ _).f 0 ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (by simp :
    (ComplexShape.embeddingUpIntGE 0).f (0 : ℕ) = (0 : ℤ))]
  simp only [Category.assoc, resolutionZeroColumnIso, Iso.inv_hom_id, Category.comp_id]
  rfl
lemma resolutionAugmentation_naturality :
    sectionComplexIntMap R c I J φ ≫ resolutionAugmentation R c N J =
      resolutionAugmentation R c M I ≫ (resolutionDoubleComplexIntMap R c I J φ).f 0 := by
  dsimp only [sectionComplexIntMap, resolutionAugmentation]
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    resolutionAugmentationNat_naturality, HomologicalComplex.extendMap_comp]
  simp only [Category.assoc]
  congr 1
  apply (cancel_epi (resolutionZeroColumnIso R c M I).hom).1
  apply (cancel_mono (resolutionZeroColumnIso R c N J).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using
    (resolutionZeroColumnIso_naturality R c I J φ).symm
end AugmentationNaturality


def resolutionSecondPageIso (M : Modules R) (J : InjectiveResolution M) (p q : ℕ) :
    DoubleComplexFirstPages.page (resolutionSpectralData R c M J).filtration
      (resolutionSpectralData R c M J).pages 2 (p : ℤ) (q : ℤ) ≅
        (localCechCohomology R c p q).obj M :=
  columnSecondPageIso (resolutionSpectralData R c M J) p q ≪≫
    resolutionSecondIntIso R c M J p q

theorem resolution_second_page :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.resolutionSecondPage := by
  intro X R U A c M J
  exact ⟨resolutionSpectralData R c M J, resolutionSpectralData_firstQuadrant R c M J,
    fun p q => ⟨resolutionSecondPageIso R c M J p q⟩⟩

section ResolutionLiftIndependence
variable {A : Type u} [Category.{v} A] [Abelian A]
lemma extendMap_homology_eq {K L : CochainComplex A ℕ} (f g : K ⟶ L)
    (h : ∀ q, HomologicalComplex.homologyMap f q = HomologicalComplex.homologyMap g q)
    (q : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntGE 0)) q =
      HomologicalComplex.homologyMap (HomologicalComplex.extendMap g (ComplexShape.embeddingUpIntGE 0)) q := by
  by_cases hq : 0 ≤ q
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    apply (cancel_mono (L.extendHomologyIso (ComplexShape.embeddingUpIntGE 0) (by simp :
      (ComplexShape.embeddingUpIntGE 0).f q = (q : ℤ))).hom).1
    rw [HomologicalComplex.extendHomologyIso_hom_naturality,
      HomologicalComplex.extendHomologyIso_hom_naturality, h]
  · apply (ShortComplex.isZero_homology_of_isZero_X₂ ((K.extend (ComplexShape.embeddingUpIntGE 0)).sc q)
      (K.isZero_extend_X (ComplexShape.embeddingUpIntGE 0) q (by intro n hn; simp at hn; omega))).eq_of_src

lemma natToIntDoubleComplexMap_homology_eq
    {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)} (f g : K ⟶ L)
    (h : ∀ p q, HomologicalComplex.homologyMap (f.f p) q = HomologicalComplex.homologyMap (g.f p) q)
    (p q : ℤ) :
    HomologicalComplex.homologyMap ((natToIntDoubleComplexMap f).f p) q =
      HomologicalComplex.homologyMap ((natToIntDoubleComplexMap g).f p) q := by
  dsimp only [natToIntDoubleComplexMap]
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [HomologicalComplex.extendMap_f _ _ (by simp :
      (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ)),
      HomologicalComplex.extendMap_f _ _ (by simp :
      (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))]
    simp only [HomologicalComplex.homologyMap_comp]
    congr 1
    congr 1
    exact extendMap_homology_eq (f.f p) (g.f p) (h p) q
  · rw [HomologicalComplex.extendMap_f_eq_zero _ _ p (by intro n hn; simp at hn; omega),
      HomologicalComplex.extendMap_f_eq_zero _ _ p (by intro n hn; simp at hn; omega)]

variable {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {B : Type v} (c : Cover U B)
variable {M N : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution N)
def resolutionLiftHomotopy (f : M ⟶ N) (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) : Homotopy φ ψ := by
  apply InjectiveResolution.descHomotopy f
  · apply HomologicalComplex.from_single_hom_ext
    simpa using hφ
  · apply HomologicalComplex.from_single_hom_ext
    simpa using hψ

lemma resolutionDoubleComplexIntMap_homology_eq (f : M ⟶ N) (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (p q : ℤ) :
    HomologicalComplex.homologyMap ((resolutionDoubleComplexIntMap R c I J φ).f p) q =
      HomologicalComplex.homologyMap ((resolutionDoubleComplexIntMap R c I J ψ).f p) q := by
  apply natToIntDoubleComplexMap_homology_eq
  intro p q
  let F := SheafOfModules.forget R ⋙ termFunctor R c p
  have hh := (Functor.mapHomotopy F (resolutionLiftHomotopy R I J f φ ψ hφ hψ)).homologyMap_eq q
  exact hh
end ResolutionLiftIndependence

section TotalAugmentation
set_option backward.isDefEq.respectTransparency.types false

variable {X : TopCat.{u}} (R : RingSheaf X)
variable {U : Opens X} {A : Type v} (c : Cover U A)

section
variable {B : Type*} [Category* B] [Abelian B]
lemma natToIntDoubleComplexRowIso_hom_f
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) (p q : ℕ) :
    (natToIntDoubleComplexRowIso K q).hom.f (p : ℤ) ≫
      ((K.flip.X q).extendXIso (ComplexShape.embeddingUpIntGE 0)
        (by simp : (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))).hom =
    (((((ComplexShape.embeddingUpIntGE 0).extendFunctor B).mapHomologicalComplex (.up ℕ)).obj K).extendXIso
      (ComplexShape.embeddingUpIntGE 0)
      (by simp : (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))).hom.f (q : ℤ) ≫
      ((K.X p).extendXIso (ComplexShape.embeddingUpIntGE 0)
        (by simp : (ComplexShape.embeddingUpIntGE 0).f q = (q : ℤ))).hom := by
  simp only [natToIntDoubleComplexRowIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.comp_f, ComplexShape.Embedding.extendFunctor_map]
  rw [HomologicalComplex.extendMap_f _ _ (by simp :
    (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, mapExtendIso_hom_f]
  rfl
end

lemma resolutionAugmentation_rowIso (M : Modules R) (I : InjectiveResolution M) (q : ℕ) :
    (resolutionAugmentation R c M I).f (q : ℤ) ≫
      (natToIntDoubleComplexRowIso (resolutionDoubleComplex R c M I) q).hom.f 0 =
    ((liftedSectionComplex R c M I).extendXIso (ComplexShape.embeddingUpIntGE 0)
      (by simp : (ComplexShape.embeddingUpIntGE 0).f q = (q : ℤ))).hom ≫
      liftedAugmentation R c (I.cocomplex.X q).val ≫
      ((cechComplex R c (I.cocomplex.X q).val).extendXIso
        (ComplexShape.embeddingUpIntGE 0)
        (by simp : (ComplexShape.embeddingUpIntGE 0).f 0 = 0)).inv := by
  apply (cancel_mono ((cechComplex R c (I.cocomplex.X q).val).extendXIso
    (ComplexShape.embeddingUpIntGE 0)
    (by simp : (ComplexShape.embeddingUpIntGE 0).f 0 = 0)).hom).1
  rw [Category.assoc]
  refine (congrArg (fun t => (resolutionAugmentation R c M I).f (q : ℤ) ≫ t)
    (natToIntDoubleComplexRowIso_hom_f (resolutionDoubleComplex R c M I) 0 q)).trans ?_
  have hc : resolutionAugmentation R c M I ≫ (resolutionZeroColumnIso R c M I).hom =
      HomologicalComplex.extendMap (resolutionAugmentationNat R c M I)
        (ComplexShape.embeddingUpIntGE 0) := by
    simp [resolutionAugmentation]
  have hcq := congrArg (fun t => t.f (q : ℤ)) hc
  simp only [HomologicalComplex.comp_f] at hcq
  change (resolutionAugmentation R c M I).f (q : ℤ) ≫
    (resolutionZeroColumnIso R c M I).hom.f (q : ℤ) ≫
      (((resolutionDoubleComplex R c M I).X 0).extendXIso
        (ComplexShape.embeddingUpIntGE 0)
        (by simp : (ComplexShape.embeddingUpIntGE 0).f q = (q : ℤ))).hom = _
  rw [← Category.assoc, hcq, HomologicalComplex.extendMap_f _ _
    (by simp : (ComplexShape.embeddingUpIntGE 0).f q = (q : ℤ))]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The row single-map is exactly the extended injective Čech augmentation. -/
lemma resolutionRowLift_comp (M : Modules R) (I : InjectiveResolution M) (q : ℕ) :
    HomologicalComplex.mkHomFromSingle
      (K := (resolutionDoubleComplexInt R c M I).flip.X (q : ℤ)) (j := 0)
      ((resolutionAugmentation R c M I).f (q : ℤ))
      (resolutionAugmentation_closed R c M I (q : ℤ)) ≫
        (natToIntDoubleComplexRowIso (resolutionDoubleComplex R c M I) q).hom =
    (HomologicalComplex.single (ModuleCat.{max u v} (sectionRing R U)) (.up ℤ) 0).map
      (((liftedSectionComplex R c M I).extendXIso (ComplexShape.embeddingUpIntGE 0)
        (by simp : (ComplexShape.embeddingUpIntGE 0).f q = (q : ℤ))).hom) ≫
    (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntGE 0)
      ((sectionLift R c).obj ((I.cocomplex.X q).val.obj (op U))) 0 0 (by simp)).inv ≫
    HomologicalComplex.extendMap (augmentationFromSingle R c (I.cocomplex.X q))
      (ComplexShape.embeddingUpIntGE 0) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.single_map_f_self, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ _ (by simp :
      (ComplexShape.embeddingUpIntGE 0).f 0 = 0)]
  rw [Category.assoc, resolutionAugmentation_rowIso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [augmentationFromSingle, HomologicalComplex.mkHomFromSingle_f,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [liftedSectionComplex, sectionComplex, Functor.mapHomologicalComplex_obj_X,
    SheafOfModules.evaluation, Functor.comp_obj, PresheafOfModules.evaluation_obj]
  change _ = (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    ((sectionComplexInt R c M I).X (q : ℤ))).hom ≫
    ((liftedSectionComplex R c M I).extendXIso (ComplexShape.embeddingUpIntGE 0)
      (by simp : (ComplexShape.embeddingUpIntGE 0).f q = (q : ℤ))).hom ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((sectionLift R c).obj ((I.cocomplex.X q).val.obj (op U)))).inv ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((sectionLift R c).obj ((I.cocomplex.X q).val.obj (op U)))).hom ≫ _
  rw [Iso.inv_hom_id_assoc]
  rfl

lemma resolutionRowLift_quasiIso_nonneg (M : Modules R) (I : InjectiveResolution M) (q : ℕ) :
    QuasiIso (HomologicalComplex.mkHomFromSingle
      (K := (resolutionDoubleComplexInt R c M I).flip.X (q : ℤ)) (j := 0)
      ((resolutionAugmentation R c M I).f (q : ℤ))
      (resolutionAugmentation_closed R c M I (q : ℤ))) := by
  have := augmented_quasiIso R c (I.cocomplex.X q)
  have hh : QuasiIso (HomologicalComplex.mkHomFromSingle
      (K := (resolutionDoubleComplexInt R c M I).flip.X (q : ℤ)) (j := 0)
      ((resolutionAugmentation R c M I).f (q : ℤ))
      (resolutionAugmentation_closed R c M I (q : ℤ)) ≫
        (natToIntDoubleComplexRowIso (resolutionDoubleComplex R c M I) q).hom) := by
    rw [resolutionRowLift_comp]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).1 hh

lemma resolutionRowLift_quasiIso (M : Modules R) (I : InjectiveResolution M) (q : ℤ) :
    QuasiIso (HomologicalComplex.mkHomFromSingle
      (K := (resolutionDoubleComplexInt R c M I).flip.X q) (j := 0)
      ((resolutionAugmentation R c M I).f q)
      (resolutionAugmentation_closed R c M I q)) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact resolutionRowLift_quasiIso_nonneg R c M I q
  · have hzS : IsZero ((sectionComplexInt R c M I).X q) :=
      (liftedSectionComplex R c M I).isZero_extend_X (ComplexShape.embeddingUpIntGE 0)
        q (by intro n hn; simp at hn; omega)
    have hzSingle := (HomologicalComplex.single (ModuleCat.{max u v} (sectionRing R U))
      (.up ℤ) 0).map_isZero hzS
    rw [quasiIso_iff]
    intro p
    apply (quasiIsoAt_iff_isIso_homologyMap _ _).2
    have hzSource := (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} (sectionRing R U))
      (.up ℤ) p).map_isZero hzSingle
    have hzTarget : IsZero (((resolutionDoubleComplexInt R c M I).flip.X q).homology p) :=
      (HomologicalComplex.ExactAt.of_isZero
        (K := (resolutionDoubleComplexInt R c M I).flip.X q) (i := p)
        (natToIntDoubleComplex_inQuadrant (resolutionDoubleComplex R c M I) p q
          (by omega))).isZero_homology
    exact hzSource.isIso hzTarget _

open DoubleTotalization FiniteDiagonalFiltrations

/-- Exact injective Čech rows assemble to the actual sum-total augmentation. -/
theorem resolution_total_augmentation (M : Modules R) (I : InjectiveResolution M) :
    ∃ α : sectionComplexInt R c M I ⟶
        sumTotal (resolutionDoubleComplexInt R c M I), QuasiIso α ∧
      ∀ n, α.f n = (resolutionAugmentation R c M I).f n ≫
        sumInjection (resolutionDoubleComplexInt R c M I) 0 n n (zero_add n) := by
  apply AugmentedDoubleComplexComparison.cochain_row_assembly
    (resolutionDoubleComplexInt R c M I)
    (natToIntDoubleComplex_finiteDiagonals (resolutionDoubleComplex R c M I))
    (fun p q hp => natToIntDoubleComplex_inQuadrant (resolutionDoubleComplex R c M I)
      p q (by omega))
    (sectionComplexInt R c M I)
    (resolutionAugmentation R c M I)
    (resolutionAugmentation_closed R c M I)
  · intro q
    have := resolutionRowLift_quasiIso R c M I q
    infer_instance
  · intro q p hp
    have := resolutionRowLift_quasiIso R c M I q
    exact (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
      ((sectionComplexInt R c M I).X q) p hp).of_iso
      (asIso (HomologicalComplex.homologyMap (HomologicalComplex.mkHomFromSingle
        (K := (resolutionDoubleComplexInt R c M I).flip.X q) (j := 0)
        ((resolutionAugmentation R c M I).f q)
        (resolutionAugmentation_closed R c M I q)) p)).symm

end TotalAugmentation

theorem total_augmentation :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.totalAugmentation := by
  intro X R U A c M J
  exact resolution_total_augmentation R c M J

section IntegerNaturality

variable {A : Type u} [Category.{v} A] [Abelian A]

section GeneralNaturality
variable {B : Type*} [Category* B] [HasZeroMorphisms B] [HasZeroObject B]
    {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (F : B ⥤ C) [F.PreservesZeroMorphisms]
    {K L : HomologicalComplex B c} (f : K ⟶ L) (e : c.Embedding c')

@[reassoc] lemma mapExtendIso_naturality :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap f e) ≫
      (mapExtendIso F L e).hom =
    (mapExtendIso F K e).hom ≫
      HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map f) e := by
  ext i
  change F.map (HomologicalComplex.extend.mapX f (e.r i)) ≫
      (mapExtendXIso F L (e.r i)).hom =
    (mapExtendXIso F K (e.r i)).hom ≫
      HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map f) (e.r i)
  cases hi : e.r i <;> simp [mapExtendXIso, HomologicalComplex.extend.mapX]

end GeneralNaturality

@[reassoc] lemma verticalHomologyNatIso_naturality
    {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)} (f : K ⟶ L) (q : ℕ) :
    ((HomologicalComplex.homologyFunctor A (.up ℕ) q).mapHomologicalComplex (.up ℕ)).map f ≫
      (verticalHomologyNatIso L q).hom =
    (verticalHomologyNatIso K q).hom ≫
      HomologicalComplex.homologyMap
        ((HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map f) q := by
  ext p
  have hh := CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map
      ((HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map f))
    (HomologicalComplex.eval A (.up ℕ) p)
  convert hh using 1 <;> rfl

@[reassoc] lemma natToIntDoubleComplexVerticalHomologyIso_naturality
    {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)} (f : K ⟶ L) (q : ℕ) :
    DoubleComplexFirstPages.verticalHomologyMap (natToIntDoubleComplex K)
      (natToIntDoubleComplexMap f) (q : ℤ) ≫
        (natToIntDoubleComplexVerticalHomologyIso L q).hom =
    (natToIntDoubleComplexVerticalHomologyIso K q).hom ≫
      HomologicalComplex.extendMap
        (((HomologicalComplex.homologyFunctor A (.up ℕ) q).mapHomologicalComplex (.up ℕ)).map f)
        (ComplexShape.embeddingUpIntGE 0) := by
  dsimp only [natToIntDoubleComplexVerticalHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc]
  change (((HomologicalComplex.homologyFunctor A (.up ℤ) (q : ℤ)).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap
        ((((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapHomologicalComplex (.up ℕ)).map f)
        (ComplexShape.embeddingUpIntGE 0)) ≫ _) ≫ _ = _
  rw [mapExtendIso_naturality, Category.assoc]
  let e := ComplexShape.embeddingUpIntGE 0
  let E := e.extendFunctor A
  let α := NatIso.mapHomologicalComplex (natExtendHomologyIso (A := A) q) (.up ℕ)
  have hh := congrArg (fun g => E.map g) (α.hom.naturality f)
  simp only [Functor.map_comp] at hh
  simp only [Category.assoc]
  convert congrArg (fun g => (mapExtendIso
    (HomologicalComplex.homologyFunctor A (.up ℤ) (q : ℤ))
    ((E.mapHomologicalComplex (.up ℕ)).obj K) e).hom ≫ g) hh using 1 <;> rfl

open TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory AdvancedHomologicalAlgebra.Cech
variable {X : TopCat.{u}} (R : RingSheaf X)
variable {U : Opens X} {B : Type v} (c : Cover U B)

@[reassoc] lemma resolutionVerticalIntIso_naturality
    (M N : Modules R) (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    DoubleComplexFirstPages.verticalHomologyMap (resolutionDoubleComplexInt R c M I)
      (resolutionDoubleComplexIntMap R c I J φ) (q : ℤ) ≫
        (resolutionVerticalIntIso R c N J q).hom =
    (resolutionVerticalIntIso R c M I q).hom ≫
      HomologicalComplex.extendMap ((cochainFunctor R c).map ((localCohomology R q).map f))
        (ComplexShape.embeddingUpIntGE 0) := by
  let K := resolutionDoubleComplex R c M I
  let L := resolutionDoubleComplex R c N J
  let ψ := resolutionDoubleComplexMap R c I J φ
  let E := (ComplexShape.embeddingUpIntGE 0).extendFunctor
    (ModuleCat.{max u v} (sectionRing R U))
  have hn :
      ((HomologicalComplex.homologyFunctor _ (.up ℕ) q).mapHomologicalComplex (.up ℕ)).map ψ ≫
        (verticalHomologyNatIso L q ≪≫ resolutionVerticalIso R c N J q).hom =
      (verticalHomologyNatIso K q ≪≫ resolutionVerticalIso R c M I q).hom ≫
        (cochainFunctor R c).map ((localCohomology R q).map f) := by
    dsimp only [Iso.trans_hom]
    rw [← Category.assoc, verticalHomologyNatIso_naturality, Category.assoc]
    have hh := resolutionVerticalIso_naturality R c M N f I J φ hφ q
    have hh' := congrArg (fun g => (verticalHomologyNatIso K q).hom ≫ g) hh
    simp only [Category.assoc] at hh' ⊢
    convert hh' using 1 <;> rfl
  dsimp only [resolutionVerticalIntIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc]
  change (DoubleComplexFirstPages.verticalHomologyMap (natToIntDoubleComplex K)
      (natToIntDoubleComplexMap ψ) (q : ℤ) ≫ _) ≫ _ = _
  rw [natToIntDoubleComplexVerticalHomologyIso_naturality, Category.assoc]
  have hh := congrArg E.map hn
  simp only [Functor.map_comp] at hh
  simp only [Category.assoc]
  convert congrArg (fun g => (natToIntDoubleComplexVerticalHomologyIso K q).hom ≫ g) hh using 1 <;> rfl

@[reassoc] lemma resolutionSecondIntIso_naturality
    (M N : Modules R) (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (p q : ℕ) :
    HomologicalComplex.homologyMap
      (DoubleComplexFirstPages.verticalHomologyMap (resolutionDoubleComplexInt R c M I)
        (resolutionDoubleComplexIntMap R c I J φ) (q : ℤ)) (p : ℤ) ≫
          (resolutionSecondIntIso R c N J p q).hom =
    (resolutionSecondIntIso R c M I p q).hom ≫ (localCechCohomology R c p q).map f := by
  have hn := congrArg (fun g => HomologicalComplex.homologyMap g (p : ℤ))
    (resolutionVerticalIntIso_naturality R c M N f I J φ hφ q)
  simp only [HomologicalComplex.homologyMap_comp] at hn
  dsimp only [resolutionSecondIntIso, Iso.trans_hom, Functor.mapIso_hom]
  change _ ≫ HomologicalComplex.homologyMap (resolutionVerticalIntIso R c N J q).hom (p : ℤ) ≫ _ = _
  rw [← Category.assoc, hn, Category.assoc]
  have he := HomologicalComplex.extendHomologyIso_hom_naturality
    ((cochainFunctor R c).map ((localCohomology R q).map f))
    (ComplexShape.embeddingUpIntGE 0) (by simp :
      (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))
  have he' := congrArg (fun g => HomologicalComplex.homologyMap
    (resolutionVerticalIntIso R c M I q).hom (p : ℤ) ≫ g) he
  simp only [Category.assoc] at he' ⊢
  convert he' using 1 <;> rfl


end IntegerNaturality

section ResolutionPageMaps

variable {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {A : Type v} (c : Cover U A)
@[simp] lemma resolutionDoubleComplexMap_id (M : Modules R) (I : InjectiveResolution M) :
    resolutionDoubleComplexMap R c I I (𝟙 I.cocomplex) = 𝟙 _ := by
  simp [resolutionDoubleComplexMap, resolutionDoubleComplex]
@[simp] lemma resolutionDoubleComplexMap_comp {M N P : Modules R}
    (I : InjectiveResolution M) (J : InjectiveResolution N) (L : InjectiveResolution P)
    (φ : I.cocomplex ⟶ J.cocomplex) (ψ : J.cocomplex ⟶ L.cocomplex) :
    resolutionDoubleComplexMap R c I L (φ ≫ ψ) =
      resolutionDoubleComplexMap R c I J φ ≫ resolutionDoubleComplexMap R c J L ψ := by
  simp [resolutionDoubleComplexMap]
@[simp] lemma resolutionDoubleComplexIntMap_id (M : Modules R) (I : InjectiveResolution M) :
    resolutionDoubleComplexIntMap R c I I (𝟙 I.cocomplex) = 𝟙 _ := by
  simp [resolutionDoubleComplexIntMap, resolutionDoubleComplexInt]
@[simp] lemma resolutionDoubleComplexIntMap_comp {M N P : Modules R}
    (I : InjectiveResolution M) (J : InjectiveResolution N) (L : InjectiveResolution P)
    (φ : I.cocomplex ⟶ J.cocomplex) (ψ : J.cocomplex ⟶ L.cocomplex) :
    resolutionDoubleComplexIntMap R c I L (φ ≫ ψ) =
      resolutionDoubleComplexIntMap R c I J φ ≫ resolutionDoubleComplexIntMap R c J L ψ := by
  simp [resolutionDoubleComplexIntMap]

def resolutionPageMapData {M N : Modules R}
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex) :=
  columnPageMapData (resolutionSpectralData R c M I) (resolutionSpectralData R c N J)
    (resolutionDoubleComplexIntMap R c I J φ)
lemma resolutionPageMapData_id (M : Modules R) (I : InjectiveResolution M) (r p n : ℤ) (hr : 0 ≤ r) :
    (resolutionPageMapData R c I I (𝟙 I.cocomplex)).map r p n = 𝟙 _ := by
  dsimp only [resolutionPageMapData]
  rw [resolutionDoubleComplexIntMap_id]
  exact columnPageMap_id _ r p n
lemma resolutionPageMapData_comp {M N P : Modules R}
    (I : InjectiveResolution M) (J : InjectiveResolution N) (L : InjectiveResolution P)
    (φ : I.cocomplex ⟶ J.cocomplex) (ψ : J.cocomplex ⟶ L.cocomplex)
    (r p n : ℤ) (hr : 0 ≤ r) :
    (resolutionPageMapData R c I L (φ ≫ ψ)).map r p n =
      (resolutionPageMapData R c I J φ).map r p n ≫ (resolutionPageMapData R c J L ψ).map r p n := by
  dsimp only [resolutionPageMapData]
  rw [resolutionDoubleComplexIntMap_comp]
  exact columnPageMap_comp _ _ _ _ _ r p n
lemma resolutionPageMapData_lift_independent {M N : Modules R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    (resolutionPageMapData R c I J φ).map r p n =
      (resolutionPageMapData R c I J ψ).map r p n :=
  columnPageMap_lift_independent _ _ _ _
    (resolutionDoubleComplexIntMap_homology_eq R c I J f φ ψ hφ hψ) r hr p n
end ResolutionPageMaps

section SelectedTotalAugmentation

variable {X : TopCat.{u}} (R : RingSheaf X)
variable {U : Opens X} {A : Type v} (c : Cover U A)
open DoubleTotalization FiniteDiagonalFiltrations
/-- The canonical axis formula makes the assembled quasi-isomorphism unique. -/
def resolutionTotalAugmentation (M : Modules R) (I : InjectiveResolution M) :
    sectionComplexInt R c M I ⟶ sumTotal (resolutionDoubleComplexInt R c M I) :=
  (resolution_total_augmentation R c M I).choose

instance resolutionTotalAugmentation_quasiIso (M : Modules R) (I : InjectiveResolution M) :
    QuasiIso (resolutionTotalAugmentation R c M I) :=
  (resolution_total_augmentation R c M I).choose_spec.1

lemma resolutionTotalAugmentation_f (M : Modules R) (I : InjectiveResolution M) (n : ℤ) :
    (resolutionTotalAugmentation R c M I).f n = (resolutionAugmentation R c M I).f n ≫
      sumInjection (resolutionDoubleComplexInt R c M I) 0 n n (zero_add n) :=
  (resolution_total_augmentation R c M I).choose_spec.2 n

lemma resolutionTotalAugmentation_naturality {M N : Modules R}
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex) :
    sectionComplexIntMap R c I J φ ≫ resolutionTotalAugmentation R c N J =
      resolutionTotalAugmentation R c M I ≫ HomologicalComplex₂.total.map
        (resolutionDoubleComplexIntMap R c I J φ) (.up ℤ) :=
  rowTotalAugmentation_naturality (resolutionAugmentation R c M I)
    (resolutionAugmentation R c N J) (resolutionTotalAugmentation R c M I)
    (resolutionTotalAugmentation R c N J) (resolutionTotalAugmentation_f R c M I)
    (resolutionTotalAugmentation_f R c N J) (sectionComplexIntMap R c I J φ)
    (resolutionDoubleComplexIntMap R c I J φ) (resolutionAugmentation_naturality R c I J φ)

lemma resolutionTotalMap_homology_lift_independent {M N : Modules R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (n : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (resolutionDoubleComplexIntMap R c I J φ) (.up ℤ)) n =
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (resolutionDoubleComplexIntMap R c I J ψ) (.up ℤ)) n := by
  apply total_homologyMap_eq_of_augmentation (resolutionTotalAugmentation R c M I)
    (resolutionTotalAugmentation R c N J) (sectionComplexIntMap R c I J φ)
    (sectionComplexIntMap R c I J ψ) (resolutionDoubleComplexIntMap R c I J φ)
    (resolutionDoubleComplexIntMap R c I J ψ)
    (resolutionTotalAugmentation_naturality R c I J φ)
    (resolutionTotalAugmentation_naturality R c I J ψ) n
  apply extendMap_homology_eq
  intro q
  exact (Functor.mapHomotopy (SheafOfModules.evaluation R (op U) ⋙ sectionLift R c)
    (resolutionLiftHomotopy R I J f φ ψ hφ hψ)).homologyMap_eq q

end SelectedTotalAugmentation

section H01Bridge
open CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
section IntModels
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]

def plusStalk (M : A) : CochainComplex.Plus A :=
  ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩

lemma intUnit_isIso (F : A ⥤ B) [F.Additive] (I : CochainComplex.Plus A)
    (hI : ∀ q : ℤ, Injective (I.obj.X q)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app I) := by
  letI := hI
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  infer_instance

def intComputationDerivedIso (F : A ⥤ B) [F.Additive] (M : A)
    (I : CochainComplex.Plus A) (ι : plusStalk M ⟶ I)
    (hι : QuasiIso ι.hom) (hI : ∀ q : ℤ, Injective (I.obj.X q)) :
    F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj (plusStalk M)) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I) := by
  letI := hι
  letI := intUnit_isIso F I hI
  letI : IsIso (DerivedCategory.Plus.Q.map ι) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso A) ι hι
  exact F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map ι)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app I)).symm

lemma intComputationDerivedIso_naturality (F : A ⥤ B) [F.Additive]
    (M N : A) (f : M ⟶ N) (I J : CochainComplex.Plus A)
    (ι : plusStalk M ⟶ I) (κ : plusStalk N ⟶ J)
    (hι : QuasiIso ι.hom) (hκ : QuasiIso κ.hom)
    (hI : ∀ q : ℤ, Injective (I.obj.X q)) (hJ : ∀ q : ℤ, Injective (J.obj.X q))
    (φ : I ⟶ J)
    (hφ : ι ≫ φ = (CochainComplex.plus A).homMk ((CochainComplex.singleFunctor A 0).map f) ≫ κ) :
    F.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ((CochainComplex.plus A).homMk
          ((CochainComplex.singleFunctor A 0).map f))) ≫
        (intComputationDerivedIso F N J κ hκ hJ).hom =
      (intComputationDerivedIso F M I ι hι hI).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) := by
  letI := intUnit_isIso F I hI
  letI := intUnit_isIso F J hJ
  dsimp [intComputationDerivedIso]
  apply (cancel_mono (F.rightDerivedFunctorPlusUnit.app J)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hu := F.rightDerivedFunctorPlusUnit.naturality φ
  dsimp only [Functor.comp_map] at hu
  rw [hu]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← F.rightDerivedFunctorPlus.map_comp, ← DerivedCategory.Plus.Q.map_comp,
    ← hφ, DerivedCategory.Plus.Q.map_comp, F.rightDerivedFunctorPlus.map_comp]

def intComputationIso (F : A ⥤ B) [F.Additive] (M : A)
    (I : CochainComplex.Plus A) (ι : plusStalk M ⟶ I)
    (hι : QuasiIso ι.hom) (hI : ∀ q : ℤ, Injective (I.obj.X q)) (q : ℕ) :
    (rightValue F q).obj M ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj I.obj).homology (q : ℤ) :=
  (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).mapIso
    (intComputationDerivedIso F M I ι hι hI) ≪≫
      (DerivedCategory.homologyFunctorFactors B (q : ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj I.obj)

lemma intComputationIso_naturality (F : A ⥤ B) [F.Additive]
    (M N : A) (f : M ⟶ N) (I J : CochainComplex.Plus A)
    (ι : plusStalk M ⟶ I) (κ : plusStalk N ⟶ J)
    (hι : QuasiIso ι.hom) (hκ : QuasiIso κ.hom)
    (hI : ∀ q : ℤ, Injective (I.obj.X q)) (hJ : ∀ q : ℤ, Injective (J.obj.X q))
    (φ : I ⟶ J)
    (hφ : ι ≫ φ = (CochainComplex.plus A).homMk ((CochainComplex.singleFunctor A 0).map f) ≫ κ)
    (q : ℕ) :
    (rightValue F q).map f ≫ (intComputationIso F N J κ hκ hJ q).hom =
      (intComputationIso F M I ι hι hI q).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom) (q : ℤ) := by
  have h := congrArg (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
    (intComputationDerivedIso_naturality F M N f I J ι κ hι hκ hI hJ φ hφ)
  simp only [Functor.map_comp] at h
  change (rightValue F q).map f ≫
      (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
        (intComputationDerivedIso F N J κ hκ hJ).hom =
    (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
        (intComputationDerivedIso F M I ι hι hI).hom ≫
      (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
        (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ)) at h
  dsimp only [intComputationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h, Category.assoc]
  have hn := (DerivedCategory.homologyFunctorFactors B (q : ℤ)).hom.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map φ.hom)
  change (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ)) ≫
      (DerivedCategory.homologyFunctorFactors B (q : ℤ)).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J.obj) =
    (DerivedCategory.homologyFunctorFactors B (q : ℤ)).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom) (q : ℤ) at hn
  have hh := congrArg (fun z ↦
    (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
      (intComputationDerivedIso F M I ι hι hI).hom ≫ z) hn
  simp only [Category.assoc] at *
  convert hh using 1 <;> rfl


lemma mapExtendIso_hom_naturality {K L : CochainComplex A ℕ} (F : A ⥤ B) [F.Additive]
    (φ : K ⟶ L) (e : (ComplexShape.up ℕ).Embedding (.up ℤ)) :
    (F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap φ e) ≫
      (mapExtendIso F L e).hom =
    (mapExtendIso F K e).hom ≫
      HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ) e := by
  ext i
  change F.map (HomologicalComplex.extend.mapX φ (e.r i)) ≫ (mapExtendXIso F L (e.r i)).hom =
    (mapExtendXIso F K (e.r i)).hom ≫
      HomologicalComplex.extend.mapX ((F.mapHomologicalComplex (.up ℕ)).map φ) (e.r i)
  cases e.r i <;> simp [mapExtendXIso, HomologicalComplex.extend.mapX]

def natResolutionPlus {M : A} (I : InjectiveResolution M) : CochainComplex.Plus A :=
  ⟨I.cochainComplex, 0, inferInstance⟩

def natResolutionPlusι {M : A} (I : InjectiveResolution M) :
    plusStalk M ⟶ natResolutionPlus I :=
  (CochainComplex.plus A).homMk I.ι'

def natComputationIso (F : A ⥤ B) [F.Additive] (M : A)
    (I : InjectiveResolution M) (q : ℕ) :
    (rightValue F q).obj M ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology q :=
  intComputationIso F M (natResolutionPlus I) (natResolutionPlusι I)
    (by exact inferInstanceAs (QuasiIso I.ι')) (fun n => by dsimp [natResolutionPlus]; infer_instance) q ≪≫
    (HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).mapIso
      (mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat) ≪≫
    ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat rfl

lemma natComputationIso_naturality (F : A ⥤ B) [F.Additive]
    (M N : A) (f : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    (rightValue F q).map f ≫ (natComputationIso F N J q).hom =
      (natComputationIso F M I q).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) q := by
  let ψ : InjectiveResolution.Hom I J f := ⟨φ, by simpa using hφ⟩
  have hi := intComputationIso_naturality F M N f (natResolutionPlus I) (natResolutionPlus J)
    (natResolutionPlusι I) (natResolutionPlusι J) (by exact inferInstanceAs (QuasiIso I.ι'))
    (by exact inferInstanceAs (QuasiIso J.ι')) (fun n => by dsimp [natResolutionPlus]; infer_instance)
    (fun n => by dsimp [natResolutionPlus]; infer_instance)
    ((CochainComplex.plus A).homMk ψ.hom') (by
      apply (CochainComplex.plus A).hom_ext
      exact ψ.ι'_comp_hom') q
  have he := congrArg (HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).map
    (mapExtendIso_hom_naturality F φ ComplexShape.embeddingUpNat)
  simp only [Functor.map_comp] at he
  change HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map ψ.hom') (q : ℤ) ≫
      (HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).map
        (mapExtendIso F J.cocomplex ComplexShape.embeddingUpNat).hom =
    (HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).map
        (mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.homologyMap (HomologicalComplex.extendMap
        ((F.mapHomologicalComplex (.up ℕ)).map φ) ComplexShape.embeddingUpNat) (q : ℤ) at he
  have hn := HomologicalComplex.extendHomologyIso_hom_naturality
    ((F.mapHomologicalComplex (.up ℕ)).map φ) ComplexShape.embeddingUpNat (j := q) (hj' := rfl)
  dsimp only [natComputationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, hi, Category.assoc, Category.assoc]
  rw [← Category.assoc _ _ (((F.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).hom]
  erw [he]
  simp only [Category.assoc]
  erw [hn]


def natRightDerivedIso (F : A ⥤ B) [F.Additive] (q : ℕ) :
    rightValue F q ≅ F.rightDerived q :=
  NatIso.ofComponents (fun M => natComputationIso F M (injectiveResolution M) q ≪≫
    ((injectiveResolution M).isoRightDerivedObj F q).symm) (by
      intro M N f
      let I := injectiveResolution M
      let J := injectiveResolution N
      let φ := InjectiveResolution.desc f J I
      have hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 := by
        simpa [φ] using congrArg (fun z => z.f 0) (InjectiveResolution.desc_commutes f J I)
      have hi := natComputationIso_naturality F M N f I J φ hφ q
      have hn := InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ hφ F q
      change (rightValue F q).map f ≫
          ((natComputationIso F N J q).hom ≫ (J.isoRightDerivedObj F q).inv) =
        ((natComputationIso F M I q).hom ≫ (I.isoRightDerivedObj F q).inv) ≫
          (F.rightDerived q).map f
      apply (cancel_mono (J.isoRightDerivedObj F q).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hn]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact hi)

end IntModels
section Sections
open TopologicalSpace Opposite
variable {X : TopCat.{u}} (R : RingSheaf X)

def localH01SectionsIso (V : Opens X) (q : ℕ) :
    localCohomology R q ⋙ PresheafOfModules.evaluation R.obj (op V) ≅
      sectionCohomology R V q := by
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R V))
  exact localSectionsIso R V q ≪≫
    (natRightDerivedIso (SheafOfModules.evaluation R (op V)) q).symm


def sectionCohomologyResolutionIso (V : Opens X) (M : Modules R)
    (I : InjectiveResolution M) (q : ℕ) :
    (sectionCohomology R V q).obj M ≅ (sectionComplex R (U := V) M I).homology q := by
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R V))
  exact natComputationIso (SheafOfModules.evaluation R (op V)) M I q

open private evaluationExtendIso evaluationExtendComponent from MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechToCohomology
open private evaluationExtendIso evaluationExtendComponent from MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechToCohomology
lemma sectionCohomologyResolutionIso_eq (V : Opens X) (M : Modules R)
    (I : InjectiveResolution M) (q : ℕ) :
    sectionCohomologyResolutionIso R V M I q = sectionResolutionIsoNat R V M I q := by
  have h : mapExtendIso (SheafOfModules.evaluation R (op V)) I.cocomplex
      ComplexShape.embeddingUpNat = evaluationExtendIso R V I.cocomplex := by
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro i
    change (mapExtendXIso (SheafOfModules.evaluation R (op V)) I.cocomplex
      (ComplexShape.embeddingUpNat.r i)).hom = (evaluationExtendComponent R V I.cocomplex
        (ComplexShape.embeddingUpNat.r i)).hom
    cases ComplexShape.embeddingUpNat.r i <;> rfl
  apply Iso.ext
  simp only [sectionCohomologyResolutionIso, sectionResolutionIsoNat, natComputationIso,
    intComputationIso, intComputationDerivedIso, Iso.trans_hom, Functor.mapIso_hom, h]
  rfl

lemma sectionCohomologyResolutionIso_naturality (V : Opens X) (M N : Modules R)
    (f : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    (sectionCohomology R V q).map f ≫ (sectionCohomologyResolutionIso R V N J q).hom =
      (sectionCohomologyResolutionIso R V M I q).hom ≫
        HomologicalComplex.homologyMap (sectionComplexMap R (U := V) I J φ) q := by
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R V))
  exact natComputationIso_naturality (SheafOfModules.evaluation R (op V)) M N f I J φ hφ q

end Sections
end H01Bridge

section CechAbutment
set_option backward.isDefEq.respectTransparency.types false

variable {X : TopCat.{u}} (R : RingSheaf X)
variable {U : Opens X} {A : Type v} (c : Cover U A)
open DoubleTotalization FiniteDiagonalFiltrations

lemma liftedSectionHomologyIso_naturality {M N : Modules R}
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) :
    HomologicalComplex.homologyMap (sectionComplexIntMap R c I J φ) (n : ℤ) ≫
        (liftedSectionHomologyIso R c N J n).hom =
      (liftedSectionHomologyIso R c M I n).hom ≫
        (sectionLift R c).map (HomologicalComplex.homologyMap
          (sectionComplexMap R (U := U) I J φ) n) := by
  let F := sectionLift R c
  let g := sectionComplexMap R (U := U) I J φ
  let g' := (F.mapHomologicalComplex (.up ℕ)).map g
  have h₁ := HomologicalComplex.extendHomologyIso_hom_naturality g'
    (ComplexShape.embeddingUpIntGE 0) (j := n) (j' := (n : ℤ)) (hj' := by simp)
  have h₂ := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map g) F
  change HomologicalComplex.homologyMap g' n ≫
      (((sectionComplex R (U := U) N J).sc n).mapHomologyIso F).hom =
    (((sectionComplex R (U := U) M I).sc n).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap g n) at h₂
  dsimp only [liftedSectionHomologyIso, Iso.trans_hom]
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

def sectionComputationIso (M : Modules R) (I : InjectiveResolution M) (n : ℕ) :
    (liftedSectionCohomology R c n).obj M ≅ (sectionComplexInt R c M I).homology (n : ℤ) :=
  (sectionLift R c).mapIso (sectionCohomologyResolutionIso R U M I n) ≪≫
    (liftedSectionHomologyIso R c M I n).symm

lemma sectionComputationIso_naturality (M N : Modules R) (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    (liftedSectionCohomology R c n).map f ≫ (sectionComputationIso R c N J n).hom =
      (sectionComputationIso R c M I n).hom ≫
        HomologicalComplex.homologyMap (sectionComplexIntMap R c I J φ) (n : ℤ) := by
  apply (cancel_mono (liftedSectionHomologyIso R c N J n).hom).1
  dsimp only [sectionComputationIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.comp_map]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [liftedSectionHomologyIso_naturality, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, ← Functor.map_comp,
    sectionCohomologyResolutionIso_naturality R U M N f I J φ hφ]

/-- The total cohomology is the original H01 derived-sections abutment. -/
def resolutionAbutmentIso (M : Modules R) (I : InjectiveResolution M) (n : ℕ) :
    (sumTotal (resolutionDoubleComplexInt R c M I)).homology (n : ℤ) ≅
      (liftedSectionCohomology R c n).obj M :=
  (asIso (HomologicalComplex.homologyMap (resolutionTotalAugmentation R c M I)
    (n : ℤ))).symm ≪≫ (sectionComputationIso R c M I n).symm

lemma resolutionAbutmentIso_naturality {M N : Modules R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (resolutionDoubleComplexIntMap R c I J φ) (.up ℤ)) (n : ℤ) ≫
        (resolutionAbutmentIso R c N J n).hom =
    (resolutionAbutmentIso R c M I n).hom ≫ (liftedSectionCohomology R c n).map f := by
  have ha := congrArg (fun g => HomologicalComplex.homologyMap g (n : ℤ))
    (resolutionTotalAugmentation_naturality R c I J φ)
  simp only [HomologicalComplex.homologyMap_comp] at ha
  have hs := sectionComputationIso_naturality R c M N f I J φ hφ n
  have ha' : HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (resolutionDoubleComplexIntMap R c I J φ) (.up ℤ)) (n : ℤ) ≫
        (asIso (HomologicalComplex.homologyMap (resolutionTotalAugmentation R c N J)
          (n : ℤ))).inv =
      (asIso (HomologicalComplex.homologyMap (resolutionTotalAugmentation R c M I)
        (n : ℤ))).inv ≫
      HomologicalComplex.homologyMap (sectionComplexIntMap R c I J φ) (n : ℤ) := by
    apply (cancel_epi (HomologicalComplex.homologyMap (resolutionTotalAugmentation R c M I)
      (n : ℤ))).1
    rw [← Category.assoc, ← ha]
    simp only [Category.assoc, asIso_inv, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  have hs' : HomologicalComplex.homologyMap (sectionComplexIntMap R c I J φ) (n : ℤ) ≫
      (sectionComputationIso R c N J n).inv =
    (sectionComputationIso R c M I n).inv ≫ (liftedSectionCohomology R c n).map f := by
    apply (cancel_epi (sectionComputationIso R c M I n).hom).1
    rw [← Category.assoc, ← hs]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  dsimp only [resolutionAbutmentIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ha', Category.assoc, hs']
  simp only [Category.assoc]

lemma resolutionAbutmentIso_agrees (M : Modules R) (I : InjectiveResolution M) (n : ℕ) :
    HomologicalComplex.homologyMap (resolutionTotalAugmentation R c M I) (n : ℤ) ≫
        (resolutionAbutmentIso R c M I n).hom =
      (liftedSectionHomologyIso R c M I n).hom ≫
        (sectionLift R c).map (sectionCohomologyResolutionIso R U M I n).inv := by
  simp only [resolutionAbutmentIso, sectionComputationIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, asIso_inv, IsIso.hom_inv_id_assoc]

end CechAbutment

section GradedAbutmentMaps
open FiniteFiltrationConvergence
variable {A : Type*} [Category* A] [Abelian A]
variable {X Y : FilteredComplex A} (f : FilteredMap X Y) {H J : A} (n : ℤ)
  (e : X.complex.homology n ≅ H) (e' : Y.complex.homology n ≅ J)

@[reassoc]
lemma abutmentGradedIso_naturality (p : ℤ) :
    abutmentGradedMap f n e e' p ≫ (abutmentGradedIso Y.filtration n e' p).hom =
      (abutmentGradedIso X.filtration n e p).hom ≫ gradedCohomologyMap f p n := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE _ _
    (abutmentPiece_decreasing X.filtration n e p)))).1
  simp [abutmentGradedMap, abutmentGradedIso, gradedCohomologyMap, abutmentPieceMap,
    Category.assoc]
end GradedAbutmentMaps

section ColumnLimitNaturality
open DoubleTotalization FiniteDiagonalFiltrations FiniteFiltrationConvergence
variable {A : Type*} [Category* A] [Abelian A]
variable {K L : Bicomplex A} [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)]

/-- Stabilized column pages map to the associated graded of the
transported abutment filtration naturally. -/
@[reassoc]
lemma columnAbutmentLimitIso_naturality (D : ColumnSpectralData K) (E : ColumnSpectralData L)
    (f : K ⟶ L) {H J : A} (n : ℤ)
    (e : (sumTotal K).homology n ≅ H) (e' : (sumTotal L).homology n ≅ J)
    (r p : ℤ) (hs : Stabilized D.filtration r p n) (ht : Stabilized E.filtration r p n) :
    (columnPageMapData D E f).map r p n ≫ (columnAbutmentLimitIso E n e' r p ht).hom =
      (columnAbutmentLimitIso D n e r p hs).hom ≫
        abutmentGradedMap (columnFilteredMap D E f) n e e' p := by
  apply (cancel_mono (abutmentGradedIso E.filtration n e' p).hom).1
  dsimp only [columnAbutmentLimitIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [abutmentGradedIso_naturality (columnFilteredMap D E f) n e e' p,
    Iso.inv_hom_id_assoc]
  exact limitIso_naturality (columnFilteredMap D E f) D.pages E.pages
    (columnPageMapData D E f) r p n (limitIso D.filtration D.pages r p n hs)
    (limitIso E.filtration E.pages r p n ht) hs
end ColumnLimitNaturality


section ResolutionSecondNaturality

variable {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {A : Type v} (c : Cover U A)

@[reassoc] lemma resolutionSecondPageIso_naturality
    {M N : Modules R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (p q : ℕ) :
    (resolutionPageMapData R c I J φ).map 2 (p : ℤ) ((p : ℤ) + (q : ℤ)) ≫
      (resolutionSecondPageIso R c N J p q).hom =
    (resolutionSecondPageIso R c M I p q).hom ≫ (localCechCohomology R c p q).map f := by
  dsimp only [resolutionPageMapData, resolutionSecondPageIso, Iso.trans_hom]
  rw [columnSecondPageIso_naturality_assoc, resolutionSecondIntIso_naturality, Category.assoc]
  exact hφ

end ResolutionSecondNaturality

section AbutmentFiltrationNaturality

variable {X : TopCat.{u}} {R : RingSheaf X} {U : Opens X} {A : Type v} {c : Cover U A}
variable {S : CechSpectralSequence R c} (N : CechSpectralNaturality R c S)

@[reassoc]
lemma CechSpectralNaturality.abutmentFiltrationMap_arrow {M P : Modules R} (f : M ⟶ P)
    (I : InjectiveResolution M) (J : InjectiveResolution P) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) (p : ℤ) :
    N.abutmentFiltrationMap I J φ n p ≫ (S.abutmentFiltration P J n p).arrow =
      (S.abutmentFiltration M I n p).arrow ≫ (liftedSectionCohomology R c n).map f := by
  apply abutmentPieceMap_arrow
  rw [N.filteredMap_hom]
  exact N.abutment_natural f I J φ hφ n

theorem abutment_filtration_naturality :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.abutmentFiltrationNaturality := by
  intro X R U A c S N
  refine ⟨N.abutmentFiltrationMap_arrow, ?_, ?_, ?_, ?_⟩
  · intro M P I J φ n p
    exact abutmentPieceMap_comm (N.filteredMap I J φ) (n : ℤ)
      (S.abutment M I n) (S.abutment P J n) p
  · intro M P f I J φ ψ hφ hψ n p
    apply (cancel_mono (S.abutmentFiltration P J n p).arrow).1
    rw [N.abutmentFiltrationMap_arrow f I J φ hφ, N.abutmentFiltrationMap_arrow f I J ψ hψ]
  · intro M I n p
    apply (cancel_mono (S.abutmentFiltration M I n p).arrow).1
    rw [N.abutmentFiltrationMap_arrow (𝟙 M) I I (𝟙 I.cocomplex) (by simp)]
    simp
  · intro M P Q f g I J K φ ψ hφ hψ n p
    have hcomp : I.ι.f 0 ≫ (φ ≫ ψ).f 0 = (f ≫ g) ≫ K.ι.f 0 := by
      rw [HomologicalComplex.comp_f, ← Category.assoc, hφ, Category.assoc, hψ, ← Category.assoc]
    apply (cancel_mono (S.abutmentFiltration Q K n p).arrow).1
    rw [N.abutmentFiltrationMap_arrow (f ≫ g) I K (φ ≫ ψ) hcomp, Category.assoc,
      N.abutmentFiltrationMap_arrow g J K ψ hψ,
      N.abutmentFiltrationMap_arrow_assoc f I J φ hφ, Functor.map_comp]
    rfl

end AbutmentFiltrationNaturality

section ResolutionComparison

variable {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {A : Type v} (c : Cover U A)
variable {S : CechSpectralSequence R c} (D : CechSpectralNaturality R c S)

/-- The page maps assigned to coefficient morphisms by resolution descent. -/
def coefficientPageMap {M N : Modules R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (r p n : ℤ) :=
  (D.pageMap I J (InjectiveResolution.desc f J I)).map r p n

lemma coefficientPageMap_eq {M N : Modules R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    coefficientPageMap R c D f I J r p n = (D.pageMap I J φ).map r p n :=
  D.lift_independent f I J _ φ (InjectiveResolution.desc_commutes_zero f J I) hφ r hr p n

lemma coefficientPageMap_id (M : Modules R) (I : InjectiveResolution M)
    (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    coefficientPageMap R c D (𝟙 M) I I r p n = 𝟙 _ :=
  (coefficientPageMap_eq R c D (𝟙 M) I I (𝟙 _) (by simp) r hr p n).trans
    (D.identity M I r p n (by omega))

lemma coefficientPageMap_comp {M N P : Modules R} (f : M ⟶ N) (g : N ⟶ P)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (K : InjectiveResolution P)
    (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    coefficientPageMap R c D (f ≫ g) I K r p n =
      coefficientPageMap R c D f I J r p n ≫ coefficientPageMap R c D g J K r p n := by
  refine (coefficientPageMap_eq R c D (f ≫ g) I K
    (InjectiveResolution.desc f J I ≫ InjectiveResolution.desc g K J) ?_ r hr p n).trans
    (D.composition I J K _ _ r p n (by omega))
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [InjectiveResolution.desc_commutes_zero_assoc, Category.assoc, InjectiveResolution.desc_commutes_zero]

/-- The canonical resolution comparison on and after the first page. -/
def coefficientPageIso (M : Modules R) (I J : InjectiveResolution M)
    (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    PageCohomology.object (S.data M I).filtration (S.data M I).pages r p n ≅
      PageCohomology.object (S.data M J).filtration (S.data M J).pages r p n where
  hom := coefficientPageMap R c D (𝟙 M) I J r p n
  inv := coefficientPageMap R c D (𝟙 M) J I r p n
  hom_inv_id := by
    rw [← coefficientPageMap_comp R c D _ _ I J I r hr p n, Category.id_comp]
    exact coefficientPageMap_id R c D M I r hr p n
  inv_hom_id := by
    rw [← coefficientPageMap_comp R c D _ _ J I J r hr p n, Category.id_comp]
    exact coefficientPageMap_id R c D M J r hr p n

def cechResolutionComparison : CechResolutionComparison R c S D where
  pageIso := coefficientPageIso R c D
  pageIso_hom M I J φ hφ r hr p n :=
    coefficientPageMap_eq R c D (𝟙 M) I J φ (by simpa using hφ) r hr p n
  pageIso_natural f I I' J J' φ ψ hφ hψ r hr p n := by
    change _ ≫ coefficientPageMap R c D (𝟙 _) J J' r p n =
      coefficientPageMap R c D (𝟙 _) I I' r p n ≫ _
    rw [← coefficientPageMap_eq R c D f I J φ hφ r hr p n,
      ← coefficientPageMap_eq R c D f I' J' ψ hψ r hr p n,
      ← coefficientPageMap_comp R c D f _ I J J' r hr p n,
      ← coefficientPageMap_comp R c D _ f I I' J' r hr p n,
      Category.comp_id, Category.id_comp]
  filtration_eq M I J n p := by
    have leOfLift (I₁ I₂ : InjectiveResolution M) :
        abutmentPiece (S.data M I₁).filtration (n : ℤ) (S.abutment M I₁ n) p ≤
          abutmentPiece (S.data M I₂).filtration (n : ℤ) (S.abutment M I₂ n) p := by
      let φ := InjectiveResolution.desc (𝟙 M) I₂ I₁
      refine Subobject.le_of_comm (D.abutmentFiltrationMap I₁ I₂ φ n p) ?_
      simpa using D.abutmentFiltrationMap_arrow (𝟙 M) I₁ I₂ φ
        (InjectiveResolution.desc_commutes_zero (𝟙 M) I₂ I₁) n p
    exact le_antisymm (leOfLift I J) (leOfLift J I)

end ResolutionComparison


section LocalEvaluationComparison

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]

lemma natRightDerivedIso_computation (F : A ⥤ B) [F.Additive] (M : A)
    (I : InjectiveResolution M) (q : ℕ) :
    (natRightDerivedIso F q).hom.app M ≫ (I.isoRightDerivedObj F q).hom =
      (natComputationIso F M I q).hom := by
  let J := injectiveResolution M
  let φ := InjectiveResolution.desc (𝟙 M) I J
  have hφ : J.ι.f 0 ≫ φ.f 0 = 𝟙 M ≫ I.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero _ _ _
  let t := HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) q
  have h₁ : (natComputationIso F M I q).hom = (natComputationIso F M J q).hom ≫ t := by
    have h := natComputationIso_naturality F M M (𝟙 M) J I φ hφ q
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
  have h₂ : (I.isoRightDerivedObj F q).hom = (J.isoRightDerivedObj F q).hom ≫ t := by
    have h := J.isoRightDerivedObj_hom_naturality (𝟙 M) I φ hφ F q
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
  change ((natComputationIso F M J q).hom ≫ (J.isoRightDerivedObj F q).inv) ≫
    (I.isoRightDerivedObj F q).hom = (natComputationIso F M I q).hom
  erw [h₂]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact h₁.symm

end LocalEvaluationComparison

section LocalSectionComparison

variable {X : TopCat.{u}} (R : RingSheaf X)

lemma localSectionsIso_computation (V : Opens X) (M : Modules R)
    (I : InjectiveResolution M) (q : ℕ) :
    (localSectionsIso R V q).hom.app M ≫
      (I.isoRightDerivedObj (SheafOfModules.evaluation R (op V)) q).hom =
      (localEvaluationIso R M I V q).hom := by
  let J := injectiveResolution M
  let φ := InjectiveResolution.desc (𝟙 M) I J
  have hφ : J.ι.f 0 ≫ φ.f 0 = 𝟙 M ≫ I.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero _ _ _
  let F := SheafOfModules.evaluation R (op V)
  let t := HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) q
  have h₁ : (localEvaluationIso R M I V q).hom = (localEvaluationIso R M J V q).hom ≫ t := by
    have h := localEvaluationIso_naturality R V M M (𝟙 M) J I φ hφ q
    erw [CategoryTheory.Functor.map_id, PresheafOfModules.id_app, Category.id_comp] at h
    exact h
  have h₂ : (I.isoRightDerivedObj F q).hom = (J.isoRightDerivedObj F q).hom ≫ t := by
    have h := J.isoRightDerivedObj_hom_naturality (𝟙 M) I φ hφ F q
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
  change ((localEvaluationIso R M J V q).hom ≫
    (J.isoRightDerivedObj F q).inv) ≫ (I.isoRightDerivedObj F q).hom =
      (localEvaluationIso R M I V q).hom
  erw [h₂]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact h₁.symm

lemma localH01SectionsIso_computation (V : Opens X) (M : Modules R)
    (I : InjectiveResolution M) (q : ℕ) :
    (localH01SectionsIso R V q).hom.app M ≫ (sectionCohomologyResolutionIso R V M I q).hom =
      (localEvaluationIso R M I V q).hom := by
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R V))
  let F := SheafOfModules.evaluation R (op V)
  change ((localSectionsIso R V q).hom.app M ≫ (natRightDerivedIso F q).inv.app M) ≫
    (natComputationIso F M I q).hom = (localEvaluationIso R M I V q).hom
  rw [← natRightDerivedIso_computation F M I q,
    Category.assoc, ← Category.assoc ((natRightDerivedIso F q).inv.app M),
    Iso.inv_hom_id_app, Category.id_comp]
  exact localSectionsIso_computation R V M I q

end LocalSectionComparison

section LocalCohomologyRestrictions

variable {X : TopCat.{u}} (R : RingSheaf X)

lemma complexCohomologyRestriction_compare {W V : Opens X} (j : op W ⟶ op V)
    (K : CochainComplex (PresheafOfModules.{u} R.obj) ℕ) (q : ℕ) :
    ((K.sc q).mapHomologyIso (PresheafOfModules.evaluation R.obj (op W))).inv ≫
      complexCohomologyRestriction R j K q =
    (K.homology q).map j ≫ (restrictionScalars R j).map
      ((K.sc q).mapHomologyIso (PresheafOfModules.evaluation R.obj (op V))).inv := by
  let τ := PresheafOfModules.restriction R.obj j
  let k := (restrictionScalars R j).map
    ((K.sc q).mapHomologyIso (PresheafOfModules.evaluation R.obj (op V))).inv
  have h := congrArg (fun t => t ≫ k) (τ.app_homology (K.sc q))
  simp only [Category.assoc] at h
  exact h.symm

lemma localEvaluationIso_restriction {W V : Opens X} (j : op W ⟶ op V)
    (M : Modules R) (I : InjectiveResolution M) (q : ℕ) :
    ((localCohomology R q).obj M).map j ≫
      (restrictionScalars R j).map (localEvaluationIso R M I V q).hom =
    (localEvaluationIso R M I W q).hom ≫ complexCohomologyRestriction R j
      (underlyingComplex R I.cocomplex) q := by
  let e := I.isoRightDerivedObj (SheafOfModules.forget R) q
  have he := PresheafOfModules.Hom.naturality e.hom j
  dsimp only [localEvaluationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have hh := congrArg (fun k ↦ k ≫ (restrictionScalars R j).map
    (((underlyingComplex R I.cocomplex).sc q).mapHomologyIso
      (PresheafOfModules.evaluation R.obj (op V))).inv) he
  simp only [Category.assoc] at hh
  simp only [Category.assoc, Functor.map_comp, complexCohomologyRestriction_compare,
    PresheafOfModules.evaluation_map]
  exact hh

end LocalCohomologyRestrictions

section H01CohomologyRestrictions

variable {X : TopCat.{u}} (R : RingSheaf X)

/-- Evaluation of local cohomology identifies its restriction with the map
induced on cohomology by restricting sections of any injective resolution. -/
lemma localH01SectionsIso_restriction {W V : Opens X} (j : op W ⟶ op V)
    (M : Modules R) (I : InjectiveResolution M) (q : ℕ) :
    ((localCohomology R q).obj M).map j ≫
      (restrictionScalars R j).map ((localH01SectionsIso R V q).hom.app M ≫
        (sectionCohomologyResolutionIso R V M I q).hom) =
    ((localH01SectionsIso R W q).hom.app M ≫
      (sectionCohomologyResolutionIso R W M I q).hom) ≫
        complexCohomologyRestriction R j (underlyingComplex R I.cocomplex) q := by
  have hV : (localH01SectionsIso R V q).hom.app M ≫
      (sectionCohomologyResolutionIso R V M I q).hom =
        (localEvaluationIso R M I V q).hom := localH01SectionsIso_computation R V M I q
  have hW : (localH01SectionsIso R W q).hom.app M ≫
      (sectionCohomologyResolutionIso R W M I q).hom =
        (localEvaluationIso R M I W q).hom := localH01SectionsIso_computation R W M I q
  rw [hV, hW]
  exact localEvaluationIso_restriction R j M I q

end H01CohomologyRestrictions

section SpectralSequence

variable {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {A : Type v} (c : Cover U A)

set_option maxHeartbeats 2000000 in
/-- The first-quadrant Čech-to-cohomology spectral sequence and its abutment,
built simultaneously for all injective resolutions. -/
def cechSpectralSequence : CechSpectralSequence R c where
  resolution := InjectiveResolution.of
  data := resolutionSpectralData R c
  firstQuadrant := resolutionSpectralData_firstQuadrant R c
  vertical := resolutionVerticalComparison R c
  second := resolutionSecondPageIso R c
  second_eq _M _I _p _q := rfl
  abutment := resolutionAbutmentIso R c
  localSections := localH01SectionsIso R
  sectionResolution := sectionCohomologyResolutionIso R
  sectionResolution_eq := sectionCohomologyResolutionIso_eq R
  localSections_eq := localH01SectionsIso_computation R
  totalAugmentation := resolutionTotalAugmentation R c
  totalAugmentation_f := resolutionTotalAugmentation_f R c
  totalAugmentation_quasiIso := resolutionTotalAugmentation_quasiIso R c
  abutment_agrees := resolutionAbutmentIso_agrees R c
  localRestriction := localH01SectionsIso_restriction R
  finite M I n :=
    abutmentPiece_finite _ (n : ℤ) _ (resolutionSpectralData R c M I).converges.target
  limit M I n r p hs :=
    columnAbutmentLimitIso (resolutionSpectralData R c M I) (n : ℤ)
      (resolutionAbutmentIso R c M I n) r p hs
  limit_representative M I n r p hs :=
    columnAbutmentLimitIso_representative (resolutionSpectralData R c M I) (n : ℤ)
      (resolutionAbutmentIso R c M I n) r p hs

set_option maxHeartbeats 2000000 in
/-- Coefficient maps are induced by actual lifts and are independent of the lift
on the abutment and from the first page on. -/
def cechSpectralNaturality : CechSpectralNaturality R c (cechSpectralSequence R c) where
  filteredMap I J φ := columnFilteredMap (resolutionSpectralData R c _ I)
    (resolutionSpectralData R c _ J) (resolutionDoubleComplexIntMap R c I J φ)
  filteredMap_hom {M N} I J φ := columnFilteredMap_hom (resolutionSpectralData R c M I)
    (resolutionSpectralData R c N J) (resolutionDoubleComplexIntMap R c I J φ)
  pageMap := resolutionPageMapData R c
  second_natural := resolutionSecondPageIso_naturality R c
  lift_independent := resolutionPageMapData_lift_independent R c
  identity := resolutionPageMapData_id R c
  composition I J L φ ψ r p n hr := resolutionPageMapData_comp R c I J L φ ψ r p n hr
  abutment_natural := resolutionAbutmentIso_naturality R c
  limit_natural {M N} I J φ n r p hs ht :=
    columnAbutmentLimitIso_naturality (resolutionSpectralData R c M I)
      (resolutionSpectralData R c N J) (resolutionDoubleComplexIntMap R c I J φ)
      (n : ℤ) (resolutionAbutmentIso R c M I n) (resolutionAbutmentIso R c N J n)
      r p hs ht

theorem cech_to_cohomology :
    Specs.AdvancedHomologicalAlgebra.CechToCohomology.fullStatement := by
  intro X R U A c
  let S := cechSpectralSequence R c
  let D := cechSpectralNaturality R c
  exact ⟨S, D, abutment_filtration_naturality R c S D,
    ⟨cechResolutionComparison R c D⟩⟩

end SpectralSequence

end AdvancedHomologicalAlgebra.CechToCohomology
