import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechCochains
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalBicomplex
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomology
import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-! HA-H03, notes/002/advanced-homological-algebra.tex:3650–3684.
The local coefficient is a presheaf of modules, obtained by deriving the
inclusion of sheaves into presheaves. No sheafification occurs here.
The totalization uses the column filtration of the full product cochains. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory AdvancedHomologicalAlgebra.Cech
universe u v w

namespace AdvancedHomologicalAlgebra.CechToCohomology

variable {X : TopCat.{u}} (R : RingSheaf X)

instance sectionEvaluationAdditive (V : Opens X) :
    (SheafOfModules.evaluation R (op V)).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- Right derived inclusion into presheaves, retaining all local section rings. -/
def localCohomology (q : ℕ) : Modules R ⥤ PresheafOfModules.{u} R.obj :=
  (SheafOfModules.forget R).rightDerived q

/-- A presheaf complex evaluated at an open. -/
abbrev evaluateComplex (V : Opens X)
    (K : CochainComplex (PresheafOfModules.{u} R.obj) ℕ) :=
  ((PresheafOfModules.evaluation R.obj (op V)).mapHomologicalComplex (.up ℕ)).obj K

/-- A sheaf complex, with its underlying presheaves. -/
abbrev underlyingComplex (K : CochainComplex (Modules R) ℕ) :=
  ((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).obj K

abbrev restrictionScalars {W V : Opens X} (j : op W ⟶ op V) :=
  ModuleCat.restrictScalars (R.obj.map j).hom

/-- The cohomology map of the degreewise restriction on an evaluated presheaf complex.
The two target comparisons retain the module structure over the larger open. -/
def complexCohomologyRestriction {W V : Opens X} (j : op W ⟶ op V)
    (K : CochainComplex (PresheafOfModules.{u} R.obj) ℕ) (q : ℕ) :
    (evaluateComplex R W K).homology q ⟶
      (restrictionScalars R j).obj ((evaluateComplex R V K).homology q) :=
  let S := K.sc q
  let E := PresheafOfModules.evaluation R.obj (op V)
  let T := restrictionScalars R j
  let τ := PresheafOfModules.restriction R.obj j
  ShortComplex.homologyMap (S.mapNatTrans τ) ≫
    (S.mapHomologyIso (E ⋙ T)).hom ≫ T.map (S.mapHomologyIso E).inv

/-- The actual Čech cochains, functorial in the presheaf coefficient. -/
def cochainMap {U : Opens X} {I : Type v} (c : Cover U I)
    {F G : PresheafOfModules.{u} R.obj} (f : F ⟶ G) (p : ℕ) :
    Cochains R F c p →ₗ[sectionRing R U] Cochains R G c p where
  toFun s t := f.app (op (tupleOpen c t)) (s t)
  map_add' s s' := by funext t; exact map_add _ _ _
  map_smul' r s := by funext t; exact (f.app _).hom.map_smul _ _

variable {U : Opens X} {I : Type v} (c : Cover U I)

/-- Enlarge the carrier of an `R(U)`-module to the cochain universe.
The ring, elements and maps are transported by `ULift.moduleEquiv`. -/
abbrev sectionLift (_ : Cover U I) := ModuleCat.uliftFunctor.{v, u} (sectionRing R U)

/-- Ordinary sheaf cohomology in the universe of the full cochain modules. -/
abbrev liftedSectionCohomology (n : ℕ) := sectionCohomology R U n ⋙ sectionLift R c

/-- The original augmentation, applied after removing the lift on sections. -/
def liftedAugmentation (F : PresheafOfModules.{u} R.obj) :
    (sectionLift R c).obj (F.obj (op U)) ⟶ (ModuleCat.of (sectionRing R U) (Cochains R F c 0)) :=
  ModuleCat.ofHom ((augmentation R F c).comp ULift.moduleEquiv.toLinearMap)

section CochainModel

open scoped Simplicial
open AlgebraicTopology.AlternatingCofaceMapComplex

variable {F : PresheafOfModules.{u} R.obj}

/-- Ordered tuple restrictions give the cosimplicial object whose alternating
coface differential is the prescribed Čech differential. -/
private def cochainCosimplicial (F : PresheafOfModules.{u} R.obj) :
    CosimplicialObject (ModuleCat.{max u v} (sectionRing R U)) where
  obj n := ModuleCat.of (sectionRing R U) (Cochains R F c n.len)
  map f := ModuleCat.ofHom (reindex R F c f.toOrderHom)
  map_id n := by
    apply ModuleCat.hom_ext
    ext s t
    change F.map (𝟙 (op (tupleOpen c t))) (s t) = s t
    exact congr($(F.presheaf.map_id (op (tupleOpen c t))) (s t))
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext s t
    exact F.map_comp_apply _ _ _

/-- The actual cochain object of the full alternating Čech complex. -/
def cechComplex (F : PresheafOfModules.{u} R.obj) :
    CochainComplex (ModuleCat.{max u v} (sectionRing R U)) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (cochainCosimplicial R c F)

lemma cechComplex_d (p : ℕ) :
    (cechComplex R c F).d p (p + 1) = ModuleCat.ofHom (differential R F c p) := by
  calc
    _ = objD (cochainCosimplicial R c F) p :=
      CochainComplex.of_d (fun n ↦ (cochainCosimplicial R c F).obj ⦋n⦌)
        (objD (cochainCosimplicial R c F)) p
    _ = _ := by
      apply ModuleCat.hom_ext
      simp only [objD, differential, ModuleCat.hom_ofHom, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
      rfl

private lemma cechAugmentation_closed (F : PresheafOfModules.{u} R.obj) :
    liftedAugmentation R c F ≫ ModuleCat.ofHom (differential R F c 0) = 0 := by
  apply ModuleCat.hom_ext
  ext s t
  obtain ⟨s⟩ := s
  change differential R F c 0 (augmentation R F c s) t = 0
  have restrict (a : Fin 2) :
      reindex R F c a.succAbove (augmentation R F c s) t =
        F.map (homOfLE (tupleOpen_le c t)).op s := by
    change F.map (homOfLE (tupleOpen_reindex_le c a.succAbove t)).op
      (F.map (homOfLE (tupleOpen_le c (t ∘ a.succAbove))).op s) = _
    rw [← F.map_comp_apply]
    rfl
  change (∑ a : Fin 2, (-1 : ℤ) ^ (a : ℕ) • reindex R F c a.succAbove)
    (augmentation R F c s) t = 0
  rw [Fin.sum_univ_two]
  simp only [LinearMap.add_apply, LinearMap.neg_apply, Pi.add_apply, Pi.neg_apply,
    restrict, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_zsmul, add_neg_cancel]

end CochainModel

lemma cochainMap_reindex {F G : PresheafOfModules.{u} R.obj} (f : F ⟶ G)
    {p q : ℕ} (θ : Fin (p + 1) → Fin (q + 1)) :
    (cochainMap R c f q).comp (reindex R F c θ) =
      (reindex R G c θ).comp (cochainMap R c f p) := by
  ext s t
  exact PresheafOfModules.naturality_apply f _ _

lemma cochainMap_differential {F G : PresheafOfModules.{u} R.obj} (f : F ⟶ G) (p : ℕ) :
    (cochainMap R c f (p + 1)).comp (differential R F c p) =
      (differential R G c p).comp (cochainMap R c f p) := by
  ext s t
  simp only [differential, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, cochainMap,
    LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact PresheafOfModules.naturality_apply f _ _

def cochainComplexMap {F G : PresheafOfModules.{u} R.obj} (f : F ⟶ G) :
    cechComplex R c F ⟶ cechComplex R c G where
  f p := ModuleCat.ofHom (cochainMap R c f p)
  comm' p q hpq := by
    have h : p + 1 = q := hpq
    subst q
    rw [cechComplex_d, cechComplex_d]
    exact ModuleCat.hom_ext (cochainMap_differential R c f p).symm

def cochainFunctor : PresheafOfModules.{u} R.obj ⥤
    CochainComplex (ModuleCat.{max u v} (sectionRing R U)) ℕ where
  obj F := cechComplex R c F
  map f := cochainComplexMap R c f
  map_id F := by ext; rfl
  map_comp f g := by ext; rfl

instance : (cochainFunctor R c).Additive where
  map_add := by intros; ext; rfl

/-- Canonical commuting first-quadrant double complex: outer index p is Čech
degree and inner index q is resolution degree. -/
def resolutionDoubleComplex (M : Modules R) (I : InjectiveResolution M) :
    HomologicalComplex₂ (ModuleCat.{max u v} (sectionRing R U)) (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip
    (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).obj
      (underlyingComplex R I.cocomplex))

/-- The displayed E₂ expression as a genuine functor of the coefficient sheaf. -/
def localCechCohomology (p q : ℕ) : Modules R ⥤ ModuleCat.{max u v} (sectionRing R U) :=
  localCohomology R q ⋙ cochainFunctor R c ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v} (sectionRing R U)) (.up ℕ) p

def augmentationFromSingle (M : Modules R) :
    (CochainComplex.single₀ (ModuleCat.{max u v} (sectionRing R U))).obj ((sectionLift R c).obj (M.val.obj (op U))) ⟶
      cechComplex R c M.val :=
  HomologicalComplex.mkHomFromSingle (j := 0)
    (liftedAugmentation R c M.val) (by
      intro q hq
      have h : 0 + 1 = q := hq
      subst q
      rw [cechComplex_d]
      exact cechAugmentation_closed R c M.val)


/-- The product functor uses genuine functions, without a finite-support condition. -/
def moduleProduct (S : Type u) [Ring S] (J : Type v) :
    (Discrete J ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{max u v} S where
  obj F := ModuleCat.of S (∀ j : J, F.obj ⟨j⟩)
  map f := ModuleCat.ofHom (LinearMap.pi fun j ↦ (f.app ⟨j⟩).hom.comp (LinearMap.proj j))

instance moduleProduct_additive (S : Type u) [Ring S] (J : Type v) :
    (moduleProduct S J).Additive where
  map_add := by intros; ext; rfl

open DoubleTotalization FiniteDiagonalFiltrations

section SpectralData
variable {A : Type w} [Category.{v} A] [Abelian A]

noncomputable def natToIntDoubleComplex
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) : Bicomplex A :=
  ((((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapHomologicalComplex (.up ℕ)).obj K).extend
    (ComplexShape.embeddingUpIntGE 0)

noncomputable def natToIntDoubleComplexMap
    {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)} (f : K ⟶ L) :
    natToIntDoubleComplex K ⟶ natToIntDoubleComplex L :=
  HomologicalComplex.extendMap
    ((((ComplexShape.embeddingUpIntGE 0).extendFunctor A).mapHomologicalComplex (.up ℕ)).map f)
    (ComplexShape.embeddingUpIntGE 0)

/-- The actual column filtration, canonical quotient pages and finite convergence. -/
structure ColumnSpectralData (K : Bicomplex A) [K.HasTotal (.up ℤ)] where
  filtration : Filtration (sumTotal K)
  formula : HasFiltrationFormula K Prod.fst filtration
  pages : F03Specs.PageData filtration
  sequence : PageCohomology.Data filtration pages
  firstPages : DoubleComplexFirstPages.ColumnData K filtration formula pages
  converges : DoubleComplexConvergence.Converges filtration

variable {T : CochainComplex A ℤ} (F : Filtration T) {H : A} (n : ℤ)
    (e : T.homology n ≅ H)
open FiniteFiltrationConvergence
/-- The actual image filtration transported to an identified abutment. -/
def abutmentPiece (p : ℤ) : Subobject H :=
  Subobject.mk ((cohomologyPiece F p n).arrow ≫ e.hom)
lemma abutmentPiece_decreasing (p : ℤ) :
    abutmentPiece F n e (p+1) ≤ abutmentPiece F n e p :=
  Subobject.mk_le_mk_of_comm (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))
    (by simp only [Subobject.ofLE_arrow_assoc])

section AbutmentMaps
variable {X Y : FilteredComplex A} (f : FilteredMap X Y) {H J : A} (n : ℤ)
    (e : X.complex.homology n ≅ H) (e' : Y.complex.homology n ≅ J)

def abutmentPieceMap (p : ℤ) :
    (abutmentPiece X.filtration n e p : A) ⟶ (abutmentPiece Y.filtration n e' p : A) :=
  (Subobject.underlyingIso ((cohomologyPiece X.filtration p n).arrow ≫ e.hom)).hom ≫
    cohomologyStepMap f p n ≫
      (Subobject.underlyingIso ((cohomologyPiece Y.filtration p n).arrow ≫ e'.hom)).inv

lemma abutmentPieceMap_arrow (p : ℤ) (h : H ⟶ J)
    (hh : HomologicalComplex.homologyMap f.hom n ≫ e'.hom = e.hom ≫ h) :
    abutmentPieceMap f n e e' p ≫ (abutmentPiece Y.filtration n e' p).arrow =
      (abutmentPiece X.filtration n e p).arrow ≫ h := by
  dsimp only [abutmentPieceMap, abutmentPiece]
  simp only [Category.assoc, Subobject.underlyingIso_arrow,
    cohomologyStepMap_arrow_assoc, hh]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ h)
    (Subobject.underlyingIso_hom_comp_eq_mk
      ((cohomologyPiece X.filtration p n).arrow ≫ e.hom))

lemma abutmentPieceMap_comm (p : ℤ) :
    Subobject.ofLE _ _ (abutmentPiece_decreasing X.filtration n e p) ≫
      abutmentPieceMap f n e e' p =
    abutmentPieceMap f n e e' (p+1) ≫
      Subobject.ofLE _ _ (abutmentPiece_decreasing Y.filtration n e' p) := by
  apply (cancel_mono (abutmentPiece Y.filtration n e' p).arrow).1
  have hh : HomologicalComplex.homologyMap f.hom n ≫ e'.hom = e.hom ≫
      (e.inv ≫ HomologicalComplex.homologyMap f.hom n ≫ e'.hom) := by simp
  simp only [Category.assoc, Subobject.ofLE_arrow_assoc, Subobject.ofLE_arrow,
    abutmentPieceMap_arrow f n e e' p _ hh,
    abutmentPieceMap_arrow f n e e' (p+1) _ hh,
    Subobject.ofLE_arrow_assoc]

/-- The quotient of two adjacent terms of the transported cohomology filtration. -/
def abutmentGradedMap (p : ℤ) :
    cokernel (Subobject.ofLE _ _ (abutmentPiece_decreasing X.filtration n e p)) ⟶
      cokernel (Subobject.ofLE _ _ (abutmentPiece_decreasing Y.filtration n e' p)) :=
  cokernel.map _ _ (abutmentPieceMap f n e e' (p+1)) (abutmentPieceMap f n e e' p)
    (abutmentPieceMap_comm f n e e' p)

end AbutmentMaps

end SpectralData

/-- Integer-indexed extension of the actual commuting Čech-resolution double complex. -/
def resolutionDoubleComplexInt {U : Opens X} {A : Type v} (c : Cover U A)
    (M : Modules R) (I : InjectiveResolution M) :
    Bicomplex (ModuleCat.{max u v} (sectionRing R U)) :=
  natToIntDoubleComplex (resolutionDoubleComplex R c M I)

/-- The actual integer column in each nonnegative Čech degree. -/
abbrev resolutionColumnIso (M : Modules R) (I : InjectiveResolution M) (p : ℕ) :
    (resolutionDoubleComplexInt R c M I).X (p : ℤ) ≅
      ((resolutionDoubleComplex R c M I).X p).extend (ComplexShape.embeddingUpIntGE 0) :=
  let extendColumns := ((ComplexShape.embeddingUpIntGE 0).extendFunctor
    (ModuleCat.{max u v} (sectionRing R U))).mapHomologicalComplex (.up ℕ)
  (extendColumns.obj (resolutionDoubleComplex R c M I)).extendXIso
    (ComplexShape.embeddingUpIntGE 0) (by simp)

abbrev cechTerm (p : ℕ) := cochainFunctor R c ⋙
  HomologicalComplex.eval (ModuleCat.{max u v} (sectionRing R U)) (.up ℕ) p

/-- Each component is the canonical exact-product comparison, followed by
the local cohomology comparison of the given injective resolution. -/
def resolutionVerticalComponent (M : Modules R) (I : InjectiveResolution M) (p q : ℕ)
    [(cechTerm R c p).PreservesHomology] :
    ((resolutionDoubleComplexInt R c M I).X (p : ℤ)).homology (q : ℤ) ≅
      (cechComplex R c ((localCohomology R q).obj M)).X p :=
  HomologicalComplex.homologyMapIso (resolutionColumnIso R c M I p) (q : ℤ) ≪≫
    ((resolutionDoubleComplex R c M I).X p).extendHomologyIso
      (ComplexShape.embeddingUpIntGE 0) (j := q) (j' := (q : ℤ)) (by simp) ≪≫
    ((underlyingComplex R I.cocomplex).sc q).mapHomologyIso (cechTerm R c p) ≪≫
    (cechTerm R c p).mapIso (I.isoRightDerivedObj (SheafOfModules.forget R) q).symm

/-- The complete alternating restriction complex in integer degrees. -/
abbrev localCechComplexInt (M : Modules R) (q : ℕ) :=
  (cechComplex R c ((localCohomology R q).obj M)).extend (ComplexShape.embeddingUpIntGE 0)

/-- A horizontal chain comparison whose components are the canonical maps. -/
structure ResolutionVerticalComparison (M : Modules R) (I : InjectiveResolution M) where
  exactTerm : ∀ p, (cechTerm R c p).PreservesHomology
  iso : ∀ q : ℕ, DoubleComplexFirstPages.verticalHomology (resolutionDoubleComplexInt R c M I) (q : ℤ) ≅
    localCechComplexInt R c M q
  component : ∀ p q : ℕ,
    letI := exactTerm p
    (iso q).hom.f (p : ℤ) ≫
      ((cechComplex R c ((localCohomology R q).obj M)).extendXIso
        (ComplexShape.embeddingUpIntGE 0) (i := p) (i' := (p : ℤ)) (by simp)).hom =
      (resolutionVerticalComponent R c M I p q).hom

/-- A lift of a coefficient map acts on the actual Čech-resolution bicomplex. -/
def resolutionDoubleComplexMap {U : Opens X} {A : Type v} (c : Cover U A)
    {M N : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex) :
    resolutionDoubleComplex R c M I ⟶ resolutionDoubleComplex R c N J :=
  (HomologicalComplex₂.flipFunctor (ModuleCat.{max u v} (sectionRing R U)) (.up ℕ) (.up ℕ)).map
    (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).map
      (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ))

def resolutionDoubleComplexIntMap {U : Opens X} {A : Type v} (c : Cover U A)
    {M N : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex) :
    resolutionDoubleComplexInt R c M I ⟶ resolutionDoubleComplexInt R c N J :=
  natToIntDoubleComplexMap (resolutionDoubleComplexMap R c I J φ)

abbrev sectionComplex (M : Modules R) (I : InjectiveResolution M) :=
  ((SheafOfModules.evaluation R (op U)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex

abbrev liftedSectionComplex (M : Modules R) (I : InjectiveResolution M) :=
  ((sectionLift R c).mapHomologicalComplex (.up ℕ)).obj (sectionComplex R (U := U) M I)

abbrev sectionComplexInt (M : Modules R) (I : InjectiveResolution M) :=
  (liftedSectionComplex R c M I).extend (ComplexShape.embeddingUpIntGE 0)

/-- Homology commutes with the carrier lift and the zero extension to integer degrees. -/
def liftedSectionHomologyIso (M : Modules R) (I : InjectiveResolution M) (n : ℕ) :
    (sectionComplexInt R c M I).homology (n : ℤ) ≅
      (sectionLift R c).obj ((sectionComplex R (U := U) M I).homology n) :=
  (liftedSectionComplex R c M I).extendHomologyIso (ComplexShape.embeddingUpIntGE 0)
    (j := n) (j' := (n : ℤ)) (by simp) ≪≫
      ((sectionComplex R (U := U) M I).sc n).mapHomologyIso (sectionLift R c)

private def evaluationExtendComponent (V : Opens X) (K : CochainComplex (Modules R) ℕ)
    (o : Option ℕ) :
    (SheafOfModules.evaluation R (op V)).obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X
        (((SheafOfModules.evaluation R (op V)).mapHomologicalComplex (.up ℕ)).obj K) o :=
  match o with
  | some _ => Iso.refl _
  | none => (SheafOfModules.evaluation R (op V)).mapZeroObject

private def evaluationExtendIso (V : Opens X) (K : CochainComplex (Modules R) ℕ) :
    ((SheafOfModules.evaluation R (op V)).mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat) ≅
      (((SheafOfModules.evaluation R (op V)).mapHomologicalComplex (.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => evaluationExtendComponent R V K (ComplexShape.embeddingUpNat.r n)) (by
      intro i j h
      let F := SheafOfModules.evaluation R (op V)
      let e := ComplexShape.embeddingUpNat
      change (evaluationExtendComponent R V K (e.r i)).hom ≫
          HomologicalComplex.extend.d ((F.mapHomologicalComplex (.up ℕ)).obj K) (e.r i) (e.r j) =
        F.map (HomologicalComplex.extend.d K (e.r i) (e.r j)) ≫
          (evaluationExtendComponent R V K (e.r j)).hom
      cases e.r i <;> cases e.r j <;>
        simp [evaluationExtendComponent, HomologicalComplex.extend.d, F])

/-- The canonical HA-H01 computation, using the derived unit and the
augmentation of this injective resolution. -/
def sectionResolutionIsoNat (V : Opens X) (M : Modules R) (I : InjectiveResolution M) (n : ℕ) :
    (sectionCohomology R V n).obj M ≅ (sectionComplex R (U := V) M I).homology n := by
  let B := ModuleCat.{u} (sectionRing R V)
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard B
  let F := SheafOfModules.evaluation R (op V)
  let P : CochainComplex.Plus (Modules R) := ⟨I.cochainComplex, 0, inferInstance⟩
  let L : CochainComplex.Plus (Modules R) :=
    ⟨(CochainComplex.singleFunctor (Modules R) 0).obj M, 0, inferInstance⟩
  let i : L ⟶ P := (CochainComplex.plus _).homMk I.ι'
  letI : IsIso (DerivedCategory.Plus.Q.map i) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (Modules R)) i
      (inferInstanceAs (QuasiIso I.ι'))
  letI : IsIso (F.rightDerivedFunctorPlusUnit.app P) := by
    have h : ∀ q : ℤ, Injective (P.obj.X q) := fun q =>
      inferInstanceAs (Injective (I.cochainComplex.X q))
    rw [Functor.rightDerivedFunctorPlusUnit_app]
    infer_instance
  let H := HomologicalComplex.homologyFunctor B (.up ℤ) (n : ℤ)
  let K := sectionComplex R (U := V) M I
  exact ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).mapIso
      (F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map i)) ≪≫
        (asIso (F.rightDerivedFunctorPlusUnit.app P)).symm) ≪≫
      (DerivedCategory.homologyFunctorFactors B (n : ℤ)).app _) ≪≫
      H.mapIso (evaluationExtendIso R V I.cocomplex) ≪≫
      K.extendHomologyIso ComplexShape.embeddingUpNat rfl

lemma augmentation_cochainMap {M N : Modules R} (f : M ⟶ N) :
    liftedAugmentation R c M.val ≫
      ModuleCat.ofHom (cochainMap R c f.val 0) =
    (sectionLift R c).map (f.val.app (op U)) ≫ liftedAugmentation R c N.val := by
  ext s t
  exact PresheafOfModules.naturality_apply f.val _ _

/-- The row augmentation in all resolution degrees, before extension. -/
def resolutionAugmentationNat (M : Modules R) (I : InjectiveResolution M) :
    liftedSectionComplex R c M I ⟶ (resolutionDoubleComplex R c M I).X 0 where
  f q := liftedAugmentation R c (I.cocomplex.X q).val
  comm' q q' _ := augmentation_cochainMap R c (I.cocomplex.d q q')

/-- The outer degree-zero identification retains the whole resolution complex. -/
def resolutionZeroColumnIso (M : Modules R) (I : InjectiveResolution M) :
    (resolutionDoubleComplexInt R c M I).X 0 ≅
      ((resolutionDoubleComplex R c M I).X 0).extend (ComplexShape.embeddingUpIntGE 0) :=
  ((((ComplexShape.embeddingUpIntGE 0).extendFunctor _).mapHomologicalComplex (.up ℕ)).obj
    (resolutionDoubleComplex R c M I)).extendXIso (ComplexShape.embeddingUpIntGE 0) (by simp)

/-- The actual resolution-sections augmentation into column zero. -/
def resolutionAugmentation (M : Modules R) (I : InjectiveResolution M) :
    sectionComplexInt R c M I ⟶ (resolutionDoubleComplexInt R c M I).X 0 :=
  HomologicalComplex.extendMap (resolutionAugmentationNat R c M I)
    (ComplexShape.embeddingUpIntGE 0) ≫ (resolutionZeroColumnIso R c M I).inv


section SectionMaps
variable {M N : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution N)
variable (φ : I.cocomplex ⟶ J.cocomplex)
abbrev sectionComplexMap := ((SheafOfModules.evaluation R (op U)).mapHomologicalComplex (.up ℕ)).map φ
abbrev sectionComplexIntMap := HomologicalComplex.extendMap
  (((sectionLift R c).mapHomologicalComplex (.up ℕ)).map (sectionComplexMap R (U := U) I J φ))
  (ComplexShape.embeddingUpIntGE 0)
end SectionMaps

/-- A realization of the Čech-to-cohomology spectral sequence for every ordinary
injective resolution, with its specified pages and abutment. -/
structure CechSpectralSequence where
  resolution : ∀ M : Modules R, InjectiveResolution M
  data : ∀ (M : Modules R) (I : InjectiveResolution M),
    ColumnSpectralData (resolutionDoubleComplexInt R c M I)
  firstQuadrant : ∀ (M : Modules R) (I : InjectiveResolution M) (r p q : ℤ),
    p < 0 ∨ q < 0 → IsZero (DoubleComplexFirstPages.page
      (data M I).filtration (data M I).pages r p q)
  vertical : ∀ (M : Modules R) (I : InjectiveResolution M), ResolutionVerticalComparison R c M I
  second : ∀ (M : Modules R) (I : InjectiveResolution M) (p q : ℕ),
    DoubleComplexFirstPages.page (data M I).filtration (data M I).pages
      2 (p : ℤ) (q : ℤ) ≅ (localCechCohomology R c p q).obj M
  second_eq : ∀ (M : Modules R) (I : InjectiveResolution M) (p q : ℕ),
    second M I p q =
      (data M I).firstPages.secondIso (p : ℤ) (q : ℤ) ≪≫
      HomologicalComplex.homologyMapIso ((vertical M I).iso q) (p : ℤ) ≪≫
      (cechComplex R c ((localCohomology R q).obj M)).extendHomologyIso
        (ComplexShape.embeddingUpIntGE 0) (j := p) (j' := (p : ℤ)) (by simp)
  abutment : ∀ (M : Modules R) (I : InjectiveResolution M) (n : ℕ),
    (sumTotal (resolutionDoubleComplexInt R c M I)).homology (n : ℤ) ≅
      (liftedSectionCohomology R c n).obj M
  localSections : ∀ (V : Opens X) (q : ℕ),
    localCohomology R q ⋙ PresheafOfModules.evaluation R.obj (op V) ≅
      sectionCohomology R V q
  sectionResolution : ∀ (V : Opens X) (M : Modules R) (I : InjectiveResolution M) (q : ℕ),
    (sectionCohomology R V q).obj M ≅ (sectionComplex R (U := V) M I).homology q
  sectionResolution_eq : ∀ (V : Opens X) (M : Modules R) (I : InjectiveResolution M) (q : ℕ),
    sectionResolution V M I q = sectionResolutionIsoNat R V M I q
  localSections_eq : ∀ (V : Opens X) (M : Modules R) (I : InjectiveResolution M) (q : ℕ),
    (localSections V q).hom.app M ≫ (sectionResolution V M I q).hom =
      (PresheafOfModules.evaluation R.obj (op V)).map
        (I.isoRightDerivedObj (SheafOfModules.forget R) q).hom ≫
      (((underlyingComplex R I.cocomplex).sc q).mapHomologyIso
        (PresheafOfModules.evaluation R.obj (op V))).inv
  totalAugmentation : ∀ (M : Modules R) (I : InjectiveResolution M),
    sectionComplexInt R c M I ⟶ sumTotal (resolutionDoubleComplexInt R c M I)
  totalAugmentation_f : ∀ (M : Modules R) (I : InjectiveResolution M) (n : ℤ),
    (totalAugmentation M I).f n = (resolutionAugmentation R c M I).f n ≫
      sumInjection (resolutionDoubleComplexInt R c M I) 0 n n (zero_add n)
  totalAugmentation_quasiIso : ∀ (M : Modules R) (I : InjectiveResolution M),
    QuasiIso (totalAugmentation M I)
  abutment_agrees : ∀ (M : Modules R) (I : InjectiveResolution M) (n : ℕ),
    HomologicalComplex.homologyMap (totalAugmentation M I) (n : ℤ) ≫ (abutment M I n).hom =
      (liftedSectionHomologyIso R c M I n).hom ≫
        (sectionLift R c).map (sectionResolution U M I n).inv
  localRestriction : ∀ {W V : Opens X} (j : op W ⟶ op V) (M : Modules R)
    (I : InjectiveResolution M) (q : ℕ),
    ((localCohomology R q).obj M).map j ≫
      (restrictionScalars R j).map ((localSections V q).hom.app M ≫
        (sectionResolution V M I q).hom) =
    ((localSections W q).hom.app M ≫ (sectionResolution W M I q).hom) ≫
      complexCohomologyRestriction R j (underlyingComplex R I.cocomplex) q
  finite : ∀ (M : Modules R) (I : InjectiveResolution M) (n : ℕ),
    ∃ a b : ℤ,
      (∀ p, p ≤ a → abutmentPiece (data M I).filtration (n : ℤ) (abutment M I n) p = ⊤) ∧
      (∀ p, b ≤ p → abutmentPiece (data M I).filtration (n : ℤ) (abutment M I n) p = ⊥)
  limit : ∀ (M : Modules R) (I : InjectiveResolution M) (n : ℕ) (r p : ℤ),
    FiniteFiltrationConvergence.Stabilized (data M I).filtration r p (n : ℤ) →
    (PageCohomology.object (data M I).filtration (data M I).pages r p (n : ℤ) ≅
      cokernel (Subobject.ofLE _ _
        (abutmentPiece_decreasing (data M I).filtration (n : ℤ) (abutment M I n) p)))
  limit_representative : ∀ (M : Modules R) (I : InjectiveResolution M) (n : ℕ) (r p : ℤ)
    (hs : FiniteFiltrationConvergence.Stabilized (data M I).filtration r p (n : ℤ)),
    let F := (data M I).filtration
    FiniteFiltrationConvergence.closedToPage F (data M I).pages r p (n : ℤ) ≫
        (limit M I n r p hs).hom =
      FiniteFiltrationConvergence.closedClass F p (n : ℤ) ≫
        (Subobject.underlyingIso
          ((FiniteFiltrationConvergence.cohomologyPiece F p (n : ℤ)).arrow ≫
            (abutment M I n).hom)).inv ≫
        cokernel.π (Subobject.ofLE _ _
          (abutmentPiece_decreasing F (n : ℤ) (abutment M I n) p))

/-- Naturality is witnessed on the actual filtered totals and quotient pages.
All page maps from the first page on are independent of the resolution lift. -/
structure CechSpectralNaturality (S : CechSpectralSequence R c) where
  filteredMap : ∀ {M N : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution N)
    (_φ : I.cocomplex ⟶ J.cocomplex),
    FilteredMap ⟨sumTotal (resolutionDoubleComplexInt R c M I), (S.data M I).filtration⟩
      ⟨sumTotal (resolutionDoubleComplexInt R c N J), (S.data N J).filtration⟩
  filteredMap_hom : ∀ {M N : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex), (filteredMap I J φ).hom =
      HomologicalComplex₂.total.map (resolutionDoubleComplexIntMap R c I J φ) (.up ℤ)
  pageMap : ∀ {M N : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex),
    FilteredPageFunctoriality.MapData (filteredMap I J φ) (S.data M I).pages (S.data N J).pages
  second_natural : ∀ {M N : Modules R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → ∀ p q : ℕ,
    (pageMap I J φ).map 2 (p : ℤ) ((p : ℤ)+(q : ℤ)) ≫ (S.second N J p q).hom =
      (S.second M I p q).hom ≫ (localCechCohomology R c p q).map f
  lift_independent : ∀ {M N : Modules R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ ψ : I.cocomplex ⟶ J.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0 →
    ∀ r : ℤ, 1 ≤ r → ∀ p n : ℤ, (pageMap I J φ).map r p n = (pageMap I J ψ).map r p n
  identity : ∀ (M : Modules R) (I : InjectiveResolution M) (r p n : ℤ),
    0 ≤ r → (pageMap I I (𝟙 I.cocomplex)).map r p n = 𝟙 _
  composition : ∀ {M N P : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution N)
    (L : InjectiveResolution P) (φ : I.cocomplex ⟶ J.cocomplex)
    (ψ : J.cocomplex ⟶ L.cocomplex) (r p n : ℤ), 0 ≤ r →
    (pageMap I L (φ ≫ ψ)).map r p n = (pageMap I J φ).map r p n ≫ (pageMap J L ψ).map r p n
  abutment_natural : ∀ {M N : Modules R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → ∀ n : ℕ,
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (resolutionDoubleComplexIntMap R c I J φ) (.up ℤ)) (n : ℤ) ≫ (S.abutment N J n).hom =
      (S.abutment M I n).hom ≫ (liftedSectionCohomology R c n).map f


  limit_natural : ∀ {M N : Modules R} (I : InjectiveResolution M)
    (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (r p : ℤ)
    (hs : FiniteFiltrationConvergence.Stabilized (S.data M I).filtration r p (n : ℤ))
    (ht : FiniteFiltrationConvergence.Stabilized (S.data N J).filtration r p (n : ℤ)),
    (pageMap I J φ).map r p (n : ℤ) ≫ (S.limit N J n r p ht).hom =
      (S.limit M I n r p hs).hom ≫
        abutmentGradedMap (filteredMap I J φ) (n : ℤ) (S.abutment M I n)
          (S.abutment N J n) p

section AbutmentFiltrationMaps

variable {R c}

/-- The abutment filtration is the image filtration on total cohomology,
transported along the identification with section cohomology. -/
abbrev CechSpectralSequence.abutmentFiltration (S : CechSpectralSequence R c)
    (M : Modules R) (I : InjectiveResolution M) (n : ℕ) (p : ℤ) :
    Subobject ((liftedSectionCohomology R c n).obj M) :=
  abutmentPiece (S.data M I).filtration (n : ℤ) (S.abutment M I n) p

/-- The map of abutment filtration pieces induced by a resolution map. -/
abbrev CechSpectralNaturality.abutmentFiltrationMap {S : CechSpectralSequence R c}
    (N : CechSpectralNaturality R c S) {M P : Modules R}
    (I : InjectiveResolution M) (J : InjectiveResolution P)
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (p : ℤ) :
    (S.abutmentFiltration M I n p : ModuleCat.{max u v} (sectionRing R U)) ⟶
      (S.abutmentFiltration P J n p : ModuleCat.{max u v} (sectionRing R U)) :=
  abutmentPieceMap (N.filteredMap I J φ) (n : ℤ) (S.abutment M I n) (S.abutment P J n) p

/-- The filtration pieces are natural under coefficient maps via any resolution lift. -/
structure CechAbutmentFiltrationNaturality (S : CechSpectralSequence R c)
    (N : CechSpectralNaturality R c S) : Prop where
  arrow : ∀ {M P : Modules R} (f : M ⟶ P)
    (I : InjectiveResolution M) (J : InjectiveResolution P) (φ : I.cocomplex ⟶ J.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → ∀ (n : ℕ) (p : ℤ),
    N.abutmentFiltrationMap I J φ n p ≫ (S.abutmentFiltration P J n p).arrow =
      (S.abutmentFiltration M I n p).arrow ≫ (liftedSectionCohomology R c n).map f
  transition : ∀ {M P : Modules R} (I : InjectiveResolution M) (J : InjectiveResolution P)
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (p : ℤ),
    Subobject.ofLE _ _
      (abutmentPiece_decreasing (S.data M I).filtration (n : ℤ) (S.abutment M I n) p) ≫
        N.abutmentFiltrationMap I J φ n p =
    N.abutmentFiltrationMap I J φ n (p+1) ≫
      Subobject.ofLE _ _
        (abutmentPiece_decreasing (S.data P J).filtration (n : ℤ) (S.abutment P J n) p)
  lift_independent : ∀ {M P : Modules R} (f : M ⟶ P)
    (I : InjectiveResolution M) (J : InjectiveResolution P) (φ ψ : I.cocomplex ⟶ J.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0 →
      ∀ (n : ℕ) (p : ℤ), N.abutmentFiltrationMap I J φ n p = N.abutmentFiltrationMap I J ψ n p
  identity : ∀ (M : Modules R) (I : InjectiveResolution M) (n : ℕ) (p : ℤ),
    N.abutmentFiltrationMap I I (𝟙 I.cocomplex) n p = 𝟙 _
  composition : ∀ {M P Q : Modules R} (f : M ⟶ P) (g : P ⟶ Q)
    (I : InjectiveResolution M) (J : InjectiveResolution P) (K : InjectiveResolution Q)
    (φ : I.cocomplex ⟶ J.cocomplex) (ψ : J.cocomplex ⟶ K.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → J.ι.f 0 ≫ ψ.f 0 = g ≫ K.ι.f 0 →
    ∀ (n : ℕ) (p : ℤ), N.abutmentFiltrationMap I K (φ ≫ ψ) n p =
      N.abutmentFiltrationMap I J φ n p ≫ N.abutmentFiltrationMap J K ψ n p

end AbutmentFiltrationMaps

/-- Changing the injective resolution gives the comparisons induced by any
lift of the identity. Their naturality compares arbitrary lifts of the same
coefficient morphism. The induced filtration is independent of the model. -/
structure CechResolutionComparison (S : CechSpectralSequence R c)
    (D : CechSpectralNaturality R c S) where
  pageIso : ∀ (M : Modules R) (I J : InjectiveResolution M) (r : ℤ), 1 ≤ r →
    ∀ p n : ℤ, PageCohomology.object (S.data M I).filtration (S.data M I).pages r p n ≅
      PageCohomology.object (S.data M J).filtration (S.data M J).pages r p n
  pageIso_hom : ∀ (M : Modules R) (I J : InjectiveResolution M) (φ : I.cocomplex ⟶ J.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = J.ι.f 0 → ∀ r (hr : 1 ≤ r) p n,
    (pageIso M I J r hr p n).hom = (D.pageMap I J φ).map r p n
  pageIso_natural : ∀ {M N : Modules R} (f : M ⟶ N)
    (I I' : InjectiveResolution M) (J J' : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex) (ψ : I'.cocomplex ⟶ J'.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → I'.ι.f 0 ≫ ψ.f 0 = f ≫ J'.ι.f 0 →
    ∀ r (hr : 1 ≤ r) p n, (D.pageMap I J φ).map r p n ≫ (pageIso N J J' r hr p n).hom =
      (pageIso M I I' r hr p n).hom ≫ (D.pageMap I' J' ψ).map r p n
  filtration_eq : ∀ (M : Modules R) (I J : InjectiveResolution M) (n : ℕ) (p : ℤ),
    abutmentPiece (S.data M I).filtration (n : ℤ) (S.abutment M I n) p =
      abutmentPiece (S.data M J).filtration (n : ℤ) (S.abutment M J n) p

end AdvancedHomologicalAlgebra.CechToCohomology

namespace Specs.AdvancedHomologicalAlgebra.CechToCohomology
open _root_.AdvancedHomologicalAlgebra.CechToCohomology

/-- Exactness of arbitrary products, with no finite-cover hypothesis. -/
def productExactness : Prop := ∀ (S : Type u) [Ring S] (J : Type v),
  (moduleProduct S J).PreservesHomology

/-- Cohomology of the actual unrestricted product is the product of cohomology. -/
def productCohomology : Prop := ∀ (S : Type u) [Ring S] (J : Type v)
  (K : CochainComplex (Discrete J ⥤ ModuleCat.{u} S) ℕ) (q : ℕ),
  Nonempty ((((moduleProduct S J).mapHomologicalComplex (.up ℕ)).obj K).homology q ≅
    ModuleCat.of S (∀ j : J,
      ((((evaluation (Discrete J) (ModuleCat.{u} S)).obj ⟨j⟩).mapHomologicalComplex
        (.up ℕ)).obj K).homology q))

/-- Exactness holds in every horizontal degree, so the cohomology identification
also retains the full horizontal differential. -/
def cechExactness : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {I : Type v} (c : Cover U I), (cochainFunctor R c).PreservesHomology

/-- The vertical cohomology is the Čech complex of the actual local cohomology
presheaf, with its specified alternating restriction differential. -/
def resolutionVertical : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {A : Type v} (c : Cover U A)
  (M : Modules R) (I : InjectiveResolution M) (q : ℕ),
  Nonempty ((((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).obj
    (underlyingComplex R I.cocomplex)).homology q ≅
      cechComplex R c ((localCohomology R q).obj M))

/-- Canonical computation of the local cohomology presheaf by every injective
resolution, not an additional certificate assumed of the sheaf. -/
def localResolution : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  (M : Modules R) (I : InjectiveResolution M) (q : ℕ),
  Nonempty ((localCohomology R q).obj M ≅ (underlyingComplex R I.cocomplex).homology q)

/-- Naturality for every lift between every pair of injective resolutions. -/
def localResolutionNaturality : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  (M N : Modules R) (f : M ⟶ N) (I : InjectiveResolution M)
  (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex),
  I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → ∀ q,
  (localCohomology R q).map f ≫ (J.isoRightDerivedObj (SheafOfModules.forget R) q).hom =
    (I.isoRightDerivedObj (SheafOfModules.forget R) q).hom ≫
      HomologicalComplex.homologyMap
        (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ) q

/-- The canonical augmentation is a quasi-isomorphism for each injective
coefficient sheaf, including degree zero and every positive degree. -/
def injectiveAugmentation : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {A : Type v} (c : Cover U A) (M : Modules R), Injective M →
  QuasiIso (augmentationFromSingle R c M)

/-- Evaluation retains the local section-ring action and agrees naturally
with ordinary right-derived sections. -/
def localSections : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X) (V : Opens X) (q : ℕ),
  Nonempty (localCohomology R q ⋙ PresheafOfModules.evaluation R.obj (op V) ≅
    (SheafOfModules.evaluation R (op V)).rightDerived q)

/-- Simultaneous comparisons of whole horizontal complexes, natural for any
lift and any choices of injective resolutions. -/
def resolutionVerticalNaturality : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {A : Type v} (c : Cover U A),
  ∃ e : ∀ (M : Modules R) (I : InjectiveResolution M) (q : ℕ),
    (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).obj
      (underlyingComplex R I.cocomplex)).homology q ≅
        cechComplex R c ((localCohomology R q).obj M),
  ∀ (M N : Modules R) (f : M ⟶ N) (I : InjectiveResolution M)
    (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → ∀ q,
    HomologicalComplex.homologyMap
      (((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).map
        (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ)) q ≫
          (e N J q).hom =
      (e M I q).hom ≫ (cochainFunctor R c).map ((localCohomology R q).map f)

/-- The iterated cohomology model for the second filtered page. -/
def resolutionSecond : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {A : Type v} (c : Cover U A) (M : Modules R)
  (I : InjectiveResolution M) (p q : ℕ),
  Nonempty (((((cochainFunctor R c).mapHomologicalComplex (.up ℕ)).obj
    (underlyingComplex R I.cocomplex)).homology q).homology p ≅
      (localCechCohomology R c p q).obj M)

/-- The genuine column spectral sequence of the Čech-resolution complex has
first-quadrant support and converges through the finite image filtration. -/
def resolutionSpectralCore : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {A : Type v} (c : Cover U A) (M : Modules R)
  (I : InjectiveResolution M),
  ∃ D : ColumnSpectralData (resolutionDoubleComplexInt R c M I),
    ∀ r p q : ℤ, p < 0 ∨ q < 0 →
      IsZero (_root_.AdvancedHomologicalAlgebra.DoubleComplexFirstPages.page
        D.filtration D.pages r p q)

/-- The genuine second filtered page is Čech cohomology of the actual local
cohomology presheaf, with first-quadrant support and finite convergence. -/
def resolutionSecondPage : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {A : Type v} (c : Cover U A) (M : Modules R)
  (I : InjectiveResolution M),
  ∃ D : ColumnSpectralData (resolutionDoubleComplexInt R c M I),
    (∀ r p q : ℤ, p < 0 ∨ q < 0 →
      IsZero (_root_.AdvancedHomologicalAlgebra.DoubleComplexFirstPages.page
        D.filtration D.pages r p q)) ∧
    ∀ p q : ℕ, Nonempty
      (_root_.AdvancedHomologicalAlgebra.DoubleComplexFirstPages.page D.filtration D.pages
        2 (p : ℤ) (q : ℤ) ≅ (localCechCohomology R c p q).obj M)

/-- The actual horizontal augmentation into the signed sum total is a
quasi-isomorphism, with its prescribed degree-zero-column formula. -/
def totalAugmentation : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    {U : Opens X} {A : Type v} (c : Cover U A) (M : Modules R) (I : InjectiveResolution M),
  ∃ α : sectionComplexInt R c M I ⟶
      _root_.AdvancedHomologicalAlgebra.DoubleTotalization.sumTotal
        (resolutionDoubleComplexInt R c M I), QuasiIso α ∧
    ∀ n, α.f n = (resolutionAugmentation R c M I).f n ≫
      _root_.AdvancedHomologicalAlgebra.DoubleTotalization.sumInjection
        (resolutionDoubleComplexInt R c M I) 0 n n (zero_add n)

/-- The natural maps on total cohomology preserve every abutment filtration piece. -/
def abutmentFiltrationNaturality : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    {U : Opens X} {A : Type v} (c : Cover U A)
    (S : CechSpectralSequence R c) (N : CechSpectralNaturality R c S),
  CechAbutmentFiltrationNaturality S N

/-- HA-H03: the natural first-quadrant Čech-to-cohomology spectral sequence,
with arbitrary indexed covers and the presheaf of local cohomology as coefficient. -/
def fullStatement : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    {U : Opens X} {A : Type v} (c : Cover U A),
  ∃ (S : CechSpectralSequence R c) (N : CechSpectralNaturality R c S),
    CechAbutmentFiltrationNaturality S N ∧ Nonempty (CechResolutionComparison R c S N)

end Specs.AdvancedHomologicalAlgebra.CechToCohomology
