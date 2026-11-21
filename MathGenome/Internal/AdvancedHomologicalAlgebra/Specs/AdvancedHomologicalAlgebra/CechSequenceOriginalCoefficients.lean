import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechToCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

/-! The Čech resolution bicomplex in the original section ring. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.Cech AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.CechOriginal AdvancedHomologicalAlgebra.SheafUniverseTransport
open scoped Simplicial

universe u r a v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AdvancedHomologicalAlgebra.CechSequenceOriginal

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable {U : Opens X} {A : Type v} (c : Cover U A)

abbrev CochainModules := ModuleCat.{max a u r v} (sectionRing R U)

/-- The full ordered-tuple construction before taking alternating cofaces. -/
def orderedCochains (F : PresheafOfModules.{a} R.obj) :
    CosimplicialObject (ModuleCat.{max a v} (sectionRing R U)) where
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

/-- The alternating restriction differential on the original cochains. -/
def orderedCochainComplex (F : PresheafOfModules.{a} R.obj) :
    CochainComplex (ModuleCat.{max a v} (sectionRing R U)) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (orderedCochains.{u,r,a,v} R c F)

lemma orderedCochainComplex_d (F : PresheafOfModules.{a} R.obj) (p : ℕ) :
    (orderedCochainComplex.{u,r,a,v} R c F).d p (p + 1) = ModuleCat.ofHom (differential R F c p) := by
  calc
    _ = AlgebraicTopology.AlternatingCofaceMapComplex.objD (orderedCochains.{u,r,a,v} R c F) p :=
      CochainComplex.of_d (fun n ↦ (orderedCochains.{u,r,a,v} R c F).obj ⦋n⦌)
        (AlgebraicTopology.AlternatingCofaceMapComplex.objD (orderedCochains.{u,r,a,v} R c F)) p
    _ = _ := by
      apply ModuleCat.hom_ext
      simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
        differential, ModuleCat.hom_ofHom, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
      rfl

/-- On a given degree, the morphism acts on each original tuple section. -/
def orderedCochainComponent {F G : PresheafOfModules.{a} R.obj} (f : F ⟶ G) (p : ℕ) :
    Cochains R F c p →ₗ[sectionRing R U] Cochains R G c p :=
  LinearMap.pi fun t ↦
    ((ModuleCat.restrictScalars (R.obj.map (homOfLE (tupleOpen_le c t)).op).hom).map
      (f.app (op (tupleOpen c t)))).hom.comp (LinearMap.proj t)

def orderedCochainMap {F G : PresheafOfModules.{a} R.obj} (f : F ⟶ G) :
    orderedCochainComplex.{u,r,a,v} R c F ⟶ orderedCochainComplex.{u,r,a,v} R c G where
  f p := ModuleCat.ofHom (orderedCochainComponent.{u,r,a,v} R c f p)
  comm' p q hpq := by
    have h : p + 1 = q := hpq
    subst q
    rw [orderedCochainComplex_d, orderedCochainComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    funext t
    change differential R G c p (orderedCochainComponent.{u,r,a,v} R c f p s) t =
      (f.app (op (tupleOpen c t))) (differential R F c p s t)
    simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
      Pi.smul_apply, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    let j := (homOfLE (tupleOpen_reindex_le c i.succAbove t)).op
    change G.map j (f.app _ (s (t ∘ i.succAbove))) =
      f.app (op (tupleOpen c t)) (F.map j (s (t ∘ i.succAbove)))
    exact (PresheafOfModules.naturality_apply f j _).symm

def orderedCochainFunctor : PresheafOfModules.{a} R.obj ⥤
    CochainComplex (ModuleCat.{max a v} (sectionRing R U)) ℕ where
  obj := orderedCochainComplex.{u,r,a,v} R c
  map := orderedCochainMap.{u,r,a,v} R c
  map_id F := by ext; rfl
  map_comp f g := by ext; rfl

instance : (orderedCochainFunctor.{u,r,a,v} R c).Additive where
  map_add := by intros; ext; rfl

/-- The alternating cochain complex in the ambient coefficient category. -/
abbrev cochainComplex (F : AmbientPresheaves.{a} R) :
    CochainComplex (CochainModules.{u,r,a,v} R (U := U)) ℕ :=
  orderedCochainComplex.{u,r,max a u r,v} R c F

lemma cochainComplex_d (F : AmbientPresheaves.{a} R) (p : ℕ) :
    (cochainComplex.{u,r,a,v} R c F).d p (p + 1) = ModuleCat.ofHom (differential R F c p) :=
  orderedCochainComplex_d.{u,r,max a u r,v} R c F p

abbrev cochainComponent {F G : AmbientPresheaves.{a} R} (f : F ⟶ G) (p : ℕ) :
    Cochains R F c p →ₗ[sectionRing R U] Cochains R G c p :=
  orderedCochainComponent.{u,r,max a u r,v} R c f p

abbrev cochainMap {F G : AmbientPresheaves.{a} R} (f : F ⟶ G) :
    cochainComplex.{u,r,a,v} R c F ⟶ cochainComplex.{u,r,a,v} R c G :=
  orderedCochainMap.{u,r,max a u r,v} R c f

abbrev cochainFunctor : AmbientPresheaves.{a} R ⥤
    CochainComplex (CochainModules.{u,r,a,v} R (U := U)) ℕ :=
  orderedCochainFunctor.{u,r,max a u r,v} R c

abbrev underlyingComplex (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :=
  ((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).obj K

/-- Horizontal degree is Čech degree and vertical degree is resolution degree. -/
def doubleComplex (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    HomologicalComplex₂ (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip
    (((cochainFunctor.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj (underlyingComplex.{u,r,a} R K))

/-- Applying a resolution map to each coefficient section gives the double-complex map. -/
def doubleComplexMap {K L : CochainComplex (AmbientSheaves.{a} R) ℕ} (f : K ⟶ L) :
    doubleComplex.{u,r,a,v} R c K ⟶ doubleComplex.{u,r,a,v} R c L :=
  (HomologicalComplex₂.flipFunctor (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) (.up ℕ)).map
    (((cochainFunctor.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).map
      (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map f))

abbrev doubleComplexInt (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :=
  CechToCohomology.natToIntDoubleComplex (doubleComplex.{u,r,a,v} R c K)

def doubleComplexIntMap {K L : CochainComplex (AmbientSheaves.{a} R) ℕ} (f : K ⟶ L) :
    doubleComplexInt.{u,r,a,v} R c K ⟶ doubleComplexInt.{u,r,a,v} R c L :=
  CechToCohomology.natToIntDoubleComplexMap (doubleComplexMap.{u,r,a,v} R c f)

/-- Restriction along the section-ring isomorphism, on the entire cochain universe. -/
abbrev originalScalars (_ : Cover U A) :=
  ModuleCat.restrictScalars.{max a u r v}
    (ringAt.{u,r,a} R ((opensEquiv.{max a u r} X).symm U) U
      ((opensEquiv.{max a u r} X).apply_symm_apply U)).toRingHom

instance : (originalScalars.{u,r,a,v} R c).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{r,max a u r,max a u r v}
    (ringAt.{u,r,a} R ((opensEquiv.{max a u r} X).symm U) U
      ((opensEquiv.{max a u r} X).apply_symm_apply U))).isEquivalence_functor

/-- The canonical product comparison on the original scalar action. -/
def isCochainComparison (F : AmbientSheaves.{a} R)
    (e : cochainComplex.{u,r,a,v} R c F.val ≅
      ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj
        (CechToCohomology.cechComplex (liftedRing.{a} R)
          (liftCover.{u,a,r,v} c) ((transport.{a} R).obj F).val)) : Prop :=
  ∀ (p : ℕ) (s : Cochains R F.val c p),
    (e.hom.f p) s = cochainComparison.{u,r,a,v} R F c p s

/-- The coefficient presheaf in the displayed second page, formed on the original site. -/
def localCohomology [EnoughInjectives (AmbientSheaves.{a} R)] (q : ℕ) :
    AmbientSheaves.{a} R ⥤ AmbientPresheaves.{a} R :=
  (SheafOfModules.forget R).rightDerived q

abbrev localCechCohomology [EnoughInjectives (AmbientSheaves.{a} R)] (p q : ℕ) :=
  localCohomology.{u,r,a} R q ⋙ cochainFunctor.{u,r,a,v} R c ⋙
    HomologicalComplex.homologyFunctor (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p

abbrev sectionLift (_ : Cover U A) :=
  ModuleCat.uliftFunctor.{v,max a u r} (sectionRing R U)

abbrev liftedSections (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :=
  ((Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients.sectionsValue.{a,u,r}
      R U ⋙ sectionLift.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj K

/-- The original sections map into the full cochains in degree zero. -/
def liftedAugmentation (F : AmbientPresheaves.{a} R) :
    (sectionLift.{u,r,a,v} R c).obj (F.obj (op U)) ⟶ (cochainComplex.{u,r,a,v} R c F).X 0 :=
  ModuleCat.ofHom ((augmentation R F c).comp ULift.moduleEquiv.toLinearMap)

/-- The horizontal augmentation on the actual original coefficient complex. -/
def horizontalAugmentation (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    liftedSections.{u,r,a,v} R c K ⟶ (doubleComplex.{u,r,a,v} R c K).X 0 where
  f q := liftedAugmentation.{u,r,a,v} R c (K.X q).val
  comm' q q' _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    funext t
    exact PresheafOfModules.naturality_apply (K.d q q').val _ _

abbrev intSections (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :=
  (liftedSections.{u,r,a,v} R c K).extend (ComplexShape.embeddingUpIntGE 0)

def zeroColumnIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    (doubleComplexInt.{u,r,a,v} R c K).X 0 ≅
      ((doubleComplex.{u,r,a,v} R c K).X 0).extend (ComplexShape.embeddingUpIntGE 0) :=
  let e := ComplexShape.embeddingUpIntGE 0
  ((e.extendFunctor (CochainModules.{u,r,a,v} R (U := U))).mapHomologicalComplex (.up ℕ) |>.obj
    (doubleComplex.{u,r,a,v} R c K)).extendXIso e (by simp [e])

/-- The horizontal augmentation after extension by zero in both gradings. -/
def intHorizontalAugmentation (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    intSections.{u,r,a,v} R c K ⟶ (doubleComplexInt.{u,r,a,v} R c K).X 0 :=
  HomologicalComplex.extendMap (horizontalAugmentation.{u,r,a,v} R c K)
    (ComplexShape.embeddingUpIntGE 0) ≫ (zeroColumnIso.{u,r,a,v} R c K).inv

/-- The coefficient augmentation in vertical degree zero of an injective model. -/
def verticalAugmentation {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    cochainComplex.{u,r,a,v} R c M.val ⟶ (doubleComplex.{u,r,a,v} R c J.cocomplex).flip.X 0 :=
  cochainMap.{u,r,a,v} R c (J.ι.f 0).val

/-- The complex in each bidegree retains the original differential and restriction maps. -/
def mapDouble {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] :=
  ((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))

/-- Scalar restriction applied at every integer bidegree. -/
def mapIntDouble {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] :=
  ((F.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ))

/-- Return from the integer zero extension to an original nonnegative bidegree. -/
def intBicomplexTermIso {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) (p q : ℕ) :
    ((CechToCohomology.natToIntDoubleComplex K).X (p : ℤ)).X (q : ℤ) ≅ (K.X p).X q :=
  let ee := ComplexShape.embeddingUpIntGE 0
  let e := (((ee.extendFunctor B).mapHomologicalComplex (.up ℕ)).obj K).extendXIso ee
    (by simp [ee] : ee.f p = (p : ℤ))
  (HomologicalComplex.eval B (.up ℤ) (q : ℤ)).mapIso e ≪≫
    (K.X p).extendXIso ee (by simp [ee] : ee.f q = (q : ℤ))

abbrev raisedDouble (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :=
  HomologicalComplex₂.flip
    (((CechToCohomology.cochainFunctor (liftedRing.{a} R) (liftCover.{u,a,r,v} c)).mapHomologicalComplex (.up ℕ)).obj
        ((((transport.{a} R) ⋙ SheafOfModules.forget (liftedRing.{a} R)).mapHomologicalComplex (.up ℕ)).obj K))

abbrev raisedLiftedSections (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :=
  (((transport.{a} R) ⋙ SheafOfModules.evaluation (liftedRing.{a} R)
      (op ((opensEquiv.{max a u r} X).symm U)) ⋙
      CechToCohomology.sectionLift (liftedRing.{a} R) (liftCover.{u,a,r,v} c)).mapHomologicalComplex (.up ℕ)).obj K

/-- The same horizontal augmentation after lifting the space and ring. -/
def raisedHorizontalAugmentation (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    raisedLiftedSections.{u,r,a,v} R c K ⟶ (raisedDouble.{u,r,a,v} R c K).X 0 where
  f q := CechToCohomology.liftedAugmentation (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
    ((transport.{a} R).obj (K.X q)).val
  comm' q q' _ := CechToCohomology.augmentation_cochainMap (liftedRing.{a} R)
    (liftCover.{u,a,r,v} c) ((transport.{a} R).map (K.d q q'))

abbrev sectionAtCover (M : AmbientSheaves.{a} R) :=
  sectionAt.{u,r,a} R M ((opensEquiv.{max a u r} X).symm U) U
    ((opensEquiv.{max a u r} X).apply_symm_apply U)

/-- The original local comparison on the whole alternating restriction complex,
computed using exactness of the full products and the given injective resolution. -/
def verticalComparison [EnoughInjectives (AmbientSheaves.{a} R)]
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (q : ℕ)
    [(cochainFunctor.{u,r,a,v} R c).PreservesHomology] :
    (((cochainFunctor.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj
      (underlyingComplex.{u,r,a} R J.cocomplex)).homology q ≅
    cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M) :=
  ((underlyingComplex.{u,r,a} R J.cocomplex).sc q).mapHomologyIso (cochainFunctor.{u,r,a,v} R c) ≪≫
    (cochainFunctor.{u,r,a,v} R c).mapIso (J.isoRightDerivedObj (SheafOfModules.forget R) q).symm

open DoubleComplexFirstPages (page verticalHomology)
open CechToCohomology (ColumnSpectralData)

/-- The integer version of the alternating complex of local cohomology. -/
abbrev localCechComplexInt [EnoughInjectives (AmbientSheaves.{a} R)]
    (M : AmbientSheaves.{a} R) (q : ℕ) :=
  (cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)).extend (ComplexShape.embeddingUpIntGE 0)

/-- The passage to the original Čech degree is fixed by zero extension. -/
def secondPageComparison [EnoughInjectives (AmbientSheaves.{a} R)]
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M)
    [(doubleComplexInt.{u,r,a,v} R c J.cocomplex).HasTotal (.up ℤ)]
    (D : ColumnSpectralData (doubleComplexInt.{u,r,a,v} R c J.cocomplex))
    (e : ∀ q : ℕ, verticalHomology (doubleComplexInt.{u,r,a,v} R c J.cocomplex) (q : ℤ) ≅
      localCechComplexInt.{u,r,a,v} R c M q)
    (p q : ℕ) :
    page D.filtration D.pages 2 (p : ℤ) (q : ℤ) ≅ (localCechCohomology.{u,r,a,v} R c p q).obj M :=
  D.firstPages.secondIso (p : ℤ) (q : ℤ) ≪≫
    HomologicalComplex.homologyMapIso (e q) (p : ℤ) ≪≫
    (cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)).extendHomologyIso
      (ComplexShape.embeddingUpIntGE 0) (by simp)

/-- Each nonnegative-degree component is the canonical homology comparison
for the exact tuple-product functor and the given injective resolution. -/
def verticalComponent [EnoughInjectives (AmbientSheaves.{a} R)]
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (p q : ℕ)
    [((cochainFunctor.{u,r,a,v} R c) ⋙ HomologicalComplex.eval
      (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p).PreservesHomology] :
    ((doubleComplexInt.{u,r,a,v} R c J.cocomplex).X (p : ℤ)).homology (q : ℤ) ≅
      (cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)).X p :=
  let B := CochainModules.{u,r,a,v} R (U := U)
  let K := doubleComplex.{u,r,a,v} R c J.cocomplex
  let e := ComplexShape.embeddingUpIntGE 0
  let E := ((e.extendFunctor B).mapHomologicalComplex (.up ℕ)).obj K
  let F := cochainFunctor.{u,r,a,v} R c ⋙ HomologicalComplex.eval B (.up ℕ) p
  HomologicalComplex.homologyMapIso (E.extendXIso e
    (by simp [e] : e.f p = (p : ℤ))) (q : ℤ) ≪≫
    (K.X p).extendHomologyIso e (by simp [e] : e.f q = (q : ℤ)) ≪≫
    ((underlyingComplex.{u,r,a} R J.cocomplex).sc q).mapHomologyIso F ≪≫
    F.mapIso (J.isoRightDerivedObj (SheafOfModules.forget R) q).symm

open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (sectionsValue cohomologyValue)
open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomology (resolutionModelMap)

abbrev sectionComplex (V : Opens X) (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :=
  ((sectionsValue.{a,u,r} R V).mapHomologicalComplex (.up ℕ)).obj K

private def sectionExtendComponent (V : Opens X) (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (q : Option ℕ) :
    (sectionsValue.{a,u,r} R V).obj (HomologicalComplex.extend.X K q) ≅
      HomologicalComplex.extend.X (sectionComplex.{u,r,a} R V K) q :=
  match q with
  | some _ => Iso.refl _
  | none => (sectionsValue.{a,u,r} R V).mapZeroObject

/-- Evaluation commutes with the zero extension used for the derived model. -/
def sectionExtendIso (V : Opens X) (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    ((sectionsValue.{a,u,r} R V).mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat) ≅
      (sectionComplex.{u,r,a} R V K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => sectionExtendComponent.{u,r,a} R V K (ComplexShape.embeddingUpNat.r q)) (by
      intro p q _
      let F := sectionsValue.{a,u,r} R V
      let e := ComplexShape.embeddingUpNat
      change (sectionExtendComponent.{u,r,a} R V K (e.r p)).hom ≫
          HomologicalComplex.extend.d (sectionComplex.{u,r,a} R V K) (e.r p) (e.r q) =
        F.map (HomologicalComplex.extend.d K (e.r p) (e.r q)) ≫
          (sectionExtendComponent.{u,r,a} R V K (e.r q)).hom
      cases e.r p <;> cases e.r q <;>
        simp [sectionExtendComponent, HomologicalComplex.extend.d, F])

/-- The HA-H01 comparison evaluated on the given augmentation, in natural degrees. -/
def sectionModelMap [EnoughInjectives (AmbientSheaves.{a} R)] (V : Opens X)
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ) :
    (sectionComplex.{u,r,a} R V J.cocomplex).homology n ⟶
      (cohomologyValue.{a,u,r} R V n).obj M :=
  ((sectionComplex.{u,r,a} R V J.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).inv ≫
    HomologicalComplex.homologyMap (sectionExtendIso.{u,r,a} R V J.cocomplex).inv (n : ℤ) ≫
    resolutionModelMap (sectionsValue.{a,u,r} R V) J.ι' (by infer_instance) n

/-- The abutment comparison uses the exact lift of the actual section module. -/
def liftedSectionModelMap [EnoughInjectives (AmbientSheaves.{a} R)]
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ) :
    (intSections.{u,r,a,v} R c J.cocomplex).homology (n : ℤ) ⟶
      (sectionLift.{u,r,a,v} R c).obj ((cohomologyValue.{a,u,r} R U n).obj M) :=
  ((liftedSections.{u,r,a,v} R c J.cocomplex).extendHomologyIso
    (ComplexShape.embeddingUpIntGE 0) (j := n) (j' := (n : ℤ)) (by simp)).hom ≫
    (((sectionComplex.{u,r,a} R U J.cocomplex).sc n).mapHomologyIso
      (sectionLift.{u,r,a,v} R c)).hom ≫
    (sectionLift.{u,r,a,v} R c).map (sectionModelMap.{u,r,a} R U J n)

/-- Evaluation on an original open of the local cohomology presheaf, computed
by the given resolution and the exact evaluation on presheaves. -/
def localEvaluationIso [EnoughInjectives (AmbientSheaves.{a} R)] (V : Opens X)
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (q : ℕ) :
    ((localCohomology.{u,r,a} R q).obj M).obj (op V) ≅
      (sectionComplex.{u,r,a} R V J.cocomplex).homology q :=
  let E := PresheafOfModules.evaluation R.obj (op V)
  E.mapIso (J.isoRightDerivedObj (SheafOfModules.forget R) q) ≪≫
    (((underlyingComplex.{u,r,a} R J.cocomplex).sc q).mapHomologyIso E).symm

/-- The map on the cohomology of evaluated complexes induced by the actual
restriction of presheaf sections. -/
def restrictionOnModel {W V : Opens X} (j : op W ⟶ op V)
    (K : CochainComplex (AmbientPresheaves.{a} R) ℕ) (q : ℕ) :
    (((PresheafOfModules.evaluation R.obj (op W)).mapHomologicalComplex (.up ℕ)).obj K).homology q ⟶
      (ModuleCat.restrictScalars.{max a u r} (R.obj.map j).hom).obj
        ((((PresheafOfModules.evaluation R.obj (op V)).mapHomologicalComplex (.up ℕ)).obj K).homology q) :=
  let S := K.sc q
  let E := PresheafOfModules.evaluation R.obj (op V)
  let H := ModuleCat.restrictScalars.{max a u r} (R.obj.map j).hom
  ShortComplex.homologyMap (S.mapNatTrans (PresheafOfModules.restriction R.obj j)) ≫
    (S.mapHomologyIso (E ⋙ H)).hom ≫ H.map (S.mapHomologyIso E).inv

/-- Identification of a presheaf section along the prescribed equality of opens. -/
def presheafSectionAt (F : AmbientPresheaves.{a} R)
    (W : Opens (liftedSpace.{max a u r} X)) (V : Opens X)
    (h : opensEquiv.{max a u r} X W = V) :
    F.obj (op V) ≃+ ((transportPresheaf.{a} R).obj F).obj (op W) :=
  h ▸ presheafSectionEquiv.{a} R F W

instance : (transportPresheaf.{a} R).Additive where
  map_add := by intros; ext V x; rfl

/-- The exact site comparison on homology keeps the original local restriction maps. -/
abbrev raisedLocalComparisonType [EnoughInjectives (AmbientSheaves.{a} R)] (q : ℕ) :=
  localCohomology.{u,r,a} R q ⋙ transportPresheaf.{a} R ≅
    transport.{a} R ⋙ CechToCohomology.localCohomology (liftedRing.{a} R) q

/-- Site and scalar transport is an equivalence, so it transports an
injective resolution together with its actual degree-zero augmentation. -/
def raisedResolution [(transport.{a} R).IsEquivalence] {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    InjectiveResolution ((transport.{a} R).obj M) where
  cocomplex := ((transport.{a} R).mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  injective n := ((transport.{a} R).asEquivalence.map_injective_iff (J.cocomplex.X n)).2 inferInstance
  ι := (HomologicalComplex.singleMapHomologicalComplex (transport.{a} R) (.up ℕ) 0).inv.app M ≫
    ((transport.{a} R).mapHomologicalComplex (.up ℕ)).map J.ι
  quasiIso := by
    haveI := HomologicalComplex.quasiIso_map_of_preservesHomology J.ι (transport.{a} R)
    infer_instance

/-- Local cohomology is compared through the exact transport of the same
augmented injective resolution. -/
def localPresheafIso [(transport.{a} R).IsEquivalence]
    [(transportPresheaf.{a} R).IsEquivalence] [EnoughInjectives (AmbientSheaves.{a} R)]
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (q : ℕ) :
    (transportPresheaf.{a} R).obj ((localCohomology.{u,r,a} R q).obj M) ≅
      (CechToCohomology.localCohomology (liftedRing.{a} R) q).obj ((transport.{a} R).obj M) :=
  (transportPresheaf.{a} R).mapIso (J.isoRightDerivedObj (SheafOfModules.forget R) q) ≪≫
    (((underlyingComplex.{u,r,a} R J.cocomplex).sc q).mapHomologyIso
      (transportPresheaf.{a} R)).symm ≪≫
    ((raisedResolution.{u,r,a} R J).isoRightDerivedObj
      (SheafOfModules.forget (liftedRing.{a} R)) q).symm

/-- Local cochain coordinates use the full tuple comparison, followed by the
exact local comparison on that same resolution. -/
def localModelCochainIso [(transport.{a} R).IsEquivalence]
    [(transportPresheaf.{a} R).IsEquivalence] [EnoughInjectives (AmbientSheaves.{a} R)]
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (q : ℕ)
    (g : cochainFunctor.{u,r,a,v} R c ≅
      transportPresheaf.{a} R ⋙
        CechToCohomology.cochainFunctor (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ⋙
          (originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)) :
    cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M) ≅
      ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj
        (CechToCohomology.cechComplex (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
          ((CechToCohomology.localCohomology (liftedRing.{a} R) q).obj ((transport.{a} R).obj M))) :=
  g.app _ ≪≫
    ((CechToCohomology.cochainFunctor (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ⋙
      (originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).mapIso
      (localPresheafIso.{u,r,a} R J q))

end AdvancedHomologicalAlgebra.CechSequenceOriginal

namespace Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechSequenceOriginal

/-- The full cochain functor and its augmentation commute with the canonical
coefficient carrier embedding needed to form an ambient injective resolution. -/
def coefficientCarrierComparison : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A),
    let L := liftCoefficients.{max u r,u,r,a} R.obj
    let S := ModuleCat.uliftFunctor.{max u r,max a v} (sectionRing R U)
    ∃ e : orderedCochainFunctor.{u,r,a,v} R c ⋙ S.mapHomologicalComplex (.up ℕ) ≅
        L ⋙ cochainFunctor.{u,r,a,v} R c,
      (∀ (F : PresheafOfModules.{a} R.obj) (p : ℕ) (s : Cochains R F c p)
          (t : Fin (p + 1) → A),
        ((e.hom.app F).f p (ULift.up s)) t = ULift.up.{max u r} (s t)) ∧
      ∀ (F : PresheafOfModules.{a} R.obj) (s : F.obj (op U)),
        (e.hom.app F).f 0 (ULift.up (augmentation R F c s)) =
          augmentation R (L.obj F) c (ULift.up s)

def cochainsTransport : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) (F : AmbientSheaves.{a} R),
    ∃ e, isCochainComparison.{u,r,a,v} R c F e

/-- Every original resolution bicomplex has the corresponding raised bicomplex,
with the prescribed term isomorphisms at every pair of indices. -/
def doubleTransport : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) (K : CochainComplex (AmbientSheaves.{a} R) ℕ),
    ∃ e : doubleComplex.{u,r,a,v} R c K ≅ (mapDouble (originalScalars.{u,r,a,v} R c)).obj (raisedDouble.{u,r,a,v} R c K),
      ∀ p q (s : Cochains R (K.X q).val c p),
        (e.hom.f p).f q s = cochainComparison.{u,r,a,v} R (K.X q) c p s

/-- The comparison carries the horizontal and vertical augmentations
with the same tuple and section coordinates as the bicomplex comparison. -/
def augmentationTransport : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
    let K := J.cocomplex
    ∃ (e : doubleComplex.{u,r,a,v} R c K ≅ (mapDouble (originalScalars.{u,r,a,v} R c)).obj (raisedDouble.{u,r,a,v} R c K))
      (f : liftedSections.{u,r,a,v} R c K ≅
        ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj (raisedLiftedSections.{u,r,a,v} R c K))
      (g : cochainComplex.{u,r,a,v} R c M.val ≅
        ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj
          (_root_.AdvancedHomologicalAlgebra.CechToCohomology.cechComplex (liftedRing.{a} R)
            (liftCover.{u,a,r,v} c) ((transport.{a} R).obj M).val)),
      (∀ p q (s : Cochains R (K.X q).val c p),
        (e.hom.f p).f q s = cochainComparison.{u,r,a,v} R (K.X q) c p s) ∧
      (∀ q (s : (K.X q).val.obj (op U)),
        (f.hom.f q) (ULift.up s) =
          ULift.up (sectionAtCover.{u,r,a} R (U := U) (K.X q) s)) ∧
      isCochainComparison.{u,r,a,v} R c M g ∧
      (horizontalAugmentation.{u,r,a,v} R c K ≫ e.hom.f 0 =
        f.hom ≫ ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).map
          (raisedHorizontalAugmentation.{u,r,a,v} R c K)) ∧
      (verticalAugmentation.{u,r,a,v} R c J ≫
        ((HomologicalComplex₂.flipFunctor (CochainModules.{u,r,a,v} R (U := U))
          (.up ℕ) (.up ℕ)).map e.hom).f 0 =
        g.hom ≫ ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).map
          (_root_.AdvancedHomologicalAlgebra.CechToCohomology.cochainComplexMap (liftedRing.{a} R)
            (liftCover.{u,a,r,v} c) ((transport.{a} R).map (J.ι.f 0)).val))

def cochainExactness : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A), (cochainFunctor.{u,r,a,v} R c).PreservesHomology

open _root_.AdvancedHomologicalAlgebra.CechToCohomology (ColumnSpectralData)
open _root_.AdvancedHomologicalAlgebra.DoubleComplexFirstPages (page verticalHomology)

def secondPage : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) [EnoughInjectives (AmbientSheaves.{a} R)]
    (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
    ∃ (D : ColumnSpectralData (doubleComplexInt.{u,r,a,v} R c J.cocomplex))
      (e : ∀ q : ℕ, verticalHomology (doubleComplexInt.{u,r,a,v} R c J.cocomplex) (q : ℤ) ≅
        localCechComplexInt.{u,r,a,v} R c M q)
      (h : ∀ p : ℕ, ((cochainFunctor.{u,r,a,v} R c) ⋙ HomologicalComplex.eval
        (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p).PreservesHomology),
      (∀ (p q : ℕ),
        letI := h p
        (e q).hom.f (p : ℤ) ≫
          ((cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)).extendXIso
            (ComplexShape.embeddingUpIntGE 0) (by simp :
              (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))).hom =
          (verticalComponent.{u,r,a,v} R c J p q).hom) ∧
      (∀ r p q : ℤ, p < 0 ∨ q < 0 → IsZero (page D.filtration D.pages r p q)) ∧
      ∀ p q : ℕ, ∃ f : page D.filtration D.pages 2 (p : ℤ) (q : ℤ) ≅
        (localCechCohomology.{u,r,a,v} R c p q).obj M,
        f = secondPageComparison.{u,r,a,v} R c J D e p q

open _root_.AdvancedHomologicalAlgebra.DoubleTotalization

/-- The actual row augmentation becomes a quasi-isomorphism to the signed total. -/
def totalAugmentation : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
    ∃ f : intSections.{u,r,a,v} R c J.cocomplex ⟶
      sumTotal (doubleComplexInt.{u,r,a,v} R c J.cocomplex), QuasiIso f ∧
      ∀ n : ℤ, f.f n = (intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex).f n ≫
        sumInjection (doubleComplexInt.{u,r,a,v} R c J.cocomplex) 0 n n (zero_add n)

open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (sectionsValue cohomologyValue)
open _root_.AdvancedHomologicalAlgebra.CechToCohomology (abutmentPiece abutmentPiece_decreasing)
open _root_.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
  (Stabilized cohomologyPiece closedToPage closedClass)

/-- The abutment, its finite image filtration, and the class of a closed representative. -/
def abutment : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) [EnoughInjectives (AmbientSheaves.{a} R)]
    (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
    let K := doubleComplexInt.{u,r,a,v} R c J.cocomplex
    ∃ (D : ColumnSpectralData K)
      (α : intSections.{u,r,a,v} R c J.cocomplex ⟶ sumTotal K)
      (e : ∀ n : ℕ, (sumTotal K).homology (n : ℤ) ≅
        (sectionLift.{u,r,a,v} R c).obj ((cohomologyValue.{a,u,r} R U n).obj M)),
      QuasiIso α ∧
      (∀ n : ℤ, α.f n = (intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex).f n ≫
        sumInjection K 0 n n (zero_add n)) ∧
      (∀ n : ℕ, HomologicalComplex.homologyMap α (n : ℤ) ≫ (e n).hom =
        liftedSectionModelMap.{u,r,a,v} R c J n) ∧
      (∀ n : ℕ, ∃ l h : ℤ,
        (∀ p, p ≤ l → abutmentPiece D.filtration (n : ℤ) (e n) p = ⊤) ∧
        (∀ p, h ≤ p → abutmentPiece D.filtration (n : ℤ) (e n) p = ⊥)) ∧
      ∀ (n : ℕ) (r p : ℤ) (_ : Stabilized D.filtration r p (n : ℤ)),
        ∃ g : _root_.AdvancedHomologicalAlgebra.PageCohomology.object D.filtration D.pages r p (n : ℤ) ≅
          cokernel (Subobject.ofLE _ _ (abutmentPiece_decreasing D.filtration (n : ℤ) (e n) p)),
          closedToPage D.filtration D.pages r p (n : ℤ) ≫ g.hom =
            closedClass D.filtration p (n : ℤ) ≫
              (Subobject.underlyingIso ((cohomologyPiece D.filtration p (n : ℤ)).arrow ≫
                (e n).hom)).inv ≫
              cokernel.π (Subobject.ofLE _ _ (abutmentPiece_decreasing D.filtration (n : ℤ) (e n) p))

/-- The coefficient really is HA-H01 cohomology on each original open,
and its restriction is the map of evaluated resolution complexes. -/
def localSectionComparison : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) [EnoughInjectives (AmbientSheaves.{a} R)],
    ∃ e : ∀ (V : Opens X) (q : ℕ), localCohomology.{u,r,a} R q ⋙
        PresheafOfModules.evaluation R.obj (op V) ≅ cohomologyValue.{a,u,r} R V q,
      (∀ V q (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
        (e V q).hom.app M =
          (localEvaluationIso.{u,r,a} R V J q).hom ≫ sectionModelMap.{u,r,a} R V J q) ∧
      ∀ {W V : Opens X} (j : op W ⟶ op V) (M : AmbientSheaves.{a} R)
        (J : InjectiveResolution M) (q : ℕ),
        let H := ModuleCat.restrictScalars.{max a u r} (R.obj.map j).hom
        ((localCohomology.{u,r,a} R q).obj M).map j ≫ H.map (localEvaluationIso.{u,r,a} R V J q).hom =
          (localEvaluationIso.{u,r,a} R W J q).hom ≫
            restrictionOnModel.{u,r,a} R j (underlyingComplex.{u,r,a} R J.cocomplex) q

/-- From the first page onward the maps attached to coefficient
morphisms are independent of resolution lifts and give comparison
isomorphisms between any pair of resolutions. -/
def pageMaps : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) [EnoughInjectives (AmbientSheaves.{a} R)],
    ∃ (D : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M),
        ColumnSpectralData (doubleComplexInt.{u,r,a,v} R c J.cocomplex))
      (F : ∀ {M N : AmbientSheaves.{a} R} (I : InjectiveResolution M) (J : InjectiveResolution N)
          (_φ : I.cocomplex ⟶ J.cocomplex),
        _root_.AdvancedHomologicalAlgebra.FilteredMap
          ⟨sumTotal _, (D I).filtration⟩ ⟨sumTotal _, (D J).filtration⟩)
      (P : ∀ {M N : AmbientSheaves.{a} R} (I : InjectiveResolution M) (J : InjectiveResolution N)
          (φ : I.cocomplex ⟶ J.cocomplex),
        _root_.AdvancedHomologicalAlgebra.FilteredPageFunctoriality.MapData
          (F I J φ) (D I).pages (D J).pages),
      (∀ {M N : AmbientSheaves.{a} R} (I : InjectiveResolution M) (J : InjectiveResolution N)
          (φ : I.cocomplex ⟶ J.cocomplex),
        (F I J φ).hom = HomologicalComplex₂.total.map (doubleComplexIntMap.{u,r,a,v} R c φ) (.up ℤ)) ∧
      (∀ {M N : AmbientSheaves.{a} R} (f : M ⟶ N)
          (I : InjectiveResolution M) (J : InjectiveResolution N) (φ ψ : I.cocomplex ⟶ J.cocomplex),
        I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0 →
        ∀ r p n : ℤ, 1 ≤ r → (P I J φ).map r p n = (P I J ψ).map r p n) ∧
      (∀ {M : AmbientSheaves.{a} R} (I : InjectiveResolution M) (r p n : ℤ),
        0 ≤ r → (P I I (𝟙 I.cocomplex)).map r p n = 𝟙 _) ∧
      (∀ {M N L : AmbientSheaves.{a} R} (I : InjectiveResolution M) (J : InjectiveResolution N)
          (K : InjectiveResolution L) (φ : I.cocomplex ⟶ J.cocomplex) (ψ : J.cocomplex ⟶ K.cocomplex)
          (r p n : ℤ), 0 ≤ r →
        (P I K (φ ≫ ψ)).map r p n = (P I J φ).map r p n ≫ (P J K ψ).map r p n) ∧
      ∀ {M : AmbientSheaves.{a} R} (I J : InjectiveResolution M) (φ : I.cocomplex ⟶ J.cocomplex),
        I.ι.f 0 ≫ φ.f 0 = J.ι.f 0 →
        ∀ r p n : ℤ, 1 ≤ r → IsIso ((P I J φ).map r p n)


section LimitTransport

open _root_.AdvancedHomologicalAlgebra
open _root_.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence (closed)
open _root_.AdvancedHomologicalAlgebra.PageCohomology (object)

variable {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]

/-- The quotient of two adjacent terms in the transported image filtration. -/
abbrev limitQuotient {K : CochainComplex B ℤ} (P : Filtration K)
    (n : ℤ) {H : B} (a : K.homology n ≅ H) (p : ℤ) :=
  cokernel (Subobject.ofLE _ _ (abutmentPiece_decreasing P n a p))

/-- Send a closed representative to its class in the graded abutment. -/
abbrev limitClass {K : CochainComplex B ℤ} (P : Filtration K)
    (n : ℤ) {H : B} (a : K.homology n ≅ H) (p : ℤ) :
    (closed P p n : B) ⟶ limitQuotient P n a p :=
  closedClass P p n ≫
    (Subobject.underlyingIso ((cohomologyPiece P p n).arrow ≫ a.hom)).inv ≫
    cokernel.π (Subobject.ofLE _ _ (abutmentPiece_decreasing P n a p))

/-- The identified filtered abutment and its closed-representative comparison
commute with the actual degreewise scalar equivalence on the total complex. -/
def comparesLimits (G : C ⥤ B) [G.Additive] [G.PreservesHomology]
    {K : CochainComplex B ℤ} {L : CochainComplex C ℤ}
    (P : Filtration K) (Q : Filtration L)
    (D : F03Specs.PageData P) (E : F03Specs.PageData Q)
    (t : K ≅ (G.mapHomologicalComplex (.up ℤ)).obj L) : Prop :=
    ∀ (n : ℤ) {H : B} {H' : C} (a : K.homology n ≅ H) (a' : L.homology n ≅ H'),
    let a₀ := a.symm ≪≫ (HomologicalComplex.homologyMapIso t n ≪≫
      (L.sc n).mapHomologyIso G) ≪≫ G.mapIso a'
    ∃ (z : ∀ p : ℤ, (closed P p n : B) ≅ G.obj (closed Q p n : C))
      (f : ∀ p : ℤ, (abutmentPiece P n a p : B) ≅ G.obj (abutmentPiece Q n a' p : C))
      (g : ∀ p : ℤ, limitQuotient P n a p ≅ G.obj (limitQuotient Q n a' p)),
      (∀ p, (z p).hom ≫ G.map (closed Q p n).arrow = (closed P p n).arrow ≫ t.hom.f n) ∧
      (∀ p, (f p).hom ≫ G.map (abutmentPiece Q n a' p).arrow =
        (abutmentPiece P n a p).arrow ≫ a₀.hom) ∧
      (∀ p, cokernel.π (Subobject.ofLE _ _ (abutmentPiece_decreasing P n a p)) ≫ (g p).hom =
        (f p).hom ≫ G.map (cokernel.π (Subobject.ofLE _ _ (abutmentPiece_decreasing Q n a' p)))) ∧
      (∀ p, limitClass P n a p ≫ (g p).hom = (z p).hom ≫ G.map (limitClass Q n a' p)) ∧
      ∀ r p : ℤ, Stabilized P r p n → Stabilized Q r p n →
        ∀ (l : object P D r p n ≅ limitQuotient P n a p)
          (l' : object Q E r p n ≅ limitQuotient Q n a' p),
          closedToPage P D r p n ≫ l.hom = limitClass P n a p →
          closedToPage Q E r p n ≫ l'.hom = limitClass Q n a' p →
          ∃ e : object P D r p n ≅ G.obj (object Q E r p n),
            closedToPage P D r p n ≫ e.hom = (z p).hom ≫ G.map (closedToPage Q E r p n) ∧
            e.hom ≫ G.map l'.hom = l.hom ≫ (g p).hom

end LimitTransport


section PageTransport

open _root_.AdvancedHomologicalAlgebra
open _root_.AdvancedHomologicalAlgebra.FilteredPage (almost toPage)
open _root_.AdvancedHomologicalAlgebra.PageCohomology (object)

/-- Transport on the positive pages is induced by the same scalar and
filtered total comparison on almost cycles and commutes with their differentials. -/
def comparesPages {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
    (G : C ⥤ B) [G.Additive]
    {K : CochainComplex B ℤ} {L : CochainComplex C ℤ}
    (P : Filtration K) (Q : Filtration L)
    (D : F03Specs.PageData P) (E : F03Specs.PageData Q)
    (t : K ≅ (G.mapHomologicalComplex (.up ℤ)).obj L) : Prop :=
  ∃ (z : ∀ r p n : ℤ, (almost P r p n : B) ≅ G.obj (almost Q r p n : C))
    (c : ∀ (r : ℤ) (_ : 1 ≤ r) (p n : ℤ), object P D r p n ≅ G.obj (object Q E r p n)),
    (∀ r p n, (z r p n).hom ≫ G.map (almost Q r p n).arrow =
      (almost P r p n).arrow ≫ t.hom.f n) ∧
    (∀ (r : ℤ) (hr : 1 ≤ r) (p n : ℤ),
      toPage P r p n (D.containment r p n) ≫ (c r hr p n).hom =
        (z r p n).hom ≫ G.map (toPage Q r p n (E.containment r p n))) ∧
    ∀ (r : ℤ) (hr : 1 ≤ r) (p n : ℤ),
      D.differential r (by omega) p n ≫ (c r hr (p+r) (n+1)).hom =
        (c r hr p n).hom ≫ G.map (E.differential r (by omega) p n)

end PageTransport


section ColumnSecondTransport
open _root_.AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations (Bicomplex)

open _root_.AdvancedHomologicalAlgebra
open _root_.AdvancedHomologicalAlgebra.FilteredPage (almost toPage)

/-- The scalar comparison on the actual E₂ page agrees with the canonical
HA-B03 iterated cohomology comparison of columns, including representatives. -/
def comparesColumnSecond {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
    (G : C ⥤ B) [G.Additive] [G.PreservesHomology]
    {K : Bicomplex B} {L : Bicomplex C} [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)]
    (D : ColumnSpectralData K) (E : ColumnSpectralData L)
    (e : K ≅ (mapIntDouble G).obj L)
    (t : sumTotal K ≅ (G.mapHomologicalComplex (.up ℤ)).obj (sumTotal L)) : Prop :=
  ∃ w : ∀ q : ℤ, verticalHomology K q ≅ (G.mapHomologicalComplex (.up ℤ)).obj (verticalHomology L q),
    (∀ p q : ℤ, (w q).hom.f p =
      (HomologicalComplex.homologyMapIso (asIso (e.hom.f p)) q ≪≫
        ((L.X p).sc q).mapHomologyIso G).hom) ∧
    ∀ p q : ℤ,
      ∀ (z : (almost D.filtration 2 p (p+q) : B) ⟶ G.obj (almost E.filtration 2 p (p+q) : C))
        (c : page D.filtration D.pages 2 p q ⟶ G.obj (page E.filtration E.pages 2 p q)),
      z ≫ G.map (almost E.filtration 2 p (p+q)).arrow =
        (almost D.filtration 2 p (p+q)).arrow ≫ t.hom.f (p+q) →
      toPage D.filtration 2 p (p+q) (D.pages.containment 2 p (p+q)) ≫ c =
        z ≫ G.map (toPage E.filtration 2 p (p+q) (E.pages.containment 2 p (p+q))) →
      c ≫ G.map (E.firstPages.secondIso p q).hom =
        (D.firstPages.secondIso p q).hom ≫
          (HomologicalComplex.homologyMapIso (w q) p ≪≫
            ((verticalHomology L q).sc p).mapHomologyIso G).hom

end ColumnSecondTransport

/-- The signed totals compare on every diagonal inclusion, over the unchanged
original section ring. The raised model is the actual image of the original
augmented injective resolution under the site equivalence. -/
def signedTotalTransport : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
    let S := originalScalars.{u,r,a,v} R c
    let C := doubleComplexInt.{u,r,a,v} R c J.cocomplex
    ∃ (J' : InjectiveResolution ((transport.{a} R).obj M)),
      J'.cocomplex = ((transport.{a} R).mapHomologicalComplex (.up ℕ)).obj J.cocomplex ∧
      HEq (J'.ι.f 0) ((transport.{a} R).map (J.ι.f 0)) ∧
      let K := _root_.AdvancedHomologicalAlgebra.CechToCohomology.resolutionDoubleComplexInt
        (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ((transport.{a} R).obj M) J'
      ∃ (e : C ≅ (mapIntDouble S).obj K)
        (t : sumTotal C ≅ (S.mapHomologicalComplex (.up ℤ)).obj (sumTotal K)),
        (∀ (p q : ℕ) (x : Cochains R (J.cocomplex.X q).val c p),
          HEq (((intBicomplexTermIso (doubleComplex.{u,r,a,v} R c J.cocomplex) p q).inv ≫
            (e.hom.f (p : ℤ)).f (q : ℤ) ≫ S.map
              (intBicomplexTermIso
                (_root_.AdvancedHomologicalAlgebra.CechToCohomology.resolutionDoubleComplex
                  (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ((transport.{a} R).obj M) J') p q).hom) x)
            (cochainComparison.{u,r,a,v} R (J.cocomplex.X q) c p x)) ∧
        (∀ (p q n : ℤ) (h : p + q = n),
          sumInjection C p q n h ≫ t.hom.f n =
            (e.hom.f p).f q ≫ S.map (sumInjection K p q n h)) ∧
        (∀ (D : ColumnSpectralData C) (E : ColumnSpectralData K),
          (∀ p n : ℤ, Subobject.mk ((D.filtration.piece p n).arrow ≫ t.hom.f n) =
            Subobject.mk (S.map ((E.filtration.piece p n).arrow))) ∧
          comparesLimits S D.filtration E.filtration D.pages E.pages t ∧
          comparesPages S D.filtration E.filtration D.pages E.pages t ∧
          comparesColumnSecond S D E e t) ∧
        ∃ (s : intSections.{u,r,a,v} R c J.cocomplex ≅
            (S.mapHomologicalComplex (.up ℤ)).obj
              (_root_.AdvancedHomologicalAlgebra.CechToCohomology.sectionComplexInt
                (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ((transport.{a} R).obj M) J'))
          (α : intSections.{u,r,a,v} R c J.cocomplex ⟶ sumTotal C)
          (β : _root_.AdvancedHomologicalAlgebra.CechToCohomology.sectionComplexInt
                (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ((transport.{a} R).obj M) J' ⟶ sumTotal K),
          QuasiIso α ∧ QuasiIso β ∧
          (∀ (q : ℕ) (x : (J.cocomplex.X q).val.obj (op U)),
            let ee := ComplexShape.embeddingUpIntGE 0
            let hq : ee.f q = (q : ℤ) := by simp [ee]
            HEq ((((liftedSections.{u,r,a,v} R c J.cocomplex).extendXIso ee hq).inv ≫
              s.hom.f (q : ℤ) ≫ S.map
                ((_root_.AdvancedHomologicalAlgebra.CechToCohomology.liftedSectionComplex
                  (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ((transport.{a} R).obj M) J').extendXIso ee hq).hom)
                    (ULift.up x))
                (ULift.up.{v} (sectionAtCover.{u,r,a} R (U := U) (J.cocomplex.X q) x))) ∧
          (∀ n : ℤ, α.f n = (intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex).f n ≫
            sumInjection C 0 n n (zero_add n)) ∧
          (∀ n : ℤ, β.f n =
            (_root_.AdvancedHomologicalAlgebra.CechToCohomology.resolutionAugmentation
              (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ((transport.{a} R).obj M) J').f n ≫
                sumInjection K 0 n n (zero_add n)) ∧
          α ≫ t.hom = s.hom ≫ (S.mapHomologicalComplex (.up ℤ)).map β

set_option maxHeartbeats 1500000 in
/-- The local-cohomology presheaf comparison is normalized on every augmented
injective resolution, and the alternating complex uses the same tuple comparison. -/
def localCarrierTransport : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) [EnoughInjectives (AmbientSheaves.{a} R)],
    let R' := liftedRing.{a} R
    let T := transport.{a} R
    let P := transportPresheaf.{a} R
    let S := originalScalars.{u,r,a,v} R c
    let c' := liftCover.{u,a,r,v} c
    let G := _root_.AdvancedHomologicalAlgebra.CechToCohomology.cochainFunctor R' c'
    ∃ (e : ∀ q : ℕ, raisedLocalComparisonType.{u,r,a} R q)
      (g : cochainFunctor.{u,r,a,v} R c ≅
        P ⋙ G ⋙ S.mapHomologicalComplex (.up ℕ)),
      (∀ (F : AmbientPresheaves.{a} R) (p : ℕ) (s : Cochains R F c p)
          (t : Fin (p + 1) → A),
        ((g.hom.app F).f p s) t =
          presheafSectionAt.{u,r,a} R F _ _ (liftCover_tuple.{u,r,a,v} c t) (s t)) ∧
      ∃ (hP : P.IsEquivalence) (hT : T.IsEquivalence)
        (hF : (cochainFunctor.{u,r,a,v} R c).PreservesHomology) (hG : G.PreservesHomology),
        letI := hP
        letI := hT
        letI := hF
        letI := hG
        ∀ (M : AmbientSheaves.{a} R) (J : InjectiveResolution M) (q : ℕ),
          ((e q).hom.app M =
            P.map (J.isoRightDerivedObj (SheafOfModules.forget R) q).hom ≫
              (((underlyingComplex.{u,r,a} R J.cocomplex).sc q).mapHomologyIso P).inv ≫
                ((raisedResolution.{u,r,a} R J).isoRightDerivedObj
                  (SheafOfModules.forget R') q).inv) ∧
          let B := S.mapHomologicalComplex (.up ℕ)
          let J' := raisedResolution.{u,r,a} R J
          let L := (G.mapHomologicalComplex (.up ℕ)).obj
            (_root_.AdvancedHomologicalAlgebra.CechToCohomology.underlyingComplex R' J'.cocomplex)
          let K := underlyingComplex.{u,r,a} R J.cocomplex
          let i := (NatIso.mapHomologicalComplex g (.up ℕ)).app K
          let w := (L.sc q).mapHomologyIso B
          let b := ((_root_.AdvancedHomologicalAlgebra.CechToCohomology.underlyingComplex R' J'.cocomplex).sc q).mapHomologyIso G ≪≫
            G.mapIso (J'.isoRightDerivedObj (SheafOfModules.forget R') q).symm
          HomologicalComplex.homologyMap i.hom q ≫ w.hom ≫ B.map b.hom =
            (verticalComparison.{u,r,a,v} R c J q).hom ≫
            (g.hom.app ((localCohomology.{u,r,a} R q).obj M)) ≫
              (G ⋙ B).map ((e q).hom.app M)

/-- The abutment comparison uses the natural transport of the actual derived section
modules and the derived-unit normalization on each of the two injective models. -/
def abutmentTransport : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) [EnoughInjectives (AmbientSheaves.{a} R)],
    let W := (opensEquiv.{max a u r} X).symm U
    let h := (opensEquiv.{max a u r} X).apply_symm_apply U
    let S₀ := ModuleCat.restrictScalars.{max a u r} (ringAt.{u,r,a} R W U h).toRingHom
    let S := originalScalars.{u,r,a,v} R c
    let R' := liftedRing.{a} R
    let c' := liftCover.{u,a,r,v} c
    ∃ (τ : ∀ n : ℕ, cohomologyValue.{a,u,r} R U n ≅
        transport.{a} R ⋙ _root_.AdvancedHomologicalAlgebra.SheafTheory.sectionCohomology R' W n ⋙ S₀),
      ∀ (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
        let C := doubleComplexInt.{u,r,a,v} R c J.cocomplex
        let M' := (transport.{a} R).obj M
        ∃ (J' : InjectiveResolution M'),
          J'.cocomplex = ((transport.{a} R).mapHomologicalComplex (.up ℕ)).obj J.cocomplex ∧
          HEq (J'.ι.f 0) ((transport.{a} R).map (J.ι.f 0)) ∧
          let B := _root_.AdvancedHomologicalAlgebra.CechToCohomology.resolutionDoubleComplex R' c' M' J'
          let K := _root_.AdvancedHomologicalAlgebra.CechToCohomology.resolutionDoubleComplexInt R' c' M' J'
          let V := _root_.AdvancedHomologicalAlgebra.CechToCohomology.sectionComplexInt R' c' M' J'
          ∃ (e : C ≅ (mapIntDouble S).obj K)
            (t : sumTotal C ≅ (S.mapHomologicalComplex (.up ℤ)).obj (sumTotal K))
            (α : intSections.{u,r,a,v} R c J.cocomplex ⟶ sumTotal C)
            (β : V ⟶ sumTotal K),
            (∀ p q : ℕ, ∀ x : Cochains R (J.cocomplex.X q).val c p,
              HEq (((intBicomplexTermIso (doubleComplex.{u,r,a,v} R c J.cocomplex) p q).inv ≫
                  (e.hom.f (p : ℤ)).f (q : ℤ) ≫ S.map (intBicomplexTermIso B p q).hom) x)
                (cochainComparison.{u,r,a,v} R (J.cocomplex.X q) c p x)) ∧
            (∀ (p q n : ℤ) (h : p + q = n), sumInjection C p q n h ≫ t.hom.f n =
                (e.hom.f p).f q ≫ S.map (sumInjection K p q n h)) ∧
            (∀ n : ℤ, α.f n = (intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex).f n ≫
              sumInjection C 0 n n (zero_add n)) ∧
            (∀ n : ℤ, β.f n =
              (_root_.AdvancedHomologicalAlgebra.CechToCohomology.resolutionAugmentation R' c' M' J').f n ≫
                sumInjection K 0 n n (zero_add n)) ∧
            ∀ n : ℕ, ∃ (g : (sumTotal C).homology (n : ℤ) ≅
                (sectionLift.{u,r,a,v} R c).obj ((cohomologyValue.{a,u,r} R U n).obj M))
              (g' : (sumTotal K).homology (n : ℤ) ≅
                (_root_.AdvancedHomologicalAlgebra.CechToCohomology.liftedSectionCohomology R' c' n).obj M'),
              HomologicalComplex.homologyMap α (n : ℤ) ≫ g.hom =
                liftedSectionModelMap.{u,r,a,v} R c J n ∧
              HomologicalComplex.homologyMap β (n : ℤ) ≫ g'.hom =
                (_root_.AdvancedHomologicalAlgebra.CechToCohomology.liftedSectionHomologyIso R' c' M' J' n).hom ≫
                  (_root_.AdvancedHomologicalAlgebra.CechToCohomology.sectionLift R' c').map
                    (_root_.AdvancedHomologicalAlgebra.CechToCohomology.sectionResolutionIsoNat R' W M' J' n).inv ∧
              (HomologicalComplex.homologyMap t.hom (n : ℤ) ≫
                  (((sumTotal K).sc (n : ℤ)).mapHomologyIso S).hom ≫ S.map g'.hom =
                g.hom ≫ (sectionLift.{u,r,a,v} R c).map ((τ n).hom.app M)) ∧
              ∀ (D : ColumnSpectralData C) (E : ColumnSpectralData K) (p : ℤ),
                ∃ f : (abutmentPiece D.filtration (n : ℤ) g p : CochainModules.{u,r,a,v} R (U := U)) ≅
                    S.obj (abutmentPiece E.filtration (n : ℤ) g' p :
                      ModuleCat (sectionRing R' W)),
                  f.hom ≫ S.map (abutmentPiece E.filtration (n : ℤ) g' p).arrow =
                    (abutmentPiece D.filtration (n : ℤ) g p).arrow ≫
                      (sectionLift.{u,r,a,v} R c).map ((τ n).hom.app M)

end Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients


namespace AdvancedHomologicalAlgebra.CechSequenceOriginal

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable {U : Opens X} {A : Type v} (c : Cover U A)

open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (cohomologyValue sectionsValue)

abbrev liftedSectionsMap {K L : CochainComplex (AmbientSheaves.{a} R) ℕ} (φ : K ⟶ L) :=
  (((sectionsValue.{a,u,r} R U ⋙ sectionLift.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ))).map φ

abbrev intSectionsMap {K L : CochainComplex (AmbientSheaves.{a} R) ℕ} (φ : K ⟶ L) :=
  HomologicalComplex.extendMap (liftedSectionsMap.{u,r,a,v} R c φ)
    (ComplexShape.embeddingUpIntGE 0)

abbrev localCechComplexIntMap [EnoughInjectives (AmbientSheaves.{a} R)]
    (q : ℕ) {M N : AmbientSheaves.{a} R} (f : M ⟶ N) :=
  HomologicalComplex.extendMap
    ((cochainFunctor.{u,r,a,v} R c).map ((localCohomology.{u,r,a} R q).map f))
    (ComplexShape.embeddingUpIntGE 0)

end AdvancedHomologicalAlgebra.CechSequenceOriginal

namespace Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechSequenceOriginal
open _root_.AdvancedHomologicalAlgebra.DoubleTotalization
open _root_.AdvancedHomologicalAlgebra.DoubleComplexFirstPages (page verticalHomology verticalHomologyMap)
open _root_.AdvancedHomologicalAlgebra.CechToCohomology (ColumnSpectralData abutmentPiece
  abutmentPieceMap abutmentPiece_decreasing abutmentGradedMap)
open _root_.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
  (Stabilized closedToPage closedClass cohomologyPiece)
open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients (cohomologyValue)

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable {U : Opens X} {A : Type v} (c : Cover U A)

variable [EnoughInjectives (AmbientSheaves.{a} R)]

/-- The choices shared by the second-page and abutment naturality squares,
with the actual product and augmentation comparisons as their normalizations. -/
structure NaturalityData where
  data : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M),
    ColumnSpectralData (doubleComplexInt.{u,r,a,v} R c J.cocomplex)
  firstQuadrant : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (r p q : ℤ),
    p < 0 ∨ q < 0 → IsZero (page (data J).filtration (data J).pages r p q)
  vertical : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (q : ℕ),
    verticalHomology (doubleComplexInt.{u,r,a,v} R c J.cocomplex) (q : ℤ) ≅
      localCechComplexInt.{u,r,a,v} R c M q
  exactTuple : ∀ p : ℕ, ((cochainFunctor.{u,r,a,v} R c) ⋙ HomologicalComplex.eval
    (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p).PreservesHomology
  vertical_component : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (p q : ℕ),
    letI := exactTuple p
    (vertical J q).hom.f (p : ℤ) ≫
      ((cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)).extendXIso
        (ComplexShape.embeddingUpIntGE 0)
        (by simp : (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))).hom =
      (verticalComponent.{u,r,a,v} R c J p q).hom
  augmentation : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M),
    intSections.{u,r,a,v} R c J.cocomplex ⟶ sumTotal (doubleComplexInt.{u,r,a,v} R c J.cocomplex)
  augmentation_quasiIso : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M),
    QuasiIso (augmentation J)
  augmentation_formula : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℤ),
    (augmentation J).f n = (intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex).f n ≫
      sumInjection (doubleComplexInt.{u,r,a,v} R c J.cocomplex) 0 n n (zero_add n)
  abutment : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ),
    (sumTotal (doubleComplexInt.{u,r,a,v} R c J.cocomplex)).homology (n : ℤ) ≅
      (sectionLift.{u,r,a,v} R c).obj ((cohomologyValue.{a,u,r} R U n).obj M)
  abutment_formula : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ),
    HomologicalComplex.homologyMap (augmentation J) (n : ℤ) ≫ (abutment J n).hom =
      liftedSectionModelMap.{u,r,a,v} R c J n
  finite : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ),
    ∃ l h : ℤ,
      (∀ p, p ≤ l → abutmentPiece (data J).filtration (n : ℤ) (abutment J n) p = ⊤) ∧
      (∀ p, h ≤ p → abutmentPiece (data J).filtration (n : ℤ) (abutment J n) p = ⊥)
  limit : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ) (r p : ℤ)
    (_ : Stabilized (data J).filtration r p (n : ℤ)),
    _root_.AdvancedHomologicalAlgebra.PageCohomology.object
      (data J).filtration (data J).pages r p (n : ℤ) ≅
      cokernel (Subobject.ofLE _ _ (abutmentPiece_decreasing
        (data J).filtration (n : ℤ) (abutment J n) p))
  limit_formula : ∀ {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ)
    (r p : ℤ) (hs : Stabilized (data J).filtration r p (n : ℤ)),
    let F := (data J).filtration
    closedToPage F (data J).pages r p (n : ℤ) ≫ (limit J n r p hs).hom =
      closedClass F p (n : ℤ) ≫
        (Subobject.underlyingIso ((cohomologyPiece F p (n : ℤ)).arrow ≫ (abutment J n).hom)).inv ≫
        cokernel.π (Subobject.ofLE _ _ (abutmentPiece_decreasing F (n : ℤ) (abutment J n) p))
  filteredMap : ∀ {M N : AmbientSheaves.{a} R} (I : InjectiveResolution M)
    (J : InjectiveResolution N) (_φ : I.cocomplex ⟶ J.cocomplex),
    _root_.AdvancedHomologicalAlgebra.FilteredMap
      ⟨sumTotal _, (data I).filtration⟩ ⟨sumTotal _, (data J).filtration⟩
  filteredMap_formula : ∀ {M N : AmbientSheaves.{a} R} (I : InjectiveResolution M)
    (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex),
    (filteredMap I J φ).hom = HomologicalComplex₂.total.map
      (doubleComplexIntMap.{u,r,a,v} R c φ) (.up ℤ)
  pageMap : ∀ {M N : AmbientSheaves.{a} R} (I : InjectiveResolution M)
    (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex),
    _root_.AdvancedHomologicalAlgebra.FilteredPageFunctoriality.MapData
      (filteredMap I J φ) (data I).pages (data J).pages
  page_identity : ∀ {M : AmbientSheaves.{a} R} (I : InjectiveResolution M) (r p n : ℤ),
    0 ≤ r → (pageMap I I (𝟙 I.cocomplex)).map r p n = 𝟙 _
  page_composition : ∀ {M N L : AmbientSheaves.{a} R} (I : InjectiveResolution M)
    (J : InjectiveResolution N) (K : InjectiveResolution L) (φ : I.cocomplex ⟶ J.cocomplex)
    (ψ : J.cocomplex ⟶ K.cocomplex) (r p n : ℤ), 0 ≤ r →
    (pageMap I K (φ ≫ ψ)).map r p n = (pageMap I J φ).map r p n ≫ (pageMap J K ψ).map r p n
  page_lift_independent : ∀ {M N : AmbientSheaves.{a} R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ ψ : I.cocomplex ⟶ J.cocomplex),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0 →
    ∀ r p n : ℤ, 1 ≤ r → (pageMap I J φ).map r p n = (pageMap I J ψ).map r p n
  page_resolution_iso : ∀ {M : AmbientSheaves.{a} R} (I J : InjectiveResolution M)
    (φ : I.cocomplex ⟶ J.cocomplex), I.ι.f 0 ≫ φ.f 0 = J.ι.f 0 →
    ∀ r p n : ℤ, 1 ≤ r → IsIso ((pageMap I J φ).map r p n)
  filtration_eq : ∀ {M : AmbientSheaves.{a} R} (I J : InjectiveResolution M) (n : ℕ) (p : ℤ),
    abutmentPiece (data I).filtration (n : ℤ) (abutment I n) p =
      abutmentPiece (data J).filtration (n : ℤ) (abutment J n) p

/-- Naturality of the coefficient augmentation, local cohomology comparison,
second page, abutment and its filtration for every lift of every coefficient map. -/
def coefficientNaturality : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) [EnoughInjectives (AmbientSheaves.{a} R)],
    ∃ D : NaturalityData.{u,r,a,v} R c,
      (∀ {M N : AmbientSheaves.{a} R} (I : InjectiveResolution M) (J : InjectiveResolution N)
        (φ : I.cocomplex ⟶ J.cocomplex),
        intSectionsMap.{u,r,a,v} R c φ ≫ D.augmentation J =
          D.augmentation I ≫ HomologicalComplex₂.total.map
            (doubleComplexIntMap.{u,r,a,v} R c φ) (.up ℤ)) ∧
      (∀ {M N : AmbientSheaves.{a} R} (I : InjectiveResolution M) (J : InjectiveResolution N)
        (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (r p : ℤ)
        (hs : Stabilized (D.data I).filtration r p (n : ℤ))
        (ht : Stabilized (D.data J).filtration r p (n : ℤ)),
        (D.pageMap I J φ).map r p (n : ℤ) ≫ (D.limit J n r p ht).hom =
          (D.limit I n r p hs).hom ≫
            abutmentGradedMap (D.filteredMap I J φ) (n : ℤ) (D.abutment I n) (D.abutment J n) p) ∧
      ∀ {M N : AmbientSheaves.{a} R} (I : InjectiveResolution M) (J : InjectiveResolution N)
        (φ : I.cocomplex ⟶ J.cocomplex) (f : M ⟶ N),
        I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 →
        (cochainMap.{u,r,a,v} R c f.val ≫ verticalAugmentation.{u,r,a,v} R c J =
          verticalAugmentation.{u,r,a,v} R c I ≫
            ((HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map
              (doubleComplexMap.{u,r,a,v} R c φ)).f 0) ∧
        (∀ q : ℕ, verticalHomologyMap (doubleComplexInt.{u,r,a,v} R c I.cocomplex)
            (doubleComplexIntMap.{u,r,a,v} R c φ) (q : ℤ) ≫ (D.vertical J q).hom =
          (D.vertical I q).hom ≫ localCechComplexIntMap.{u,r,a,v} R c q f) ∧
        (∀ p q : ℕ, (D.pageMap I J φ).map 2 (p : ℤ) ((p : ℤ) + (q : ℤ)) ≫
            (secondPageComparison.{u,r,a,v} R c J (D.data J) (D.vertical J) p q).hom =
          (secondPageComparison.{u,r,a,v} R c I (D.data I) (D.vertical I) p q).hom ≫
            (localCechCohomology.{u,r,a,v} R c p q).map f) ∧
        (∀ n : ℕ, HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
            (doubleComplexIntMap.{u,r,a,v} R c φ) (.up ℤ)) (n : ℤ) ≫ (D.abutment J n).hom =
          (D.abutment I n).hom ≫
            (sectionLift.{u,r,a,v} R c).map ((cohomologyValue.{a,u,r} R U n).map f)) ∧
        ∀ (n : ℕ) (p : ℤ),
          abutmentPieceMap (D.filteredMap I J φ) (n : ℤ) (D.abutment I n) (D.abutment J n) p ≫
            (abutmentPiece (D.data J).filtration (n : ℤ) (D.abutment J n) p).arrow =
          (abutmentPiece (D.data I).filtration (n : ℤ) (D.abutment I n) p).arrow ≫
            (sectionLift.{u,r,a,v} R c).map ((cohomologyValue.{a,u,r} R U n).map f)

/-- The cohomology map of the total in every degree is independent of the lift. -/
def totalLiftIndependence : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) {M N : AmbientSheaves.{a} R}
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ ψ : I.cocomplex ⟶ J.cocomplex) (f : M ⟶ N),
    I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 → I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0 →
    ∀ n : ℤ,
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (doubleComplexIntMap.{u,r,a,v} R c φ) (.up ℤ)) n =
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (doubleComplexIntMap.{u,r,a,v} R c ψ) (.up ℤ)) n

end Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (cohomologyValue sectionsValue restrictSections restrictSectionScalars)
open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomology (resolutionModelMap)
open _root_.AdvancedHomologicalAlgebra.CechSequenceOriginal

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable [EnoughInjectives (AmbientSheaves.{a} R)]

/-- The normalization of HA-H01's restriction on an actual augmented
integer-indexed injective resolution. -/
def IsRestrictionModelComparison {W V : Opens X} (j : op W ⟶ op V)
    (t : ∀ n : ℕ, cohomologyValue.{a,u,r} R W n ⟶
      cohomologyValue.{a,u,r} R V n ⋙ restrictSectionScalars.{a} X R j.unop) : Prop :=
  ∀ (M : AmbientSheaves.{a} R) (K : CochainComplex (AmbientSheaves.{a} R) ℤ)
    [K.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M ⟶ K)
    (hi : QuasiIso i), (∀ q : ℤ, Injective (K.X q)) → ∀ n : ℕ,
    resolutionModelMap (sectionsValue.{a,u,r} R W) i hi n ≫ (t n).app M =
      HomologicalComplex.homologyMap (((restrictSections.{a} X R j.unop).mapHomologicalComplex
        (.up ℤ)).app K) (n : ℤ) ≫
      (((((sectionsValue.{a,u,r} R V).mapHomologicalComplex (.up ℤ)).obj K).sc
        (n : ℤ)).mapHomologyIso (restrictSectionScalars.{a} X R j.unop)).hom ≫
      (restrictSectionScalars.{a} X R j.unop).map
        (resolutionModelMap (sectionsValue.{a,u,r} R V) i hi n)

/-- The restriction of the original presheaf is the very same restriction
as HA-H01 on the derived section objects, over the original section maps. -/
def originalRestrictionCompatibility : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) [EnoughInjectives (AmbientSheaves.{a} R)],
    ∃ e : ∀ (V : Opens X) (n : ℕ), localCohomology.{u,r,a} R n ⋙
        PresheafOfModules.evaluation R.obj (op V) ≅ cohomologyValue.{a,u,r} R V n,
      (∀ V n (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
        (e V n).hom.app M =
          (localEvaluationIso.{u,r,a} R V J n).hom ≫ sectionModelMap.{u,r,a} R V J n) ∧
      ∀ {W V : Opens X} (j : op W ⟶ op V),
        let H := restrictSectionScalars.{a} X R j.unop
        ∃ t : ∀ n : ℕ, cohomologyValue.{a,u,r} R W n ⟶ cohomologyValue.{a,u,r} R V n ⋙ H,
          IsRestrictionModelComparison.{u,r,a} R j t ∧
          ∀ (M : AmbientSheaves.{a} R) (n : ℕ),
            ((localCohomology.{u,r,a} R n).obj M).map j ≫ H.map ((e V n).hom.app M) =
              (e W n).hom.app M ≫ (t n).app M

end Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechSequenceOriginal
open _root_.AdvancedHomologicalAlgebra.DoubleTotalization

/-- The coefficient augmentation into the signed total is the original
map into the zero row at every nonnegative total degree. -/
def verticalTotalAugmentation : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
    let e := ComplexShape.embeddingUpIntGE 0
    let L := cochainComplex.{u,r,a,v} R c M.val
    let K := doubleComplex.{u,r,a,v} R c J.cocomplex
    let K' := doubleComplexInt.{u,r,a,v} R c J.cocomplex
    ∃ β : L.extend e ⟶ sumTotal K',
      ∀ p : ℕ, β.f (p : ℤ) =
        (L.extendXIso e (by simp [e] : e.f p = (p : ℤ))).hom ≫
          (verticalAugmentation.{u,r,a,v} R c J).f p ≫
          (intBicomplexTermIso K p 0).inv ≫ sumInjection K' (p : ℤ) 0 (p : ℤ) (add_zero _)

end Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients


namespace AdvancedHomologicalAlgebra.CechSequenceOriginal

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable {U : Opens X} {A : Type v} (c : Cover U A)

/-- The raised coefficient augmentation is induced by the transported
degree-zero map of the same injective resolution. -/
def raisedVerticalAugmentation {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    CechToCohomology.cechComplex (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
      ((transport.{a} R).obj M).val ⟶ (raisedDouble.{u,r,a,v} R c J.cocomplex).flip.X 0 :=
  CechToCohomology.cochainComplexMap (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
    ((transport.{a} R).map (J.ι.f 0)).val

end AdvancedHomologicalAlgebra.CechSequenceOriginal

namespace Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechSequenceOriginal
open _root_.AdvancedHomologicalAlgebra.DoubleTotalization
open _root_.AdvancedHomologicalAlgebra.CechToCohomology (natToIntDoubleComplex)

/-- The zero-row map into the signed total respects the original full
tuple comparison, including its degree-zero coefficient augmentation. -/
def verticalSignedTotalTransport : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
    let S := originalScalars.{u,r,a,v} R c
    let h := ComplexShape.embeddingUpIntGE 0
    let K := doubleComplex.{u,r,a,v} R c J.cocomplex
    let L := raisedDouble.{u,r,a,v} R c J.cocomplex
    let P := cochainComplex.{u,r,a,v} R c M.val
    let Q := _root_.AdvancedHomologicalAlgebra.CechToCohomology.cechComplex
      (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ((transport.{a} R).obj M).val
    ∃ (e : natToIntDoubleComplex K ≅ (mapIntDouble S).obj (natToIntDoubleComplex L))
      (t : sumTotal (natToIntDoubleComplex K) ≅
        (S.mapHomologicalComplex (.up ℤ)).obj (sumTotal (natToIntDoubleComplex L)))
      (b : P.extend h ≅ (S.mapHomologicalComplex (.up ℤ)).obj (Q.extend h))
      (α : P.extend h ⟶ sumTotal (natToIntDoubleComplex K))
      (β : Q.extend h ⟶ sumTotal (natToIntDoubleComplex L)),
      (∀ (p q n : ℤ) (hn : p + q = n), sumInjection (natToIntDoubleComplex K) p q n hn ≫ t.hom.f n =
        (e.hom.f p).f q ≫ S.map (sumInjection (natToIntDoubleComplex L) p q n hn)) ∧
      (∀ (p q : ℕ) (x : Cochains R (J.cocomplex.X q).val c p),
        HEq (((intBicomplexTermIso K p q).inv ≫ (e.hom.f (p : ℤ)).f (q : ℤ) ≫
          S.map (intBicomplexTermIso L p q).hom) x)
          (cochainComparison.{u,r,a,v} R (J.cocomplex.X q) c p x)) ∧
      (∀ (p : ℕ) (x : Cochains R M.val c p),
        let hp : h.f p = (p : ℤ) := by simp [h]
        HEq ((((P.extendXIso h hp).inv ≫ b.hom.f (p : ℤ)) ≫ S.map (Q.extendXIso h hp).hom) x)
          (cochainComparison.{u,r,a,v} R M c p x)) ∧
      (∀ p : ℕ, α.f (p : ℤ) =
        (P.extendXIso h (by simp [h] : h.f p = (p : ℤ))).hom ≫
          (verticalAugmentation.{u,r,a,v} R c J).f p ≫
          (intBicomplexTermIso K p 0).inv ≫
          sumInjection (natToIntDoubleComplex K) (p : ℤ) 0 (p : ℤ) (add_zero _)) ∧
      (∀ p : ℕ, β.f (p : ℤ) =
        (Q.extendXIso h (by simp [h] : h.f p = (p : ℤ))).hom ≫
          (raisedVerticalAugmentation.{u,r,a,v} R c J).f p ≫
          (intBicomplexTermIso L p 0).inv ≫
          sumInjection (natToIntDoubleComplex L) (p : ℤ) 0 (p : ℤ) (add_zero _)) ∧
      α ≫ t.hom = b.hom ≫ (S.mapHomologicalComplex (.up ℤ)).map β

end Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechSequenceOriginal
open _root_.AdvancedHomologicalAlgebra.DoubleTotalization
open _root_.AdvancedHomologicalAlgebra.DoubleComplexFirstPages (page)
open _root_.AdvancedHomologicalAlgebra.FilteredPage (almost toPage)
open _root_.AdvancedHomologicalAlgebra.CechToCohomology (CechSpectralSequence resolutionDoubleComplex
  resolutionDoubleComplexInt)

set_option maxHeartbeats 1500000 in
/-- The same filtered scalar comparison carries the normalized HA-B03 second
page to the comparison on the original alternating local-cohomology complex. -/
def secondPageCarrierTransport : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v}
    (c : Cover U A) [EnoughInjectives (AmbientSheaves.{a} R)],
    let R' := liftedRing.{a} R
    let c' := liftCover.{u,a,r,v} c
    let T := transport.{a} R
    let P := transportPresheaf.{a} R
    let S := originalScalars.{u,r,a,v} R c
    let G := _root_.AdvancedHomologicalAlgebra.CechToCohomology.cochainFunctor R' c'
    ∃ (hT : T.IsEquivalence) (hP : P.IsEquivalence),
    letI := hT
    letI := hP
    ∃ (D : NaturalityData.{u,r,a,v} R c)
      (E : CechSpectralSequence R' c')
      (g : cochainFunctor.{u,r,a,v} R c ≅ P ⋙ G ⋙ S.mapHomologicalComplex (.up ℕ)),
      (∀ (F : AmbientPresheaves.{a} R) (p : ℕ) (s : Cochains R F c p)
          (j : Fin (p + 1) → A),
        ((g.hom.app F).f p s) j =
          presheafSectionAt.{u,r,a} R F _ _ (liftCover_tuple.{u,r,a,v} c j) (s j)) ∧
      ∀ (M : AmbientSheaves.{a} R) (J : InjectiveResolution M),
        let J' := raisedResolution.{u,r,a} R J
        let M' := T.obj M
        let K := doubleComplexInt.{u,r,a,v} R c J.cocomplex
        let K' := resolutionDoubleComplexInt R' c' M' J'
        let d := D.data J
        let d' := E.data M' J'
        ∃ (e : K ≅ (mapIntDouble S).obj K')
          (t : sumTotal K ≅ (S.mapHomologicalComplex (.up ℤ)).obj (sumTotal K')),
          (∀ (p q : ℕ) (x : Cochains R (J.cocomplex.X q).val c p),
            HEq (((intBicomplexTermIso (doubleComplex.{u,r,a,v} R c J.cocomplex) p q).inv ≫
              (e.hom.f (p : ℤ)).f (q : ℤ) ≫ S.map
                (intBicomplexTermIso (resolutionDoubleComplex R' c' M' J') p q).hom) x)
              (cochainComparison.{u,r,a,v} R (J.cocomplex.X q) c p x)) ∧
          (∀ (p q n : ℤ) (h : p + q = n),
            sumInjection K p q n h ≫ t.hom.f n =
              (e.hom.f p).f q ≫ S.map (sumInjection K' p q n h)) ∧
          ∀ p q : ℕ,
            let n := (p : ℤ) + (q : ℤ)
            let yc := _root_.AdvancedHomologicalAlgebra.CechToCohomology.cechComplex R' c'
              ((_root_.AdvancedHomologicalAlgebra.CechToCohomology.localCohomology R' q).obj M')
            ∃ (z : (almost d.filtration 2 (p : ℤ) n : CochainModules.{u,r,a,v} R (U := U)) ≅
                S.obj (almost d'.filtration 2 (p : ℤ) n : ModuleCat.{max a u r v}
                  (sectionRing R' ((opensEquiv.{max a u r} X).symm U))))
              (w : page d.filtration d.pages 2 (p : ℤ) (q : ℤ) ≅
                S.obj (page d'.filtration d'.pages 2 (p : ℤ) (q : ℤ))),
              z.hom ≫ S.map (almost d'.filtration 2 (p : ℤ) n).arrow =
                (almost d.filtration 2 (p : ℤ) n).arrow ≫ t.hom.f n ∧
              toPage d.filtration 2 (p : ℤ) n (d.pages.containment 2 (p : ℤ) n) ≫ w.hom =
                z.hom ≫ S.map (toPage d'.filtration 2 (p : ℤ) n (d'.pages.containment 2 (p : ℤ) n)) ∧
              w.hom ≫ S.map (E.second M' J' p q).hom =
                (secondPageComparison.{u,r,a,v} R c J d (D.vertical J) p q).hom ≫
                  (HomologicalComplex.homologyMapIso (localModelCochainIso.{u,r,a,v} R c J q g) p ≪≫
                    (yc.sc p).mapHomologyIso S).hom

end Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

namespace AdvancedHomologicalAlgebra.CechSequenceOriginal

open HomologicalComplex
universe b c₁ c₂
variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable {U : Opens X} {A : Type v} (c : Cover U A)

/-- Raise coefficient carriers on the same ringed space. -/
abbrev sheafCarrierLift :=
  liftSheafCoefficients.{b,u,r,max a u r} R

abbrev presheafCarrierLift := liftCoefficients.{b,u,r,max a u r} R.obj

abbrev cochainCarrierLift (_ : Cover U A) :=
  ModuleCat.uliftFunctor.{b,max a u r v} (sectionRing R U)

set_option quotPrecheck false in
set_option hygiene false in
local notation "L" => sheafCarrierLift.{u,r,a,b} R

abbrev liftSheafComplex (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :=
  ((L).mapHomologicalComplex (.up ℕ)).obj K

/-- Apply the exact coefficient lift to the terms and coaugmentation of a resolution. -/
def carrierLiftResolution [(L).PreservesHomology] [(L).PreservesInjectiveObjects]
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    InjectiveResolution ((L).obj M) where
  cocomplex := ((L).mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  injective n := (L).injective_obj (J.cocomplex.X n)
  ι := (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
    ((L).mapHomologicalComplex (.up ℕ)).map J.ι
  quasiIso := by
    let _ := HomologicalComplex.quasiIso_map_of_preservesHomology J.ι L
    infer_instance

/-- The individually adequate category for the original coefficient. -/
abbrev nativeCoefficient (M : SheafOfModules.{a} R) : AmbientSheaves.{a} R :=
  (liftSheafCoefficients.{max u r,u,r,a} R).obj M

/-- Identify the iterated lift of the original sections with the direct common lift. -/
def flattenNativeCoefficient (M : SheafOfModules.{a} R) :
    (sheafCarrierLift.{u,r,a,b} R).obj (nativeCoefficient.{u,r,a} R M) ≅
      (liftSheafCoefficients.{max a b u r,u,r,a} R).obj M :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun V ↦
        ({ toFun := fun x ↦ ULift.up x.down.down
           invFun := fun x ↦ ULift.up (ULift.up x.down)
           left_inv := fun _ ↦ rfl
           right_inv := fun _ ↦ rfl
           map_add' := fun _ _ ↦ rfl
           map_smul' := fun _ _ ↦ rfl } :
          ((sheafCarrierLift.{u,r,a,b} R).obj (nativeCoefficient.{u,r,a} R M)).val.obj V ≃ₗ[R.obj.obj V]
            ((liftSheafCoefficients.{max a b u r,u,r,a} R).obj M).val.obj V).toModuleIso)
      (by intros; ext x; rfl))

/-- The original sectionwise coefficient map acting between the lifted
native models over the same section rings. -/
def mixedCoefficientMap {M : SheafOfModules.{a} R} {N : SheafOfModules.{b} R}
    (f : SectionwiseHom M N) :
    (sheafCarrierLift.{u,r,a,b} R).obj (nativeCoefficient.{u,r,a} R M) ⟶
      (sheafCarrierLift.{u,r,b,a} R).obj (nativeCoefficient.{u,r,b} R N) :=
  (flattenNativeCoefficient.{u,r,a,b} R M).hom ≫ f.lift.{max u r} ≫
    (flattenNativeCoefficient.{u,r,b,a} R N).inv

/-- Return a linear map of lifted section modules to the original carriers. -/
def originalCarrierMap {S : Type r} [Ring S] {M : ModuleCat.{a} S} {N : ModuleCat.{b} S}
    (f : ULift.{c₁} M →ₗ[S] ULift.{c₂} N) : M →ₗ[S] N :=
  ULift.moduleEquiv.toLinearMap.comp (f.comp ULift.moduleEquiv.symm.toLinearMap)

end AdvancedHomologicalAlgebra.CechSequenceOriginal

namespace Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra
open _root_.AdvancedHomologicalAlgebra.CechSequenceOriginal
open _root_.AdvancedHomologicalAlgebra.DoubleTotalization
open _root_.AdvancedHomologicalAlgebra.FilteredPage (almost toPage)
open _root_.AdvancedHomologicalAlgebra.PageCohomology (object)
open _root_.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence (closed Stabilized)
open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients (cohomologyValue)
open _root_.AdvancedHomologicalAlgebra.CechToCohomology (abutmentPiece abutmentPieceMap
  abutmentGradedMap abutmentPiece_decreasing)
open HomologicalComplex

universe b
variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable {U : Opens X} {A : Type v} (c : Cover U A)
variable [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]

set_option quotPrecheck false in
set_option hygiene false in
local notation "L" => sheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "P" => presheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cochainCarrierLift.{u,r,a,v,b} R c

/-- Data for enlarging the carriers of one actual augmented model over the
unchanged section ring and cover. -/
structure CarrierModelComparison
    [(L).PreservesInjectiveObjects] [(L).PreservesHomology] [(P).PreservesHomology]
    (D : NaturalityData.{u,r,a,v} R c) (E : NaturalityData.{u,r,max a b,v} R c)
    {M : AmbientSheaves.{a} R} (I : InjectiveResolution M) where
  double : let I' := carrierLiftResolution.{u,r,a,b} R I
    doubleComplexInt.{u,r,max a b,v} R c I'.cocomplex ≅
      (mapIntDouble (S)).obj (doubleComplexInt.{u,r,a,v} R c I.cocomplex)
  double_formula : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ (p q : ℕ) (s : Cochains R (I'.cocomplex.X q).val c p),
      ((intBicomplexTermIso (doubleComplex.{u,r,max a b,v} R c I'.cocomplex) p q).inv ≫
        (double.hom.f (p : ℤ)).f (q : ℤ) ≫
        (S).map (intBicomplexTermIso (doubleComplex.{u,r,a,v} R c I.cocomplex) p q).hom) s =
        ULift.up (fun t ↦ (s t).down)
  total : let I' := carrierLiftResolution.{u,r,a,b} R I
    sumTotal (doubleComplexInt.{u,r,max a b,v} R c I'.cocomplex) ≅
      ((S).mapHomologicalComplex (.up ℤ)).obj (sumTotal (doubleComplexInt.{u,r,a,v} R c I.cocomplex))
  total_formula : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ (p q n : ℤ) (h : p + q = n),
      sumInjection (doubleComplexInt.{u,r,max a b,v} R c I'.cocomplex) p q n h ≫ total.hom.f n =
        (double.hom.f p).f q ≫ (S).map (sumInjection (doubleComplexInt.{u,r,a,v} R c I.cocomplex) p q n h)
  filtration : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ p n : ℤ,
      Subobject.mk (((E.data I').filtration.piece p n).arrow ≫ total.hom.f n) =
        Subobject.mk ((S).map ((D.data I).filtration.piece p n).arrow)
  sections : let I' := carrierLiftResolution.{u,r,a,b} R I
    intSections.{u,r,max a b,v} R c I'.cocomplex ≅
      ((S).mapHomologicalComplex (.up ℤ)).obj (intSections.{u,r,a,v} R c I.cocomplex)
  augmentation : let I' := carrierLiftResolution.{u,r,a,b} R I
    E.augmentation I' ≫ total.hom =
      sections.hom ≫ ((S).mapHomologicalComplex (.up ℤ)).map (D.augmentation I)
  localPresheaf : ∀ q : ℕ, (P).obj ((localCohomology.{u,r,a} R q).obj M) ≅
    (localCohomology.{u,r,max a b} R q).obj ((L).obj M)
  local_formula : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ q : ℕ, (localPresheaf q).hom =
      (P).map (I.isoRightDerivedObj (SheafOfModules.forget R) q).hom ≫
      (((underlyingComplex.{u,r,a} R I.cocomplex).sc q).mapHomologyIso (P)).inv ≫
      (I'.isoRightDerivedObj (SheafOfModules.forget R) q).inv
  localTuples : ∀ (F : AmbientPresheaves.{a} R),
    cochainComplex.{u,r,max a b,v} R c ((P).obj F) ≅
      ((S).mapHomologicalComplex (.up ℕ)).obj (cochainComplex.{u,r,a,v} R c F)
  localTuples_formula : ∀ (F : AmbientPresheaves.{a} R) (p : ℕ)
    (s : Cochains R ((P).obj F) c p), (localTuples F).hom.f p s = ULift.up (fun t ↦ (s t).down)
  verticalAugmentation_formula : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∃ e : doubleComplex.{u,r,max a b,v} R c I'.cocomplex ≅
      (mapDouble (S)).obj (doubleComplex.{u,r,a,v} R c I.cocomplex),
      (∀ (p q : ℕ) (s : Cochains R (I'.cocomplex.X q).val c p),
        (e.hom.f p).f q s = ULift.up (fun t ↦ (s t).down)) ∧
      verticalAugmentation.{u,r,max a b,v} R c I' ≫
        ((HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map e.hom).f 0 =
        (localTuples M.val).hom ≫
          ((S).mapHomologicalComplex (.up ℕ)).map (verticalAugmentation.{u,r,a,v} R c I)
  pages : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ (r : ℤ) (_ : 1 ≤ r) (p n : ℤ),
      object (E.data I').filtration (E.data I').pages r p n ≅
        (S).obj (object (D.data I).filtration (D.data I).pages r p n)
  representatives : let I' := carrierLiftResolution.{u,r,a,b} R I
    let d := D.data I
    let e := E.data I'
    ∀ (r : ℤ) (hr : 1 ≤ r) (p n : ℤ),
      ∃ z : (almost e.filtration r p n : CochainModules.{u,r,max a b,v} R (U := U)) ≅
          (S).obj (almost d.filtration r p n : CochainModules.{u,r,a,v} R (U := U)),
        z.hom ≫ (S).map (almost d.filtration r p n).arrow =
          (almost e.filtration r p n).arrow ≫ total.hom.f n ∧
        toPage e.filtration r p n (e.pages.containment r p n) ≫ (pages r hr p n).hom =
          z.hom ≫ (S).map (toPage d.filtration r p n (d.pages.containment r p n))
  differential : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ (r : ℤ) (hr : 1 ≤ r) (p n : ℤ),
      (E.data I').pages.differential r (by omega) p n ≫ (pages r hr (p+r) (n+1)).hom =
        (pages r hr p n).hom ≫ (S).map ((D.data I).pages.differential r (by omega) p n)
  second : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ p q : ℕ,
      let K := cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)
      let g := (cochainFunctor.{u,r,max a b,v} R c).mapIso (localPresheaf q).symm ≪≫ localTuples _
      (pages 2 (by omega) (p : ℤ) ((p : ℤ) + (q : ℤ))).hom ≫
        (S).map (secondPageComparison.{u,r,a,v} R c I (D.data I) (D.vertical I) p q).hom =
      (secondPageComparison.{u,r,max a b,v} R c I' (E.data I') (E.vertical I') p q).hom ≫
        (homologyMapIso g p ≪≫ (K.sc p).mapHomologyIso (S)).hom
  sectionComparison : ∀ (V : Opens X) (n : ℕ),
    (cohomologyValue.{max a b,u,r} R V n).obj ((L).obj M) ≅
      (ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R V)).obj
        ((cohomologyValue.{a,u,r} R V n).obj M)
  section_model : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ (V : Opens X) (n : ℕ),
      let H := ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R V)
      let K := sectionComplex.{u,r,a} R V I.cocomplex
      sectionModelMap.{u,r,max a b} R V I' n ≫ (sectionComparison V n).hom =
        ((K.sc n).mapHomologyIso H).hom ≫ H.map (sectionModelMap.{u,r,a} R V I n)
  local_sections : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ (V : Opens X) (n : ℕ),
      let H := ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R V)
      let B := PresheafOfModules.evaluation.{max a b u r} R.obj (op V)
      B.map (localPresheaf n).inv ≫
          H.map ((localEvaluationIso.{u,r,a} R V I n).hom ≫ sectionModelMap.{u,r,a} R V I n) =
        (localEvaluationIso.{u,r,max a b} R V I' n).hom ≫
          sectionModelMap.{u,r,max a b} R V I' n ≫ (sectionComparison V n).hom
  target : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ n : ℕ,
      (sectionLift.{u,r,max a b,v} R c).obj ((cohomologyValue.{max a b,u,r} R U n).obj ((L).obj M)) ≅
        (S).obj ((sectionLift.{u,r,a,v} R c).obj ((cohomologyValue.{a,u,r} R U n).obj M))
  target_sections : ∀ (n : ℕ) (x : (cohomologyValue.{max a b,u,r} R U n).obj ((L).obj M)),
    (target n).hom (ULift.up x) = ULift.up (ULift.up ((sectionComparison U n).hom x).down)
  target_formula : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ n : ℕ,
      let K := sumTotal (doubleComplexInt.{u,r,a,v} R c I.cocomplex)
      (homologyMapIso total (n : ℤ) ≪≫ (K.sc (n : ℤ)).mapHomologyIso (S)).hom ≫
        (S).map (D.abutment I n).hom = (E.abutment I' n).hom ≫ (target n).hom
  limits : let I' := carrierLiftResolution.{u,r,a,b} R I
    comparesLimits (S) (E.data I').filtration (D.data I).filtration (E.data I').pages (D.data I).pages total
  limit_pages : let I' := carrierLiftResolution.{u,r,a,b} R I
    ∀ (n : ℕ) (p : ℤ),
      ∃ g : limitQuotient (E.data I').filtration (n : ℤ) (E.abutment I' n) p ≅
          (S).obj (limitQuotient (D.data I).filtration (n : ℤ) (D.abutment I n) p),
        (∃ z : (closed (E.data I').filtration p (n : ℤ) :
            CochainModules.{u,r,max a b,v} R (U := U)) ≅
              (S).obj (closed (D.data I).filtration p (n : ℤ) :
                CochainModules.{u,r,a,v} R (U := U)),
          z.hom ≫ (S).map (closed (D.data I).filtration p (n : ℤ)).arrow =
            (closed (E.data I').filtration p (n : ℤ)).arrow ≫ total.hom.f (n : ℤ) ∧
          limitClass (E.data I').filtration (n : ℤ) (E.abutment I' n) p ≫ g.hom =
            z.hom ≫ (S).map (limitClass (D.data I).filtration (n : ℤ) (D.abutment I n) p)) ∧
        ∀ (r : ℤ) (hr : 1 ≤ r)
          (hs : Stabilized (E.data I').filtration r p (n : ℤ))
          (ht : Stabilized (D.data I).filtration r p (n : ℤ)),
          (pages r hr p (n : ℤ)).hom ≫ (S).map (D.limit I n r p ht).hom =
            (E.limit I' n r p hs).hom ≫ g.hom

/-- Change of coefficient size on every chosen native augmented resolution. -/
def coefficientSizeTransport : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v} (c : Cover U A)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)],
    let Lift := sheafCarrierLift.{u,r,a,b} R
    let PLift := presheafCarrierLift.{u,r,a,b} R
    ∃ (i : Lift.PreservesInjectiveObjects) (hL : Lift.PreservesHomology) (hP : PLift.PreservesHomology),
    letI := i
    letI := hL
    letI := hP
    ∃ (D : NaturalityData.{u,r,a,v} R c) (E : NaturalityData.{u,r,max a b,v} R c),
      ∀ {M : AmbientSheaves.{a} R} (I : InjectiveResolution M),
        Nonempty (CarrierModelComparison.{u,r,a,v,b} R c D E I)

end Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra
open _root_.AdvancedHomologicalAlgebra.CechSequenceOriginal
open _root_.AdvancedHomologicalAlgebra.PageCohomology (object)
open _root_.AdvancedHomologicalAlgebra.CechToCohomology (abutmentPiece abutmentPieceMap abutmentGradedMap)
open _root_.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence (Stabilized)
open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients (cohomologyValue)
open HomologicalComplex

universe b
variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable {U : Opens X} {A : Type v} (c : Cover U A)

set_option maxHeartbeats 2200000 in
/-- The given coefficient map acts on the pages of each native resolution,
the second-page Čech cohomology, and the filtered derived section modules. -/
def mixedCoefficientNaturality : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {A : Type v} (c : Cover U A)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{b} R)]
    [EnoughInjectives (AmbientSheaves.{max a b} R)],
    let L₁ := sheafCarrierLift.{u,r,a,b} R
    let L₂ := sheafCarrierLift.{u,r,b,a} R
    let P₁ := presheafCarrierLift.{u,r,a,b} R
    let P₂ := presheafCarrierLift.{u,r,b,a} R
    let S₁ := cochainCarrierLift.{u,r,a,v,b} R c
    let S₂ := cochainCarrierLift.{u,r,b,v,a} R c
    ∃ (i₁ : L₁.PreservesInjectiveObjects) (i₂ : L₂.PreservesInjectiveObjects)
      (h₁ : L₁.PreservesHomology) (h₂ : L₂.PreservesHomology)
      (k₁ : P₁.PreservesHomology) (k₂ : P₂.PreservesHomology),
    letI := i₁
    letI := i₂
    letI := h₁
    letI := h₂
    letI := k₁
    letI := k₂
    ∃ (D₁ : NaturalityData.{u,r,a,v} R c) (D₂ : NaturalityData.{u,r,b,v} R c)
      (D : NaturalityData.{u,r,max a b,v} R c),
    ∀ {M : SheafOfModules.{a} R} {N : SheafOfModules.{b} R} (f : SectionwiseHom M N)
      (I : InjectiveResolution (nativeCoefficient.{u,r,a} R M))
      (J : InjectiveResolution (nativeCoefficient.{u,r,b} R N)),
      let I' := carrierLiftResolution.{u,r,a,b} R I
      let J' := carrierLiftResolution.{u,r,b,a} R J
      let f' := mixedCoefficientMap.{u,r,a,b} R f
      let U₁ (n : ℕ) := (sectionLift.{u,r,a,v} R c).obj
        ((cohomologyValue.{a,u,r} R U n).obj (nativeCoefficient.{u,r,a} R M))
      let U₂ (n : ℕ) := (sectionLift.{u,r,b,v} R c).obj
        ((cohomologyValue.{b,u,r} R U n).obj (nativeCoefficient.{u,r,b} R N))
      let E₁ (r p n : ℤ) := object (D₁.data I).filtration (D₁.data I).pages r p n
      let E₂ (r p n : ℤ) := object (D₂.data J).filtration (D₂.data J).pages r p n
      let F₁ (n : ℕ) (p : ℤ) := abutmentPiece (D₁.data I).filtration (n : ℤ) (D₁.abutment I n) p
      let F₂ (n : ℕ) (p : ℤ) := abutmentPiece (D₂.data J).filtration (n : ℤ) (D₂.abutment J n) p
      let C₁ (p q : ℕ) := (localCechCohomology.{u,r,a,v} R c p q).obj (nativeCoefficient.{u,r,a} R M)
      let C₂ (p q : ℕ) := (localCechCohomology.{u,r,b,v} R c p q).obj (nativeCoefficient.{u,r,b} R N)
      ∃ (A₁ : CarrierModelComparison.{u,r,a,v,b} R c D₁ D I)
        (A₂ : CarrierModelComparison.{u,r,b,v,a} R c D₂ D J)
        (step₁ : ∀ (n : ℕ) (p : ℤ), (abutmentPiece (D.data I').filtration (n : ℤ)
          (D.abutment I' n) p : CochainModules.{u,r,max a b,v} R (U := U)) ≅
            S₁.obj (F₁ n p : CochainModules.{u,r,a,v} R (U := U)))
        (step₂ : ∀ (n : ℕ) (p : ℤ), (abutmentPiece (D.data J').filtration (n : ℤ)
          (D.abutment J' n) p : CochainModules.{u,r,max a b,v} R (U := U)) ≅
            S₂.obj (F₂ n p : CochainModules.{u,r,b,v} R (U := U))),
      ∃ (pageMap : ∀ (r : ℤ) (_ : 2 ≤ r) (p n : ℤ), E₁ r p n →ₗ[sectionRing R U] E₂ r p n)
        (localMap : ∀ (p q : ℕ), C₁ p q →ₗ[sectionRing R U] C₂ p q)
        (targetMap : ∀ n : ℕ, U₁ n →ₗ[sectionRing R U] U₂ n)
        (stepMap : ∀ (n : ℕ) (p : ℤ),
          (F₁ n p : CochainModules.{u,r,a,v} R (U := U)) →ₗ[sectionRing R U]
          (F₂ n p : CochainModules.{u,r,b,v} R (U := U))),
        (∀ (p : ℕ) (s : Cochains R M.val c p) (t : Fin (p+1) → A),
          ((cochainMap.{u,r,max a b,v} R c f'.val).f p
            (fun k ↦ ULift.up (ULift.up (s k)))) t =
              ULift.up (ULift.up (f.app (op (tupleOpen c t)) (s t)))) ∧
        (∀ (n : ℕ) (p : ℤ),
          (step₁ n p).hom ≫ S₁.map (F₁ n p).arrow =
            (abutmentPiece (D.data I').filtration (n : ℤ) (D.abutment I' n) p).arrow ≫ (A₁.target n).hom ∧
          (step₂ n p).hom ≫ S₂.map (F₂ n p).arrow =
            (abutmentPiece (D.data J').filtration (n : ℤ) (D.abutment J' n) p).arrow ≫ (A₂.target n).hom) ∧
        (∀ (n : ℕ) (x : U₁ n),
          (((A₁.target n).inv ≫ (sectionLift.{u,r,max a b,v} R c).map
              ((cohomologyValue.{max a b,u,r} R U n).map f') ≫ (A₂.target n).hom) (ULift.up x)) =
            ULift.up (targetMap n x)) ∧
        (∀ (p q : ℕ),
          let iso₁ := HomologicalComplex.homologyMapIso
            ((cochainFunctor.{u,r,max a b,v} R c).mapIso (A₁.localPresheaf q).symm ≪≫ A₁.localTuples _) p ≪≫
            ((cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj
              (nativeCoefficient.{u,r,a} R M))).sc p).mapHomologyIso S₁
          let iso₂ := HomologicalComplex.homologyMapIso
            ((cochainFunctor.{u,r,max a b,v} R c).mapIso (A₂.localPresheaf q).symm ≪≫ A₂.localTuples _) p ≪≫
            ((cochainComplex.{u,r,b,v} R c ((localCohomology.{u,r,b} R q).obj
              (nativeCoefficient.{u,r,b} R N))).sc p).mapHomologyIso S₂
          ∀ x : C₁ p q, (iso₁.inv ≫ (localCechCohomology.{u,r,max a b,v} R c p q).map f' ≫
              iso₂.hom) (ULift.up x) = ULift.up (localMap p q x)) ∧
        (∀ (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) (x : E₁ r p n),
          (D₂.data J).pages.differential r (by omega) p n (pageMap r hr p n x) =
            pageMap r hr (p+r) (n+1) ((D₁.data I).pages.differential r (by omega) p n x)) ∧
        (∀ (p q : ℕ) (x : E₁ 2 (p : ℤ) ((p : ℤ) + (q : ℤ))),
          let τ₁ := secondPageComparison.{u,r,a,v} R c I (D₁.data I) (D₁.vertical I) p q
          let τ₂ := secondPageComparison.{u,r,b,v} R c J (D₂.data J) (D₂.vertical J) p q
          τ₂.hom (pageMap 2 (by omega) (p : ℤ) ((p : ℤ) + (q : ℤ)) x) = localMap p q (τ₁.hom x)) ∧
        (∀ (n : ℕ) (p : ℤ) (x : (F₁ n p : CochainModules.{u,r,a,v} R (U := U))),
          (F₂ n p).arrow (stepMap n p x) = targetMap n ((F₁ n p).arrow x)) ∧
        ∀ (φ : I'.cocomplex ⟶ J'.cocomplex)
          (_ : I'.ι.f 0 ≫ φ.f 0 = f' ≫ J'.ι.f 0),
          (∀ (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) (x : E₁ r p n),
            ((A₁.pages r (by omega) p n).inv ≫ (D.pageMap I' J' φ).map r p n ≫
                (A₂.pages r (by omega) p n).hom) (ULift.up x) =
              ULift.up (pageMap r hr p n x)) ∧
          (∀ (n : ℕ) (p : ℤ) (x : (F₁ n p : CochainModules.{u,r,a,v} R (U := U))),
            ((step₁ n p).inv ≫
                abutmentPieceMap (D.filteredMap I' J' φ) (n : ℤ) (D.abutment I' n) (D.abutment J' n) p ≫
                  (step₂ n p).hom) (ULift.up x) = ULift.up (stepMap n p x)) ∧
          (∀ (n : ℕ) (r p : ℤ)
            (hs : Stabilized (D.data I').filtration r p (n : ℤ))
            (ht : Stabilized (D.data J').filtration r p (n : ℤ)),
            (D.pageMap I' J' φ).map r p (n : ℤ) ≫ (D.limit J' n r p ht).hom =
              (D.limit I' n r p hs).hom ≫
                abutmentGradedMap (D.filteredMap I' J' φ) (n : ℤ) (D.abutment I' n) (D.abutment J' n) p)

end Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
