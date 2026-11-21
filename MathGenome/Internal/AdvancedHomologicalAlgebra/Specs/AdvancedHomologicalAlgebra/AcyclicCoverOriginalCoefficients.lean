import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.EdgesAndFiveTerms

/-! HA-H04 on the original full ordered cochains and over the original section ring. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AdvancedHomologicalAlgebra.Cech
open AdvancedHomologicalAlgebra.SheafTheory (sectionRing)
open AdvancedHomologicalAlgebra.CechSequenceOriginal
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.DoubleTotalization
open AdvancedHomologicalAlgebra.EdgesAndFiveTerms
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (coefficientCohomologyValue cohomologyValue IndividualCohomologyComparison
    IsIndividualCohomologyComparison)
open Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
  (CarrierModelComparison NaturalityData)

universe a u r v b

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3500
set_option maxHeartbeats 2000000

namespace AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X}
  {T : Type v} (c : Cover U T)

abbrev embedding := ComplexShape.embeddingUpIntGE 0

abbrev rawCochainLift (_ : Cover U T) :=
  ModuleCat.uliftFunctor.{max u r,max a v} (sectionRing R U)

abbrev rawComplexFunctor : SheafOfModules.{a} R ⥤
    CochainComplex (ModuleCat.{max a v} (sectionRing R U)) ℕ :=
  SheafOfModules.forget R ⋙ orderedCochainFunctor.{u,r,a,v} R c

abbrev liftedComplexFunctor :=
  rawComplexFunctor.{a,u,r,v} R c ⋙
    (rawCochainLift.{a,u,r,v} R c).mapHomologicalComplex (.up ℕ)

abbrev liftedRawCochainComplex (F : SheafOfModules.{a} R) :=
  (liftedComplexFunctor.{a,u,r,v} R c).obj F

abbrev sourceCohomology (n : ℕ) :
    SheafOfModules.{a} R ⥤ CochainModules.{u,r,a,v} R (U := U) :=
  rawComplexFunctor.{a,u,r,v} R c ⋙ homologyFunctor _ (.up ℕ) n ⋙
    rawCochainLift.{a,u,r,v} R c

/-- The canonical identification for the exact carrier lift and zero extension. -/
def sourceModel (F : SheafOfModules.{a} R) (n : ℕ) :
    ((liftedRawCochainComplex.{a,u,r,v} R c F).extend embedding).homology (n : ℤ) ≅
      (sourceCohomology.{a,u,r,v} R c n).obj F :=
  (liftedRawCochainComplex.{a,u,r,v} R c F).extendHomologyIso embedding
    (j := n) (j' := (n : ℤ)) (by simp [embedding]) ≪≫
  (((rawComplexFunctor.{a,u,r,v} R c).obj F).sc n).mapHomologyIso
    (rawCochainLift.{a,u,r,v} R c)

/-- The identification of the lifted original product with the product of lifted sections. -/
structure CoefficientComparison where
  iso : orderedCochainFunctor.{u,r,a,v} R c ⋙
        (rawCochainLift.{a,u,r,v} R c).mapHomologicalComplex (.up ℕ) ≅
      liftCoefficients.{max u r,u,r,a} R.obj ⋙ cochainFunctor.{u,r,a,v} R c
  coordinate (F : PresheafOfModules.{a} R.obj) (p : ℕ)
      (s : Cochains R F c p) (t : Fin (p + 1) → T) :
    ((iso.hom.app F).f p (ULift.up s)) t = ULift.up.{max u r} (s t)

variable [EnoughInjectives (AmbientSheaves.{a} R)]

abbrev originalSectionCohomology (n : ℕ) :=
  coefficientCohomologyValue.{a,u,r} X R U n ⋙ sectionLift.{u,r,a,v} R c

/-- The comparison as a linear map on the given cohomology carriers. -/
def originalComparisonMap (n : ℕ)
    (η : sourceCohomology.{a,u,r,v} R c n ⟶ originalSectionCohomology.{a,u,r,v} R c n)
    (F : SheafOfModules.{a} R) :
    ((rawComplexFunctor.{a,u,r,v} R c).obj F).homology n →ₗ[sectionRing R U]
      (coefficientCohomologyValue.{a,u,r} X R U n).obj F :=
  ULift.moduleEquiv.toLinearMap.comp ((η.app F).hom.comp ULift.moduleEquiv.symm.toLinearMap)

/-- Vanishing on every actual ordered tuple intersection, in positive degree. -/
def AcyclicOnIntersections (F : SheafOfModules.{a} R) : Prop :=
  ∀ (p : ℕ) (t : Fin (p + 1) → T) (q : ℕ), 0 < q →
    IsZero ((coefficientCohomologyValue.{a,u,r} X R (tupleOpen c t) q).obj F)

/-- The ordinary degree-zero identification is the right-derived unit. -/
def degreeZeroMap (e : CoefficientComparison.{a,u,r,v} R c) (F : SheafOfModules.{a} R) :
    liftedRawCochainComplex.{a,u,r,v} R c F ⟶
      cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R 0).obj
        (nativeCoefficient.{u,r,a} R F)) :=
  e.iso.hom.app F.val ≫ (cochainFunctor.{u,r,a,v} R c).map
    ((SheafOfModules.forget.{max a u r} R).toRightDerivedZero.app (nativeCoefficient.{u,r,a} R F))

/-- The total map is the coefficient augmentation into the original zero row. -/
def IsVerticalAugmentation (e : CoefficientComparison.{a,u,r,v} R c)
    (F : SheafOfModules.{a} R) (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F))
    (β : (liftedRawCochainComplex.{a,u,r,v} R c F).extend embedding ⟶
      sumTotal (doubleComplexInt.{u,r,a,v} R c I.cocomplex)) : Prop :=
  ∀ p : ℕ, β.f (p : ℤ) =
    ((liftedRawCochainComplex.{a,u,r,v} R c F).extendXIso embedding
      (by simp [embedding] : embedding.f p = (p : ℤ))).hom ≫
    (e.iso.hom.app F.val).f p ≫ (verticalAugmentation.{u,r,a,v} R c I).f p ≫
    (intBicomplexTermIso (doubleComplex.{u,r,a,v} R c I.cocomplex) p 0).inv ≫
    sumInjection (doubleComplexInt.{u,r,a,v} R c I.cocomplex) (p : ℤ) 0 (p : ℤ) (add_zero _)

/-- Both augmentation formulas and the row edge use the same normalized model. -/
def AgreesWithModel
    (D : Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.NaturalityData.{u,r,a,v} R c)
    (e : CoefficientComparison.{a,u,r,v} R c)
    (η : ∀ n, sourceCohomology.{a,u,r,v} R c n ⟶ originalSectionCohomology.{a,u,r,v} R c n)
    (F : SheafOfModules.{a} R) (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F))
    (β : (liftedRawCochainComplex.{a,u,r,v} R c F).extend embedding ⟶
      sumTotal (doubleComplexInt.{u,r,a,v} R c I.cocomplex)) : Prop :=
  let P := D.data I
  (∀ n : ℕ,
    letI := D.augmentation_quasiIso I
    letI : IsIso (homologyMap (D.augmentation I) (n : ℤ)) := inferInstance
    (η n).app F = (sourceModel.{a,u,r,v} R c F n).inv ≫ homologyMap β (n : ℤ) ≫
      inv (homologyMap (D.augmentation I) (n : ℤ)) ≫ liftedSectionModelMap.{u,r,a,v} R c I n) ∧
  Nonempty (EdgeData P.filtration P.pages) ∧
  ∀ (E : EdgeData P.filtration P.pages) (n : ℕ),
    let K := liftedRawCochainComplex.{a,u,r,v} R c F
    (sourceModel.{a,u,r,v} R c F n).inv ≫
      (K.extendHomologyIso embedding (j := n) (j' := (n : ℤ)) (by simp [embedding])).hom ≫
      homologyMap (degreeZeroMap R c e F) n ≫
      (secondPageComparison.{u,r,a,v} R c I P (D.vertical I) n 0).inv ≫
      eqToHom (congrArg (PageCohomology.object P.filtration P.pages 2 (n : ℤ)) (add_zero _)) ≫
      E.row (n : ℤ) (by omega) ≫ (D.abutment I n).hom = (η n).app F

section CarrierComparison

set_option quotPrecheck false in
set_option hygiene false in
local notation "L" => sheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "P" => presheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cochainCarrierLift.{u,r,a,v,b} R c

variable [EnoughInjectives (AmbientSheaves.{max a b} R)]
  [(L).PreservesInjectiveObjects] [(L).PreservesHomology] [(P).PreservesHomology]
  {D : NaturalityData.{u,r,a,v} R c} {E : NaturalityData.{u,r,max a b,v} R c}
  {F : SheafOfModules.{a} R} {I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)}

/-- The full Čech complex in the common category identifies with the lift
of the complex of the given coefficient, using the two tuple comparisons. -/
def commonCochainIso (A : CarrierModelComparison.{u,r,a,v,b} R c D E I)
    (e : CoefficientComparison.{a,u,r,v} R c) :
    cochainComplex.{u,r,max a b,v} R c ((L).obj (nativeCoefficient.{u,r,a} R F)).val ≅
      ((S).mapHomologicalComplex (.up ℕ)).obj (liftedRawCochainComplex.{a,u,r,v} R c F) :=
  A.localTuples (nativeCoefficient.{u,r,a} R F).val ≪≫
    ((S).mapHomologicalComplex (.up ℕ)).mapIso (e.iso.app F.val).symm

/-- The induced identification on original Čech cohomology, including the
canonical identifications for the exact lifts and the zero extension. -/
def commonSourceIso (A : CarrierModelComparison.{u,r,a,v,b} R c D E I)
    (e : CoefficientComparison.{a,u,r,v} R c) (n : ℕ) :
    ((cochainComplex.{u,r,max a b,v} R c ((L).obj (nativeCoefficient.{u,r,a} R F)).val).extend
      embedding).homology (n : ℤ) ≅ (S).obj ((sourceCohomology.{a,u,r,v} R c n).obj F) :=
  let K := cochainComplex.{u,r,max a b,v} R c ((L).obj (nativeCoefficient.{u,r,a} R F)).val
  let K₀ := (rawComplexFunctor.{a,u,r,v} R c).obj F
  let K₁ := liftedRawCochainComplex.{a,u,r,v} R c F
  K.extendHomologyIso embedding (j := n) (j' := (n : ℤ)) (by simp [embedding]) ≪≫
    homologyMapIso (commonCochainIso.{a,u,r,v,b} R c (F := F) A e) n ≪≫
    (K₁.sc n).mapHomologyIso (S) ≪≫
    (S).mapIso ((K₀.sc n).mapHomologyIso (rawCochainLift.{a,u,r,v} R c))

/-- The comparison through both augmentations commutes with passage from
the native resolution to its common lift in the HA-H03-Carrier coordinates. -/
def AgreesAfterEnlargement (A : CarrierModelComparison.{u,r,a,v,b} R c D E I)
    (e : CoefficientComparison.{a,u,r,v} R c)
    (η : ∀ n, sourceCohomology.{a,u,r,v} R c n ⟶ originalSectionCohomology.{a,u,r,v} R c n) :
    Prop :=
  let I' := carrierLiftResolution.{u,r,a,b} R I
  let K := cochainComplex.{u,r,max a b,v} R c ((L).obj (nativeCoefficient.{u,r,a} R F)).val
  ∃ β : K.extend embedding ⟶ sumTotal (doubleComplexInt.{u,r,max a b,v} R c I'.cocomplex),
    (∀ p : ℕ, β.f (p : ℤ) =
      (K.extendXIso embedding (by simp [embedding] : embedding.f p = (p : ℤ))).hom ≫
        (verticalAugmentation.{u,r,max a b,v} R c I').f p ≫
        (intBicomplexTermIso (doubleComplex.{u,r,max a b,v} R c I'.cocomplex) p 0).inv ≫
        sumInjection (doubleComplexInt.{u,r,max a b,v} R c I'.cocomplex) (p : ℤ) 0 (p : ℤ)
          (add_zero _)) ∧
    ∀ n : ℕ,
      letI := E.augmentation_quasiIso I'
      letI : IsIso (homologyMap (E.augmentation I') (n : ℤ)) := inferInstance
      homologyMap β (n : ℤ) ≫ inv (homologyMap (E.augmentation I') (n : ℤ)) ≫
        liftedSectionModelMap.{u,r,max a b,v} R c I' n ≫ (A.target n).hom =
        (commonSourceIso.{a,u,r,v,b} R c (F := F) A e n).hom ≫ (S).map ((η n).app F)

end CarrierComparison

end AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients

def comparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {T : Type v} (c : Cover U T),
    ∃ h : EnoughInjectives (AmbientSheaves.{a} R),
      letI := h
      Nonempty (NaturalityData.{u,r,a,v} R c) ∧
      ∃ (e : CoefficientComparison.{a,u,r,v} R c)
        (η : ∀ n, sourceCohomology.{a,u,r,v} R c n ⟶
          originalSectionCohomology.{a,u,r,v} R c n),
        (∀ (F : SheafOfModules.{a} R) (n : ℕ), AcyclicOnIntersections.{a,u,r,v} R c F →
          Function.Bijective (originalComparisonMap R c n (η n) F)) ∧
        (∀ {F G : SheafOfModules.{a} R} (f : F ⟶ G) (n : ℕ) (x :
          ((rawComplexFunctor.{a,u,r,v} R c).obj F).homology n),
          originalComparisonMap R c n (η n) G (homologyMap ((rawComplexFunctor R c).map f) n x) =
            (coefficientCohomologyValue.{a,u,r} X R U n).map f
              (originalComparisonMap R c n (η n) F x)) ∧
        ∀ (D : NaturalityData.{u,r,a,v} R c) (F : SheafOfModules.{a} R)
          (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)),
          ∃ β, IsVerticalAugmentation R c e F I β ∧ AgreesWithModel R c D e η F I β

/-- Naturality for the given sectionwise map between independently sized
coefficients, with both native comparisons in the same normalized model
coordinates used for the mixed Čech spectral sequence. -/
def mixedComparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {T : Type v} (c : Cover U T)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{b} R)]
    [EnoughInjectives (AmbientSheaves.{max a b} R)],
    let L₁ := sheafCarrierLift.{u,r,a,b} R
    let L₂ := sheafCarrierLift.{u,r,b,a} R
    let P₁ := presheafCarrierLift.{u,r,a,b} R
    let P₂ := presheafCarrierLift.{u,r,b,a} R
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
        (E : NaturalityData.{u,r,max a b,v} R c),
      ∀ {F : SheafOfModules.{a} R} {G : SheafOfModules.{b} R} (f : SectionwiseHom F G)
        (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F))
        (J : InjectiveResolution (nativeCoefficient.{u,r,b} R G))
        (e₁ : CoefficientComparison.{a,u,r,v} R c) (e₂ : CoefficientComparison.{b,u,r,v} R c)
        (η₁ : ∀ n, sourceCohomology.{a,u,r,v} R c n ⟶ originalSectionCohomology.{a,u,r,v} R c n)
        (η₂ : ∀ n, sourceCohomology.{b,u,r,v} R c n ⟶ originalSectionCohomology.{b,u,r,v} R c n)
        {β₁ β₂},
        IsVerticalAugmentation R c e₁ F I β₁ → AgreesWithModel R c D₁ e₁ η₁ F I β₁ →
        IsVerticalAugmentation R c e₂ G J β₂ → AgreesWithModel R c D₂ e₂ η₂ G J β₂ →
        ∃ (A₁ : CarrierModelComparison.{u,r,a,v,b} R c D₁ E I)
          (A₂ : CarrierModelComparison.{u,r,b,v,a} R c D₂ E J)
          (j₁ : IndividualCohomologyComparison.{b,u,r,a} X R U)
          (j₂ : IndividualCohomologyComparison.{a,u,r,b} X R U)
          (g : ∀ n : ℕ, ((rawComplexFunctor.{a,u,r,v} R c).obj F).homology n →ₗ[sectionRing R U]
            ((rawComplexFunctor.{b,u,r,v} R c).obj G).homology n)
          (h : ∀ n : ℕ, (coefficientCohomologyValue.{a,u,r} X R U n).obj F →ₗ[sectionRing R U]
            (coefficientCohomologyValue.{b,u,r} X R U n).obj G),
          let f' := mixedCoefficientMap.{u,r,a,b} R f
          let g' := cochainMap.{u,r,max a b,v} R c f'.val
          AgreesAfterEnlargement.{a,u,r,v,b} R c (F := F) A₁ e₁ η₁ ∧
          AgreesAfterEnlargement.{b,u,r,v,a} R c (F := G) A₂ e₂ η₂ ∧
          IsIndividualCohomologyComparison X R U j₁ ∧ IsIndividualCohomologyComparison X R U j₂ ∧
          (∀ (p : ℕ) (s : Cochains R F.val c p),
            (((commonCochainIso.{a,u,r,v,b} R c (F := F) A₁ e₁).inv ≫ g' ≫
              (commonCochainIso.{b,u,r,v,a} R c (F := G) A₂ e₂).hom).f p)
              (ULift.up (ULift.up s)) =
              ULift.up (ULift.up (fun t ↦ f.app (op (tupleOpen c t)) (s t)))) ∧
          (∀ (n : ℕ) (x : ((rawComplexFunctor.{a,u,r,v} R c).obj F).homology n),
            ((commonSourceIso.{a,u,r,v,b} R c (F := F) A₁ e₁ n).inv ≫
              homologyMap (extendMap g' embedding) (n : ℤ) ≫
              (commonSourceIso.{b,u,r,v,a} R c (F := G) A₂ e₂ n).hom) (ULift.up (ULift.up x)) =
                ULift.up (ULift.up (g n x))) ∧
          (∀ (n : ℕ) (x : (coefficientCohomologyValue.{a,u,r} X R U n).obj F),
            (cohomologyValue.{max a b,u,r} R U n).map f.lift.{max u r}
              ((j₁ n).hom.app F (ULift.up x)) = (j₂ n).hom.app G (ULift.up (h n x))) ∧
          (∀ (n : ℕ) (x : (coefficientCohomologyValue.{a,u,r} X R U n).obj F),
            ((A₁.target n).inv ≫ (sectionLift.{u,r,max a b,v} R c).map
              ((cohomologyValue.{max a b,u,r} R U n).map f') ≫ (A₂.target n).hom)
                (ULift.up (ULift.up x)) = ULift.up (ULift.up (h n x))) ∧
          ∀ (n : ℕ) (x : ((rawComplexFunctor.{a,u,r,v} R c).obj F).homology n),
            originalComparisonMap R c n (η₂ n) G (g n x) =
              h n (originalComparisonMap R c n (η₁ n) F x)

end Specs.AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients
