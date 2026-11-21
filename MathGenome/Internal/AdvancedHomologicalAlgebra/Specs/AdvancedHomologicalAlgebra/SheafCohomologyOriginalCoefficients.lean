import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Sections and right-derived sections over the original site and ring. -/

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.SheafCohomology
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors

universe a u r

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.checkUnivs false
set_option linter.unusedVariables false

namespace Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

attribute [local instance] HasDerivedCategory.standard

section Site

variable (X : TopCat.{u})

local notation "J₀" => Opens.grothendieckTopology X
private abbrev raisedOpensTopology := Opens.grothendieckTopology (liftedSpace.{a} X)
private abbrev raisedOpensEquivalence := (opensEquiv.{a} X).equivalence.symm
private instance : (raisedOpensEquivalence.{a} X).functor.IsCocontinuous J₀ (raisedOpensTopology.{a} X) :=
  ((raisedOpensEquivalence.{a} X).toAdjunction.isCocontinuous_iff_coverPreserving J₀ (raisedOpensTopology.{a} X)).mpr
    (opensCongrCoverPreserving (X.uliftFunctorObjHomeo.{a}).symm)

private instance : (raisedOpensEquivalence.{a} X).inverse.IsCocontinuous (raisedOpensTopology.{a} X) J₀ :=
  ((raisedOpensEquivalence.{a} X).symm.toAdjunction.isCocontinuous_iff_coverPreserving (raisedOpensTopology.{a} X) J₀).mpr
    (opensCongrCoverPreserving (X.uliftFunctorObjHomeo.{a}))

private instance : (raisedOpensEquivalence.{a} X).inverse.IsDenseSubsite (raisedOpensTopology.{a} X) J₀ :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous J₀ (raisedOpensTopology.{a} X) (raisedOpensEquivalence.{a} X)

def originalAbelianEquivalence :
    Sheaf J₀ AddCommGrpCat.{max a u} ≌ Sheaf (raisedOpensTopology.{a} X) AddCommGrpCat.{max a u} :=
  (raisedOpensEquivalence.{a} X).sheafCongr J₀ (raisedOpensTopology.{a} X) _

instance (priority := 90) sectionHasSheafify : HasSheafify J₀ AddCommGrpCat.{max a u} :=
  Equivalence.hasSheafify J₀ (raisedOpensTopology.{a} X) (raisedOpensEquivalence.{a} X) _

instance (priority := 90) sectionWEqualsLocallyBijective : (J₀).WEqualsLocallyBijective AddCommGrpCat.{max a u} := by
  let T := originalAbelianEquivalence.{a} X
  have : ((raisedOpensEquivalence.{a} X).inverse.sheafPushforwardContinuous AddCommGrpCat.{max a u} (raisedOpensTopology.{a} X) J₀).EssSurj :=
    inferInstanceAs T.functor.EssSurj
  exact GrothendieckTopology.WEqualsLocallyBijective.transport J₀ (raisedOpensTopology.{a} X) (raisedOpensEquivalence.{a} X).inverse
    (opensCongrCoverPreserving (X.uliftFunctorObjHomeo.{a}).symm)

end Site

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)

abbrev SectionModules := ModuleCat.{max a u r} (R.obj.obj (op U))

abbrev OpenModules := SheafOfModules.{max a u r} (U.sheafRestrict.obj R)

@[implicit_reducible] def openModulesAbelian : Abelian (OpenModules.{a} R U) := by
  letI := sectionHasSheafify.{max a r,u} (TopCat.of U)
  letI := sectionWEqualsLocallyBijective.{max a r,u} (TopCat.of U)
  infer_instance

abbrev sectionsValue : AmbientSheaves.{a} R ⥤ SectionModules.{a} R U :=
  SheafOfModules.evaluation R (op U)

instance : (sectionsValue.{a} R U).Additive where
  map_add := by intros; ext x; rfl

/-- Sections on the actual open subspace, evaluated at the terminal over-open. -/
def openSectionsValue : OpenModules.{a} R U ⥤ SectionModules.{a} R U :=
  (U.sheafOfModulesEquivOver R).inverse ⋙
    SheafOfModules.evaluation (R.over U) (op (Over.mk (𝟙 U)))

instance : (openSectionsValue.{a} R U).Additive where
  map_add := by intros; ext x; rfl

instance : (originalRestriction.{a} R U).Additive where
  map_add := by intros; ext V x; rfl

/-- Applying the inverse unit of the open-site equivalence gives the actual
identification of sections on the subspace with sections on the original open. -/
def sectionsRestrictionValue :
    originalRestriction.{a} R U ⋙ openSectionsValue.{a} R U ≅ sectionsValue.{a} R U := by
  let E := U.sheafOfModulesEquivOver.{max a u r} R
  let F := SheafOfModules.overFunctor.{max a u r} R U
  let G := SheafOfModules.evaluation.{max a u r} (R.over U) (op (Over.mk (𝟙 U)))
  exact (Functor.associator (F ⋙ E.functor) E.inverse G).symm ≪≫
    isoWhiskerRight (Functor.associator F E.functor E.inverse ≪≫
      isoWhiskerLeft F E.unitIso.symm ≪≫ Functor.rightUnitor F) G

def enoughInjectivesType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}), EnoughInjectives (AmbientSheaves.{a} R)

def openEnoughInjectivesType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X),
    EnoughInjectives (OpenModules.{a} R U)

variable [EnoughInjectives (AmbientSheaves.{a} R)]

def cohomologyValue (n : ℕ) : AmbientSheaves.{a} R ⥤ SectionModules.{a} R U :=
  rightValue (sectionsValue.{a} R U) n

def systemValue : CohomologicalSystem (AmbientSheaves.{a} R) (SectionModules.{a} R U) :=
  rightSystem (sectionsValue.{a} R U)

def cohomologyType :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] (n : ℕ),
    AmbientSheaves.{a} R ⥤ SectionModules.{a} R U

def systemType :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)],
    CohomologicalSystem (AmbientSheaves.{a} R) (SectionModules.{a} R U)

def openSectionsType :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X),
    OpenModules.{a} R U ⥤ SectionModules.{a} R U

def sectionsRestrictionType :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X),
    originalRestriction.{a} R U ⋙ openSectionsValue.{a} R U ≅ sectionsValue.{a} R U

variable [EnoughInjectives (OpenModules.{a} R U)]

def openCohomologyValue (n : ℕ) : AmbientSheaves.{a} R ⥤ SectionModules.{a} R U := by
  letI := openModulesAbelian.{a} R U
  exact originalRestriction.{a} R U ⋙ rightValue (openSectionsValue.{a} R U) n

def openCohomologyType :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (OpenModules.{a} R U)] (n : ℕ),
    AmbientSheaves.{a} R ⥤ SectionModules.{a} R U

/-- The chain map induced on the resolution by a functor, with the
canonical identification of the two degree-zero stalk complexes. -/
def mapAugmentation {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (J : A ⥤ B) [J.Additive] {M : A} {I : CochainComplex A ℤ}
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) :
    (CochainComplex.singleFunctor B 0).obj (J.obj M) ⟶
      (J.mapHomologicalComplex (.up ℤ)).obj I :=
  (J.mapCochainComplexSingleFunctor 0).inv.app M ≫
    (J.mapHomologicalComplex (.up ℤ)).map i

/-- Every augmented injective model computes the original cohomology through
the actual derived unit and the localized augmentation. -/
def resolutionType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] (M : AmbientSheaves.{a} R)
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ) [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M ⟶ I)
    (hi : QuasiIso i), (∀ q : ℤ, Injective (I.X q)) → ∀ n : ℕ,
    IsIso (resolutionModelMap (sectionsValue.{a} R U) i hi n)

def resolutionNaturalityType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] {M N : AmbientSheaves.{a} R}
    {I J : CochainComplex (AmbientSheaves.{a} R) ℤ} [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M ⟶ I) (hi : QuasiIso i)
    (j : (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj N ⟶ J) (hj : QuasiIso j)
    (f : M ⟶ N) (g : I ⟶ J),
    i ≫ g = (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).map f ≫ j →
    ∀ n : ℕ, resolutionModelMap (sectionsValue.{a} R U) i hi n ≫
        (cohomologyValue.{a} R U n).map f =
      HomologicalComplex.homologyMap
        (((sectionsValue.{a} R U).mapHomologicalComplex (.up ℤ)).map g) (n : ℤ) ≫
      resolutionModelMap (sectionsValue.{a} R U) j hj n

def zeroType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)], IsIso (rightDegreeZeroUnit (sectionsValue.{a} R U))

def longExactType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)], IsCohomological (systemValue.{a} R U)

/-- Locality through the actual restricted augmentation, with normalization
on ordinary sections and on the connecting maps. -/
def localityType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (OpenModules.{a} R U)],
    letI := openModulesAbelian.{a} R U
    let Γ := sectionsValue.{a} R U
    let J := originalRestriction.{a} R U
    let ΓU := openSectionsValue.{a} R U
    ∃ e : ∀ n : ℕ, cohomologyValue.{a} R U n ≅ openCohomologyValue.{a} R U n,
      rightDegreeZeroUnit Γ ≫ (e 0).hom =
        (sectionsRestrictionValue.{a} R U).inv ≫ whiskerLeft J (rightDegreeZeroUnit ΓU) ∧
      (∀ (S : ShortComplex (AmbientSheaves.{a} R)) (hS : S.ShortExact),
        ∃ hJS : (S.map J).ShortExact, ∀ n : ℕ,
          (e n).hom.app S.X₃ ≫ rightBoundary ΓU hJS n =
            rightBoundary Γ hS n ≫ (e (n + 1)).hom.app S.X₁) ∧
      ∀ (M : AmbientSheaves.{a} R) (I : CochainComplex (AmbientSheaves.{a} R) ℤ)
        [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M ⟶ I)
        (hi : QuasiIso i), (∀ q : ℤ, Injective (I.X q)) →
        ∃ hJi : QuasiIso (mapAugmentation J i),
          (∀ q : ℤ, Injective (J.obj (I.X q))) ∧
          ∀ n : ℕ,
            resolutionModelMap Γ i hi n ≫ (e n).hom.app M =
              HomologicalComplex.homologyMap
                ((Functor.mapHomologicalComplexCompIso (sectionsRestrictionValue.{a} R U)
                  (.up ℤ)).inv.app I) (n : ℤ) ≫
              resolutionModelMap ΓU (mapAugmentation J i) hJi n

section Comparisons

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  (F : A ⥤ B) (G : A' ⥤ B') (J : A ⥤ A') (H : B ⥤ B')
  [F.Additive] [G.Additive] [J.Additive] [H.Additive] [H.PreservesHomology]
  (c : F ⋙ H ≅ J ⋙ G)

/-- The termwise comparison on section complexes, followed by homology. -/
def modelComparison (I : CochainComplex A ℤ) (n : ℕ) :
    H.obj (((F.mapHomologicalComplex (.up ℤ)).obj I).homology (n : ℤ)) ≅
      ((G.mapHomologicalComplex (.up ℤ)).obj
        ((J.mapHomologicalComplex (.up ℤ)).obj I)).homology (n : ℤ) :=
  ((((F.mapHomologicalComplex (.up ℤ)).obj I).sc (n : ℤ)).mapHomologyIso H).symm ≪≫
    (HomologicalComplex.homologyFunctor B' (.up ℤ) (n : ℤ)).mapIso
      ((NatIso.mapHomologicalComplex c (.up ℤ)).app I)

variable [EnoughInjectives A] [EnoughInjectives A']

/-- Natural comparison characterized by the augmented model, on every
source injective resolution. The target model can have acyclic terms. -/
def IsResolutionComparison (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n) : Prop :=
    ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
      (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i),
      (∀ q : ℤ, Injective (I.X q)) →
      ∃ hJi : QuasiIso (mapAugmentation J i), ∀ n : ℕ,
        H.map (resolutionModelMap F i hi n) ≫ (e n).hom.app M =
          (modelComparison F G J H c I n).hom ≫
            resolutionModelMap G (mapAugmentation J i) hJi n

def ResolutionComparison : Prop :=
  ∃ e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n,
    IsResolutionComparison F G J H c e

/-- The same comparison on augmented resolutions also identifies the actual
degree-zero units, with the indicated ordinary section identification. -/
def DegreeZeroResolutionComparison : Prop :=
  ∃ e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n,
    IsResolutionComparison F G J H c e ∧
    whiskerRight (rightDegreeZeroUnit F) H ≫ (e 0).hom =
      c.hom ≫ whiskerLeft J (rightDegreeZeroUnit G)

end Comparisons

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- Choose the larger site's open corresponding to the specified original open. -/
abbrev liftedOpen (V : Opens X) : Opens (liftedSpace.{max a u r} X) :=
  (opensEquiv.{max a u r} X).symm V

/-- Restrict the transported section module along the original section-ring
equivalence. The formula keeps the additive section carriers. -/
abbrev originalScalars (U : Opens (liftedSpace.{max a u r} X)) :=
  ModuleCat.restrictScalars.{max a u r} (sectionRingEquiv.{a} R U).toRingHom

/-- The inverse scalar change allows the ordinary section square to have
codomain the transported section-module category. -/
def liftedScalars (U : Opens (liftedSpace.{max a u r} X)) :=
  ModuleCat.restrictScalars.{max a u r} (sectionRingEquiv.{a} R U).symm.toRingHom

def siteSectionsIso (U : Opens (liftedSpace.{max a u r} X)) :
    sectionsValue.{a} R (opensEquiv X U) ⋙ liftedScalars.{a} R U ≅
      transport.{a} R ⋙ SheafOfModules.evaluation (liftedRing.{a} R) (op U) :=
  NatIso.ofComponents (fun M ↦ by
    let P := (sectionsValue.{a} R (opensEquiv X U) ⋙ liftedScalars.{a} R U).obj M
    let Q := (transport.{a} R ⋙ SheafOfModules.evaluation (liftedRing.{a} R) (op U)).obj M
    let e : (P : Type (max a u r)) ≃ₗ[(liftedRing.{a} R).obj.obj (op U)]
        (Q : Type (max a u r)) :=
      { toAddEquiv := sectionEquiv.{a} R M U
        map_smul' := fun _ _ ↦ rfl }
    exact e.toModuleIso)
    (by intros; ext x; rfl)

/-- The statement is at the lifted section ring via its equivalence with the
original one. Applying restriction along the equivalence returns the original
module structures. -/
instance (U : Opens (liftedSpace.{max a u r} X)) :
    (liftedScalars.{a} R U).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max a u r,r,max a u r}
    (sectionRingEquiv.{a} R U).symm).isEquivalence_functor

instance (U : Opens (liftedSpace.{max a u r} X)) :
    (liftedScalars.{a} R U).Additive where
  map_add := by intros; ext x; rfl

instance : (transport.{a} R).Additive where
  map_add := by intros; ext V x; rfl

def siteComparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (AmbientSheaves.{a} R)],
    ResolutionComparison (sectionsValue.{a} R (opensEquiv X U))
      (sectionsValue.{0} (liftedRing.{a} R) U)
      (transport.{a} R) (liftedScalars.{a} R U) (siteSectionsIso.{a} R U)

/-- The transported cohomology restricted along the original section ring. -/
def transportedCohomologyValue (U : Opens (liftedSpace.{max a u r} X)) (n : ℕ) :
    AmbientSheaves.{a} R ⥤ SectionModules.{a} R (opensEquiv X U) :=
  (transport.{a} R ⋙ AdvancedHomologicalAlgebra.SheafTheory.sectionCohomology
    (liftedRing.{a} R) U n) ⋙ originalScalars.{a} R U

/-- Take the normalized comparison in raised scalar coordinates back to the
original section ring, using the counit of the scalar equivalence. -/
def recoverOriginalScalars (U : Opens (liftedSpace.{max a u r} X))
    (F : AmbientSheaves.{a} R ⥤ SectionModules.{a} R (opensEquiv X U)) (n : ℕ)
    (e : F ⋙ liftedScalars.{a} R U ≅ transport.{a} R ⋙
      AdvancedHomologicalAlgebra.SheafTheory.sectionCohomology (liftedRing.{a} R) U n) :
    F ≅ transportedCohomologyValue.{a} R U n := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{r,max a u r,max a u r}
    (sectionRingEquiv.{a} R U)
  exact (Functor.rightUnitor F).symm ≪≫ isoWhiskerLeft F E.counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e E.functor

def siteComparisonOriginalType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (AmbientSheaves.{a} R)],
    let F := sectionsValue.{a} R (opensEquiv X U)
    let G := sectionsValue.{0} (liftedRing.{a} R) U
    let J := transport.{a} R
    let H := liftedScalars.{a} R U
    ∃ (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n)
      (c : ∀ n : ℕ, cohomologyValue.{a} R (opensEquiv X U) n ≅
        transportedCohomologyValue.{a} R U n),
      IsResolutionComparison F G J H (siteSectionsIso.{a} R U) e ∧
        ∀ n, c n = recoverOriginalScalars.{a} R U _ n (e n)

def flasqueType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] (M : AmbientSheaves.{a} R),
    IsFlasque R M → ∀ n : ℕ, IsZero ((cohomologyValue.{a} R U (n + 1)).obj M)

universe b

def ambientComparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max b a} R)],
    ResolutionComparison (sectionsValue.{a} R U) (sectionsValue.{max b a} R U)
      (liftSheafCoefficients.{b,u,r,max a u r} R)
      (ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U)))
      (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{b,u,r,max a u r} X R U).symm

/-- Ordinary abelian sheaves on the original site with admissible carriers. -/
abbrev OriginalAbelianSheaves (X : TopCat.{u}) :=
  Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max a u r}

/-- This evaluates the actual abelian sheaf, with its original restrictions. -/
abbrev abelianSectionsValue (X : TopCat.{u}) (U : Opens X) :
    OriginalAbelianSheaves.{a,u,r} X ⥤ AddCommGrpCat.{max a u r} :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op U)

instance (X : TopCat.{u}) (U : Opens X) : (abelianSectionsValue.{a,u,r} X U).Additive where
  map_add := by intros; rfl

def forgetComparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)],
    ResolutionComparison (sectionsValue.{a} R U) (abelianSectionsValue.{a,u,r} X U)
      (SheafOfModules.toSheaf R) (forget₂ (SectionModules.{a} R U) AddCommGrpCat.{max a u r})
      (Iso.refl _)


/-- Original coefficients in any universe, moved into the adequate category
over their given site and ring by the objectwise coefficient lift. -/
def coefficientCohomologyValue (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] (n : ℕ) :
    SheafOfModules.{a} R ⥤ SectionModules.{a} R U :=
  liftSheafCoefficients.{max u r,u,r,a} R ⋙ cohomologyValue.{a} R U n

def coefficientCohomologyType :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] (_n : ℕ),
    SheafOfModules.{a} R ⥤ SectionModules.{a} R U

def coefficientFlasqueType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] (M : SheafOfModules.{a} R),
    IsFlasque R M → ∀ n : ℕ,
    IsZero ((coefficientCohomologyValue.{a} X R U (n + 1)).obj M)

/-- The degree-zero map for arbitrary coefficients is the original section
map, evaluated after the objectwise lift. -/
def coefficientZeroType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)],
    let J := liftSheafCoefficients.{max u r,u,r,a} R
    let c := Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{max u r,u,r,a} X R U
    IsIso (c.inv ≫ whiskerLeft J (rightDegreeZeroUnit (sectionsValue.{a} R U)))

/-- Germ-locally exact sequences with arbitrary original coefficient carriers
yield the long exact sequence with the boundary of the lifted short exact
sequence on the original site. -/
def coefficientLongExactType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)]
    (S : ShortComplex (SheafOfModules.{a} R)),
    GermLocallyShortExact R.obj (S.map (SheafOfModules.forget R)) →
    let T := S.map (liftSheafCoefficients.{max u r,u,r,a} R)
    let F := systemValue.{a} R U
    ∃ hT : T.ShortExact, (∀ n : ℕ,
      ExactPair (F.δ hT n) ((F.value (n + 1)).map T.f) ∧
      ExactPair ((F.value n).map T.f) ((F.value n).map T.g) ∧
      ExactPair ((F.value n).map T.g) (F.δ hT n)) ∧ Mono ((F.value 0).map T.f)

/-- Linear restriction of ordinary sections over the original section map. -/
abbrev restrictSectionScalars (X : TopCat.{u}) (R : X.Sheaf RingCat.{r})
    {U V : Opens X} (i : V ⟶ U) : SectionModules.{a} R V ⥤ SectionModules.{a} R U :=
  ModuleCat.restrictScalars (R.obj.map i.op).hom

instance (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) {U V : Opens X} (i : V ⟶ U) :
    PreservesFiniteLimits (restrictSectionScalars.{a} X R i) where
  preservesFiniteLimits K _ _ := by
    constructor
    intro L
    exact ModuleCat.preservesLimit_restrictScalars (R.obj.map i.op).hom L

instance (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) {U V : Opens X} (i : V ⟶ U) :
    PreservesFiniteColimits (restrictSectionScalars.{a} X R i) where
  preservesFiniteColimits K _ _ := by
    constructor
    intro L
    exact ModuleCat.preservesColimit_restrictScalars (R.obj.map i.op).hom L

def restrictSections (X : TopCat.{u}) (R : X.Sheaf RingCat.{r})
    {U V : Opens X} (i : V ⟶ U) :
    sectionsValue.{a} R U ⟶ sectionsValue.{a} R V ⋙ restrictSectionScalars.{a} X R i :=
  whiskerLeft (SheafOfModules.forget.{max a u r} R)
    (PresheafOfModules.restriction R.obj i.op)

section AbelianUnit

open AdvancedHomologicalAlgebra.SheafTheory (constantIntegerRingSheaf)
open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport (OpenTransportData)

variable (X : TopCat.{u}) (U : Opens (liftedSpace.{max a u r} X))

abbrev IntegerOpenData :=
  OpenTransportData.{max a r} (constantIntegerRingSheaf X) U

/-- Extension by zero of the original integer unit, in the adequate abelian category. -/
def originalAbelianUnit (D : IntegerOpenData.{a,u,r} X U) : OriginalAbelianSheaves.{a,u,r} X :=
  (SheafOfModules.toSheaf (constantIntegerRingSheaf X)).obj
    (originalExtendedUnitOf (constantIntegerRingSheaf X) U D.overExtension)

def originalAbelianUnitSection (D : IntegerOpenData.{a,u,r} X U) :
    (abelianSectionsValue.{a,u,r} X (opensEquiv X U)).obj (originalAbelianUnit.{a,u,r} X U D) :=
  originalExtendedGeneratorOf (constantIntegerRingSheaf X) U
    D.overExtension D.overAdjunction

def abelianUnitType : Prop :=
  ∀ (X : TopCat.{u}) (U : Opens (liftedSpace.{max a u r} X))
    (D : IntegerOpenData.{a,u,r} X U),
    let Γ := abelianSectionsValue.{a,u,r} X (opensEquiv X U)
    let A := originalAbelianUnit.{a,u,r} X U D
    ∃ e : preadditiveCoyoneda.obj (op A) ≅ Γ,
      ∀ (F : OriginalAbelianSheaves.{a,u,r} X) (f : A ⟶ F),
        e.hom.app F f = Γ.map f (originalAbelianUnitSection.{a,u,r} X U D)

end AbelianUnit


/-- On every augmented injective resolution the restriction in cohomology
is induced by the original section restrictions, with the actual scalar map. -/
def restrictionMapType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) {U V : Opens X} (f : V ⟶ U)
    [EnoughInjectives (AmbientSheaves.{a} R)],
    let H := restrictSectionScalars.{a} X R f
    let Γ := sectionsValue.{a} R U
    let Γ' := sectionsValue.{a} R V
    let c := restrictSections.{a} X R f
    ∃ t : ∀ n : ℕ, cohomologyValue.{a} R U n ⟶ cohomologyValue.{a} R V n ⋙ H,
      rightDegreeZeroUnit Γ ≫ t 0 = c ≫ whiskerRight (rightDegreeZeroUnit Γ') H ∧
      (∀ (S : ShortComplex (AmbientSheaves.{a} R)) (hS : S.ShortExact) (n : ℕ),
        (t n).app S.X₃ ≫ H.map (rightBoundary Γ' hS n) =
          rightBoundary Γ hS n ≫ (t (n + 1)).app S.X₁) ∧
      ∀ (M : AmbientSheaves.{a} R) (I : CochainComplex (AmbientSheaves.{a} R) ℤ)
        [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M ⟶ I)
        (hi : QuasiIso i), (∀ q : ℤ, Injective (I.X q)) → ∀ n : ℕ,
        resolutionModelMap Γ i hi n ≫ (t n).app M =
          HomologicalComplex.homologyMap ((c.mapHomologicalComplex (.up ℤ)).app I) (n : ℤ) ≫
          ((((Γ'.mapHomologicalComplex (.up ℤ)).obj I).sc (n : ℤ)).mapHomologyIso H).hom ≫
          H.map (resolutionModelMap Γ' i hi n)


section ExtComparison

open CochainComplex CochainComplex.HomComplex
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

/-- The shifted Hom comparison is natural on the actual abelian coefficients
and is induced by evaluating each cochain at the original universal section. -/
def abelianExtType : Prop :=
  ∀ (X : TopCat.{u}) (U : Opens (liftedSpace.{max a u r} X))
    (D : IntegerOpenData.{a,u,r} X U)
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)],
    let A := OriginalAbelianSheaves.{a,u,r} X
    let P := originalAbelianUnit.{a,u,r} X U D
    let Γ := abelianSectionsValue.{a,u,r} X (opensEquiv X U)
    ∃ e : ∀ (M : A) (n : ℕ), (rightValue Γ n).obj M ≃+ Ext P M (n : ℤ),
      (∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (rightValue Γ n).obj M),
        e N n ((rightValue Γ n).map f x) = extMap (𝟙 P) f (n : ℤ) (e M n x)) ∧
      (∀ (M : A) (f : P ⟶ M), e M 0 ((rightDegreeZeroUnit Γ).app M
        (Γ.map f (originalAbelianUnitSection.{a,u,r} X U D))) = zeroHom f) ∧
      (∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ) (x : (rightValue Γ n).obj S.X₃),
        e S.X₁ (n + 1) (rightBoundary Γ hS n x) =
          ShiftedHom.comp (e S.X₃ n x) hS.singleδ (by omega)) ∧
      ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i),
        (∀ q : ℤ, Injective (I.X q)) →
        let L := (CochainComplex.singleFunctor A 0).obj P
        ∃ c : HomComplex L I ≅ ((Γ.mapHomologicalComplex (.up ℤ)).obj I),
          (∀ (q : ℤ) (f : Cochain L I q),
            c.hom.f q f = Γ.map (Cochain.fromSingleEquiv (zero_add q) f)
              (originalAbelianUnitSection.{a,u,r} X U D)) ∧
          ∀ (n : ℕ) (x : CohomologyClass L I (n : ℤ)),
            e M n (resolutionModelMap Γ i hi n
              (HomologicalComplex.homologyMap c.hom (n : ℤ)
                ((HomComplex.homologyAddEquiv L I (n : ℤ)).symm x))) =
              injectiveClassMap P M I i hi (n : ℤ) x

end ExtComparison


section AbelianTransport

variable (X : TopCat.{u}) (U : Opens (liftedSpace.{max a u r} X))

abbrev abelianTransport := (originalAbelianEquivalence.{max a u r} X).functor

instance : (abelianTransport.{a,u,r} X).Additive where
  map_add := by intros; rfl

abbrev abelianSiteSectionsIso :
    abelianSectionsValue.{a,u,r} X (opensEquiv X U) ⋙ 𝟭 AddCommGrpCat.{max a u r} ≅
      abelianTransport.{a,u,r} X ⋙
        AdvancedHomologicalAlgebra.SheafTheory.abelianSections (liftedSpace.{max a u r} X) U :=
  Iso.refl _

def abelianSiteComparisonType : Prop :=
  ∀ (X : TopCat.{u}) (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)],
    ResolutionComparison
      (abelianSectionsValue.{a,u,r} X (opensEquiv X U))
      (AdvancedHomologicalAlgebra.SheafTheory.abelianSections (liftedSpace.{max a u r} X) U)
      (abelianTransport.{a,u,r} X) (𝟭 AddCommGrpCat.{max a u r})
      (abelianSiteSectionsIso.{a,u,r} X U)

end AbelianTransport

def forgottenResolutionType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (M : AmbientSheaves.{a} R)
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ) [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M ⟶ I),
    QuasiIso i → (∀ q : ℤ, Injective (I.X q)) →
    QuasiIso (mapAugmentation (SheafOfModules.toSheaf.{max a u r} R) i) ∧
    ∀ q : ℤ, TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf.{max a u r} R).obj (I.X q))

def siteComparisonZeroType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (AmbientSheaves.{a} R)],
    DegreeZeroResolutionComparison (sectionsValue.{a} R (opensEquiv X U))
      (sectionsValue.{0} (liftedRing.{a} R) U)
      (transport.{a} R) (liftedScalars.{a} R U) (siteSectionsIso.{a} R U)


def ambientComparisonZeroType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max b a} R)],
    DegreeZeroResolutionComparison (sectionsValue.{a} R U) (sectionsValue.{max b a} R U)
      (liftSheafCoefficients.{b,u,r,max a u r} R)
      (ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U)))
      (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{b,u,r,max a u r} X R U).symm


def forgetComparisonZeroType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)],
    DegreeZeroResolutionComparison (sectionsValue.{a} R U) (abelianSectionsValue.{a,u,r} X U)
      (SheafOfModules.toSheaf R) (forget₂ (SectionModules.{a} R U) AddCommGrpCat.{max a u r})
      (Iso.refl _)



def abelianSiteComparisonZeroType : Prop :=
  ∀ (X : TopCat.{u}) (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)],
    DegreeZeroResolutionComparison
      (abelianSectionsValue.{a,u,r} X (opensEquiv X U))
      (AdvancedHomologicalAlgebra.SheafTheory.abelianSections (liftedSpace.{max a u r} X) U)
      (abelianTransport.{a,u,r} X) (𝟭 AddCommGrpCat.{max a u r})
      (abelianSiteSectionsIso.{a,u,r} X U)



/-- The ordinary site comparison in the original scalar coordinates. -/
def originalSiteSectionsIso (U : Opens (liftedSpace.{max a u r} X)) :
    sectionsValue.{a} R (opensEquiv X U) ≅
      (transport.{a} R ⋙ sectionsValue.{0} (liftedRing.{a} R) U) ⋙ originalScalars.{a} R U := by
  let F := sectionsValue.{a} R (opensEquiv X U)
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{r,max a u r,max a u r}
    (sectionRingEquiv.{a} R U)
  exact (Functor.rightUnitor F).symm ≪≫ isoWhiskerLeft F E.counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (siteSectionsIso.{a} R U) E.functor

/-- The model-normalized comparison also intertwines the degree-zero units
after restriction along the original section ring isomorphism. -/
def siteComparisonOriginalZeroType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (AmbientSheaves.{a} R)],
    let F := sectionsValue.{a} R (opensEquiv X U)
    let G := sectionsValue.{0} (liftedRing.{a} R) U
    let J := transport.{a} R
    let H := liftedScalars.{a} R U
    let K := originalScalars.{a} R U
    ∃ e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n,
      IsResolutionComparison F G J H (siteSectionsIso.{a} R U) e ∧
      rightDegreeZeroUnit F ≫ (recoverOriginalScalars.{a} R U _ 0 (e 0)).hom =
        (originalSiteSectionsIso.{a} R U).hom ≫
          whiskerRight (whiskerLeft J (rightDegreeZeroUnit G)) K

def cohomologyExpectedValue : cohomologyType.{a,u,r} := @cohomologyValue.{a,u,r}

def systemExpectedValue : systemType.{a,u,r} := @systemValue.{a,u,r}

def openSectionsExpectedValue : openSectionsType.{a,u,r} := @openSectionsValue.{a,u,r}

def sectionsRestrictionExpectedValue : sectionsRestrictionType.{a,u,r} := @sectionsRestrictionValue.{a,u,r}

def openCohomologyExpectedValue : openCohomologyType.{a,u,r} := @openCohomologyValue.{a,u,r}

def coefficientCohomologyExpectedValue : coefficientCohomologyType.{a,u,r} := @coefficientCohomologyValue.{a,u,r}

/-- The model, degree-zero unit and connecting maps in one comparison. -/
def ExactResolutionComparison {A A' B B' : Type*}
    [Category* A] [Category* A'] [Category* B] [Category* B']
    [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
    [EnoughInjectives A] [EnoughInjectives A']
    (F : A ⥤ B) (G : A' ⥤ B') (J : A ⥤ A') (H : B ⥤ B')
    [F.Additive] [G.Additive] [J.Additive] [H.Additive] [H.PreservesHomology]
    (c : F ⋙ H ≅ J ⋙ G) : Prop :=
  ∃ e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n,
    IsResolutionComparison F G J H c e ∧
    (whiskerRight (rightDegreeZeroUnit F) H ≫ (e 0).hom =
      c.hom ≫ whiskerLeft J (rightDegreeZeroUnit G)) ∧
    ∀ (S : ShortComplex A) (hS : S.ShortExact),
      ∃ hJS : (S.map J).ShortExact, ∀ n : ℕ,
        (e n).hom.app S.X₃ ≫ rightBoundary G hJS n =
          H.map (rightBoundary F hS n) ≫ (e (n + 1)).hom.app S.X₁

def siteComparisonExactType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (AmbientSheaves.{a} R)],
    ExactResolutionComparison (sectionsValue.{a} R (opensEquiv X U))
      (sectionsValue.{0} (liftedRing.{a} R) U)
      (transport.{a} R) (liftedScalars.{a} R U) (siteSectionsIso.{a} R U)

def ambientComparisonExactType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max b a} R)],
    ExactResolutionComparison (sectionsValue.{a} R U) (sectionsValue.{max b a} R U)
      (liftSheafCoefficients.{b,u,r,max a u r} R)
      (ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U)))
      (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{b,u,r,max a u r} X R U).symm

def forgetComparisonExactType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)],
    ExactResolutionComparison (sectionsValue.{a} R U) (abelianSectionsValue.{a,u,r} X U)
      (SheafOfModules.toSheaf R) (forget₂ (SectionModules.{a} R U) AddCommGrpCat.{max a u r})
      (Iso.refl _)

def abelianSiteComparisonExactType : Prop :=
  ∀ (X : TopCat.{u}) (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)],
    ExactResolutionComparison
      (abelianSectionsValue.{a,u,r} X (opensEquiv X U))
      (AdvancedHomologicalAlgebra.SheafTheory.abelianSections (liftedSpace.{max a u r} X) U)
      (abelianTransport.{a,u,r} X) (𝟭 AddCommGrpCat.{max a u r})
      (abelianSiteSectionsIso.{a,u,r} X U)

/-- The connecting square lives over the original section ring after
restriction along its equivalence with the lifted section ring. -/
def siteComparisonOriginalExactType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (AmbientSheaves.{a} R)],
    let F := sectionsValue.{a} R (opensEquiv X U)
    let G := sectionsValue.{0} (liftedRing.{a} R) U
    let J := transport.{a} R
    let H := liftedScalars.{a} R U
    let K := originalScalars.{a} R U
    ∃ e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n,
      IsResolutionComparison F G J H (siteSectionsIso.{a} R U) e ∧
      (rightDegreeZeroUnit F ≫ (recoverOriginalScalars.{a} R U _ 0 (e 0)).hom =
        (originalSiteSectionsIso.{a} R U).hom ≫
          whiskerRight (whiskerLeft J (rightDegreeZeroUnit G)) K) ∧
      ∀ (S : ShortComplex (AmbientSheaves.{a} R)) (hS : S.ShortExact),
        ∃ hJS : (S.map J).ShortExact, ∀ n : ℕ,
          (recoverOriginalScalars.{a} R U _ n (e n)).hom.app S.X₃ ≫
            K.map (rightBoundary G hJS n) =
              rightBoundary F hS n ≫
                (recoverOriginalScalars.{a} R U _ (n + 1) (e (n + 1))).hom.app S.X₁

/-- Scalar forgetting and the exact change of sites give the same map on
cohomology in the common additive section coordinates. -/
def forgetSiteCompatibilityType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (AmbientSheaves.{a} R)]
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)],
    let V := opensEquiv X U
    let R' := liftedRing.{a} R
    let F := sectionsValue.{a} R V
    let G := sectionsValue.{0} R' U
    let C := abelianSectionsValue.{a,u,r} X V
    let D := AdvancedHomologicalAlgebra.SheafTheory.abelianSections _ U
    let J := transport.{a} R
    let E := abelianTransport.{a,u,r} X
    let O := SheafOfModules.toSheaf.{max a u r} R
    let O' := SheafOfModules.toSheaf.{max a u r} R'
    let H := liftedScalars.{a} R U
    let K := forget₂ (SectionModules.{a} R V) AddCommGrpCat.{max a u r}
    let K' := forget₂ (SectionModules.{0} R' U) AddCommGrpCat.{max a u r}
    ∃ (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n)
      (f : ∀ n : ℕ, rightValue F n ⋙ K ≅ O ⋙ rightValue C n)
      (s : ∀ n : ℕ, rightValue C n ⋙ 𝟭 AddCommGrpCat.{max a u r} ≅ E ⋙ rightValue D n)
      (t : ∀ n : ℕ, rightValue G n ⋙ K' ≅ O' ⋙ rightValue D n),
      IsResolutionComparison F G J H (siteSectionsIso.{a} R U) e ∧
      IsResolutionComparison F C O K (Iso.refl _) f ∧
      IsResolutionComparison C D E (𝟭 _) (abelianSiteSectionsIso.{a,u,r} X U) s ∧
      IsResolutionComparison G D O' K' (Iso.refl _) t ∧
      ∀ (M : AmbientSheaves.{a} R) (n : ℕ),
        (f n).hom.app M ≫ (s n).hom.app (O.obj M) =
          K'.map ((e n).hom.app M) ≫ (t n).hom.app (J.obj M) ≫
            (rightValue D n).map
              ((Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.forgetAbelianComparisonValue.{a,u,r,0} X R).1.hom.app M)

section AbelianExtTransport

open CochainComplex CochainComplex.HomComplex
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

/-- The evaluation of every augmented injective model determines the comparison with Ext. -/
def IsSectionsExtModelComparison.{v} {A : Type*} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] (Γ : A ⥤ AddCommGrpCat.{v}) [Γ.Additive]
    (P : A) (s : Γ.obj P)
    (e : ∀ (M : A) (n : ℕ), (rightValue Γ n).obj M ≃+ Ext P M (n : ℤ)) : Prop :=
  ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i), (∀ q : ℤ, Injective (I.X q)) →
    let L := (CochainComplex.singleFunctor A 0).obj P
    ∃ c : HomComplex L I ≅ (Γ.mapHomologicalComplex (.up ℤ)).obj I,
      (∀ (q : ℤ) (f : Cochain L I q), c.hom.f q f = Γ.map (Cochain.fromSingleEquiv (zero_add q) f) s) ∧
      ∀ (n : ℕ) (x : CohomologyClass L I (n : ℤ)),
        e M n (resolutionModelMap Γ i hi n
          (HomologicalComplex.homologyMap c.hom (n : ℤ)
            ((HomComplex.homologyAddEquiv L I (n : ℤ)).symm x))) =
          injectiveClassMap P M I i hi (n : ℤ) x

/-- Transport of shifted Hom by the exact functor and its canonical stalk isomorphisms. -/
def extTransportValue {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (J : A ⥤ B) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    {P M : A} {P' : B} (e : P' ⟶ J.obj P) {n : ℤ} (x : Ext P M n) : Ext P' (J.obj M) n :=
  (DerivedCategory.singleFunctor B 0).map e ≫
    (J.mapDerivedCategorySingleFunctor 0).inv.app P ≫ ShiftedHom.map x J.mapDerivedCategory ≫
    (CategoryTheory.shiftFunctor _ n).map ((J.mapDerivedCategorySingleFunctor 0).hom.app M)

open AdvancedHomologicalAlgebra.SheafTheory
open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport (liftedSpace opensEquiv)
open Specs.AdvancedHomologicalAlgebra.SheafCohomology (abelianOpenUnitSection)

/-- The abelian site equivalence identifies the representing unit with its generator
and carries the same augmented comparison to shifted derived Hom. -/
def abelianSiteExtType : Prop :=
  ∀ (X : TopCat.{u}) (U : Opens (liftedSpace.{max a u r} X)) (D : IntegerOpenData.{a,u,r} X U)
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)],
    let A := OriginalAbelianSheaves.{a,u,r} X
    let Y := liftedSpace.{max a u r} X
    let J := abelianTransport.{a,u,r} X
    let Γ := abelianSectionsValue.{a,u,r} X (opensEquiv X U)
    let Γ' := abelianSections Y U
    let P := originalAbelianUnit.{a,u,r} X U D
    let s := originalAbelianUnitSection.{a,u,r} X U D
    let P' := abelianOpenUnit Y U
    let s' := abelianOpenUnitSection Y U
    ∃ (q : P' ≅ J.obj P),
      Γ'.map q.hom s' = s ∧
      ∃ (c : ∀ n : ℕ, rightValue Γ n ⋙ 𝟭 AddCommGrpCat.{max a u r} ≅ J ⋙ rightValue Γ' n),
        IsResolutionComparison Γ Γ' J (𝟭 _) (abelianSiteSectionsIso.{a,u,r} X U) c ∧
        ∃ (e : ∀ (M : A) (n : ℕ), (rightValue Γ n).obj M ≃+ Ext P M (n : ℤ))
          (e' : ∀ (M' : AbelianSheaves Y) (n : ℕ), (rightValue Γ' n).obj M' ≃+ Ext P' M' (n : ℤ)),
          IsSectionsExtModelComparison Γ P s e ∧
          IsSectionsExtModelComparison Γ' P' s' e' ∧
          ∀ (M : A) (n : ℕ) (x : (rightValue Γ n).obj M),
            e' (J.obj M) n ((c n).hom.app M x) = extTransportValue J q.hom (e M n x)

end AbelianExtTransport

section OpenSectionsComparison

variable {D E B C C' : Type*} [Category* D] [Category* E] [Category* B]
  [Category* C] [Category* C']
  (Y : E ≌ B) (V : D ⥤ E) (G : E ⥤ C') (F : D ⥤ C) (H : C ⥤ C')
  (s : F ⋙ H ≅ V ⋙ G)

/-- The comparison of open sections from their corresponding over-site sections. -/
def openSectionsComparisonOfOver :
    F ⋙ H ≅ (V ⋙ Y.functor) ⋙ (Y.inverse ⋙ G) :=
  s ≪≫ isoWhiskerLeft V (isoWhiskerRight Y.unitIso G ≪≫
    associator Y.functor Y.inverse G) ≪≫ (associator V Y.functor _).symm

variable {A B' : Type*} [Category* A] [Category* B']
  (X : D ≌ B') (P : A ⥤ D) (Q : A ⥤ E)
  (c : P ⋙ V ≅ Q)

/-- Changing over-site models followed by the equivalence with the actual
open subspace commutes with restriction. -/
def openRestrictionComparisonOfOver :
    (P ⋙ X.functor) ⋙ (X.inverse ⋙ V ⋙ Y.functor) ≅ Q ⋙ Y.functor :=
  associator P X.functor _ ≪≫
    isoWhiskerLeft P ((associator X.functor X.inverse (V ⋙ Y.functor)).symm ≪≫
      isoWhiskerRight X.unitIso.symm _ ≪≫ leftUnitor _) ≪≫
    (associator P V Y.functor).symm ≪≫ isoWhiskerRight c Y.functor

variable {M₀ S₀ : Type*} [Category* M₀] [Category* S₀]
  (L : M₀ ⥤ D) (G₀ : D ⥤ C) (Q₀ : M₀ ⥤ E) (v : L ⋙ V ≅ Q₀)
  (E₀ : D ≌ S₀)

def restrictionSectionsOver :
    (L ⋙ E₀.functor) ⋙ (E₀.inverse ⋙ G₀) ≅ L ⋙ G₀ :=
  (Functor.associator (L ⋙ E₀.functor) E₀.inverse G₀).symm ≪≫
    isoWhiskerRight (Functor.associator L E₀.functor E₀.inverse ≪≫
      isoWhiskerLeft L E₀.unitIso.symm ≪≫ Functor.rightUnitor L) G₀

def ambientSectionsOfOver (e : G₀ ⋙ H ≅ V ⋙ G) :
    (L ⋙ G₀) ⋙ H ≅ Q₀ ⋙ G :=
  associator _ _ _ ≪≫ isoWhiskerLeft L e ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight v G

def subspaceSectionsOfOver (e : G₀ ⋙ H ≅ V ⋙ G) :
    (E₀.inverse ⋙ G₀) ⋙ H ≅ (E₀.inverse ⋙ V ⋙ Y.functor) ⋙ (Y.inverse ⋙ G) :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ (openSectionsComparisonOfOver _ _ _ _ _ e) ≪≫
    (associator _ _ _).symm

end OpenSectionsComparison

open AdvancedHomologicalAlgebra.SheafTheory in
/-- Evaluation at the terminal over-open commutes with change of sites and scalars. -/
def overSiteSectionsIso {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X)) :
    SheafOfModules.evaluation.{max a u r} (R.over (opensEquiv X U))
      (op (Over.mk (𝟙 (opensEquiv X U)))) ⋙ liftedScalars.{a} R U ≅
    transportOver.{a} R U ⋙
      SheafOfModules.evaluation ((liftedRing.{a} R).over U) (op (Over.mk (𝟙 U))) :=
  Iso.refl _

/-- The comparison of sections of an arbitrary sheaf on the actual original
open with sections after the canonical transport on that open. -/
def openSiteSectionsIso {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X)) :
    openSectionsValue.{a} R (opensEquiv X U) ⋙ liftedScalars.{a} R U ≅
      transportOnOpen.{a} R U ⋙ AdvancedHomologicalAlgebra.SheafTheory.openSections (liftedRing.{a} R) U :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ (openSectionsComparisonOfOver _ _ _ _ _
    (overSiteSectionsIso.{a} R U)) ≪≫ (associator _ _ _).symm

/-- The coefficient lift on the actual open subspace over the same ring. -/
abbrev liftOpenCoefficients {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X) :
    OpenModules.{a} R U ⥤ OpenModules.{max a b} R U :=
  liftSheafCoefficients.{b,u,r,max a u r} (X := TopCat.of U) (U.sheafRestrict.obj R)

instance {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X) :
    (liftOpenCoefficients.{a,u,r,b} R U).Additive where
  map_add := by intros; ext V x; rfl

def openAmbientSectionsIso {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X) :
    openSectionsValue.{a} R U ⋙ ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U)) ≅
      liftOpenCoefficients.{a,u,r,b} R U ⋙ openSectionsValue.{max a b} R U :=
  Iso.refl _

set_option maxHeartbeats 1600000 in
def ambientRestrictionIso {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X) :
    originalRestriction.{a} R U ⋙ liftOpenCoefficients.{a,u,r,b} R U ≅
      liftSheafCoefficients.{b,u,r,max a u r} R ⋙ originalRestriction.{max a b} R U :=
  Iso.refl _


/-- The open corresponding to the terminal over-open in the actual subspace. -/
abbrev terminalSubspaceOpen {X : TopCat.{u}} (U : Opens X) : Opens U :=
  U.overEquivalence.functor.obj (Over.mk (𝟙 U))

def terminalSectionRingIso {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X) :
    R.obj.obj (op U) ≅ (U.sheafRestrict.obj R).obj.obj (op (terminalSubspaceOpen U)) :=
  ((CategoryTheory.evaluation _ _).obj (op (Over.mk (𝟙 U)))).mapIso
    ((sheafToPresheaf _ _).mapIso (U.sheafRestrictSheafEquivOver.app R).symm)

def openSectionsEvaluationIso {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X) :
    sectionsValue.{a} (X := TopCat.of U) (U.sheafRestrict.obj R) (terminalSubspaceOpen U) ⋙
      ModuleCat.restrictScalars.{max a u r} (terminalSectionRingIso R U).hom.hom ≅
    openSectionsValue.{a} R U :=
  Iso.refl _


section LocalityComparison

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B]
  [Abelian A] [Abelian A'] [Abelian B] [EnoughInjectives A] [EnoughInjectives A']
  (J : A ⥤ A') [J.Additive] (F : A ⥤ B) [F.Additive] (G : A' ⥤ B) [G.Additive]
  (c : J ⋙ G ≅ F)

/-- The locality isomorphism on every augmented injective model. -/
def IsLocalityComparison (e : ∀ n : ℕ, rightValue F n ≅ J ⋙ rightValue G n) : Prop :=
  ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i),
    (∀ q : ℤ, Injective (I.X q)) →
    ∃ hJi : QuasiIso (mapAugmentation J i),
      (∀ q : ℤ, Injective (J.obj (I.X q))) ∧
      ∀ n : ℕ,
        resolutionModelMap F i hi n ≫ (e n).hom.app M =
          HomologicalComplex.homologyMap
            ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).inv.app I) (n : ℤ) ≫
          resolutionModelMap G (mapAugmentation J i) hJi n

end LocalityComparison

open AdvancedHomologicalAlgebra.SheafTheory in
instance {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X)) : (transportOnOpen.{a} R U).Additive where
  map_add := by intros; ext V x; rfl


open AdvancedHomologicalAlgebra.SheafTheory in
def transportRestrictionTypeValue {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a u r} X)) :
    originalRestriction.{a} R (opensEquiv X U) ⋙ transportOnOpen.{a} R U ≅
      transport.{a} R ⋙ restriction (liftedRing.{a} R) U :=
  openRestrictionComparisonOfOver
    (U.sheafOfModulesEquivOver (liftedRing.{a} R))
    (transportOver.{a} R U) ((opensEquiv X U).sheafOfModulesEquivOver R)
    (SheafOfModules.overFunctor R (opensEquiv X U)) (transport.{a} R ⋙
      SheafOfModules.overFunctor (liftedRing.{a} R) U)
    (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.transportOverRestrictionValue.{a,u,r} X R U)

set_option maxHeartbeats 1600000 in
open AdvancedHomologicalAlgebra.SheafTheory in
/-- Locality commutes with site transport, via the actual restricted model. -/
def localitySiteCoherenceType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens (liftedSpace.{max a u r} X))
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (OpenModules.{a} R (opensEquiv X U))],
    letI := openModulesAbelian.{a} R (opensEquiv X U)
    let V := opensEquiv X U
    let F := sectionsValue.{a} R V
    let F' := openSectionsValue.{a} R V
    let G := sectionsValue.{0} (liftedRing.{a} R) U
    let G' := openSections (liftedRing.{a} R) U
    let S := originalRestriction.{a} R V
    let T := restriction (liftedRing.{a} R) U
    let J := transport.{a} R
    let K := transportOnOpen.{a} R U
    let H := liftedScalars.{a} R U
    ∃ (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n)
      (e' : ∀ n : ℕ, rightValue F' n ⋙ H ≅ K ⋙ rightValue G' n)
      (l : ∀ n : ℕ, rightValue F n ≅ S ⋙ rightValue F' n)
      (l' : ∀ n : ℕ, rightValue G n ≅ T ⋙ rightValue G' n),
      IsResolutionComparison F G J H (siteSectionsIso.{a} R U) e ∧
      IsResolutionComparison F' G' K H (openSiteSectionsIso.{a} R U) e' ∧
      IsLocalityComparison S F F' (sectionsRestrictionValue.{a} R V) l ∧
      IsLocalityComparison T G G' (sectionsRestrictionIso (liftedRing.{a} R) U) l' ∧
      ∀ (M : AmbientSheaves.{a} R) (n : ℕ),
        let f := (rightValue G' n).map ((transportRestrictionTypeValue.{a} R U).hom.app M)
        let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{r,max a u r,max a u r}
          (sectionRingEquiv.{a} R U)
        (H.map ((l n).hom.app M) ≫ (e' n).hom.app (S.obj M) ≫ f =
          (e n).hom.app M ≫ (l' n).hom.app (J.obj M)) ∧
        ((l n).hom.app M ≫ E.counitIso.inv.app ((rightValue F' n).obj (S.obj M)) ≫
          E.functor.map ((e' n).hom.app (S.obj M)) ≫ E.functor.map f =
          (recoverOriginalScalars.{a} R U _ n (e n)).hom.app M ≫
            E.functor.map ((l' n).hom.app (J.obj M)))


set_option maxHeartbeats 1600000 in
/-- Locality commutes with the actual coefficient lift on both the space and
its open subspace. All four comparisons use the same normalized models. -/
def localityAmbientCoherenceType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    [EnoughInjectives (OpenModules.{a} R U)] [EnoughInjectives (OpenModules.{max a b} R U)],
    letI := openModulesAbelian.{a} R U
    letI := openModulesAbelian.{max a b} R U
    let F := sectionsValue.{a} R U
    let F' := openSectionsValue.{a} R U
    let G := sectionsValue.{max a b} R U
    let G' := openSectionsValue.{max a b} R U
    let S := originalRestriction.{a} R U
    let T := originalRestriction.{max a b} R U
    let J := liftSheafCoefficients.{b,u,r,max a u r} R
    let K := liftOpenCoefficients.{a,u,r,b} R U
    let H := ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U))
    ∃ (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n)
      (e' : ∀ n : ℕ, rightValue F' n ⋙ H ≅ K ⋙ rightValue G' n)
      (l : ∀ n : ℕ, rightValue F n ≅ S ⋙ rightValue F' n)
      (l' : ∀ n : ℕ, rightValue G n ≅ T ⋙ rightValue G' n),
      IsResolutionComparison F G J H
        (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{b,u,r,max a u r}
          X R U).symm e ∧
      IsResolutionComparison F' G' K H (openAmbientSectionsIso.{a,u,r,b} R U) e' ∧
      IsLocalityComparison S F F' (sectionsRestrictionValue.{a} R U) l ∧
      IsLocalityComparison T G G' (sectionsRestrictionValue.{max a b} R U) l' ∧
      (∀ (M : AmbientSheaves.{a} R) (I : CochainComplex (AmbientSheaves.{a} R) ℤ)
        [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M ⟶ I)
        (hi : QuasiIso i), (∀ q : ℤ, Injective (I.X q)) →
        ∃ (hiJ : QuasiIso (mapAugmentation J i))
          (hiTJ : QuasiIso (mapAugmentation T (mapAugmentation J i))),
          ∀ n : ℕ, IsIso (resolutionModelMap G (mapAugmentation J i) hiJ n) ∧
            IsIso (resolutionModelMap G' (mapAugmentation T (mapAugmentation J i)) hiTJ n) ∧
            resolutionModelMap G (mapAugmentation J i) hiJ n ≫ (l' n).hom.app (J.obj M) =
              HomologicalComplex.homologyMap
                ((Functor.mapHomologicalComplexCompIso (sectionsRestrictionValue.{max a b} R U)
                  (.up ℤ)).inv.app ((J.mapHomologicalComplex (.up ℤ)).obj I)) (n : ℤ) ≫
              resolutionModelMap G' (mapAugmentation T (mapAugmentation J i)) hiTJ n) ∧
      ∀ (M : AmbientSheaves.{a} R) (n : ℕ),
        H.map ((l n).hom.app M) ≫ (e' n).hom.app (S.obj M) ≫
          (rightValue G' n).map ((ambientRestrictionIso.{a,u,r,b} R U).hom.app M) =
        (e n).hom.app M ≫ (l' n).hom.app (J.obj M)


abbrev abelianCoefficientLift (X : TopCat.{u}) :
    OriginalAbelianSheaves.{a,u,r} X ⥤ OriginalAbelianSheaves.{max a b,u,r} X :=
  sheafCompose (Opens.grothendieckTopology X) AddCommGrpCat.uliftFunctor.{b,max a u r}

instance (X : TopCat.{u}) : (abelianCoefficientLift.{a,u,r,b} X).Additive where
  map_add := by intros; rfl

abbrev abelianCoefficientSectionsIso (X : TopCat.{u}) (U : Opens X) :
    abelianSectionsValue.{a,u,r} X U ⋙ AddCommGrpCat.uliftFunctor.{b,max a u r} ≅
      abelianCoefficientLift.{a,u,r,b} X ⋙ abelianSectionsValue.{max a b,u,r} X U :=
  Iso.refl _

def abelianAmbientComparisonExactType : Prop :=
  ∀ (X : TopCat.{u}) (U : Opens X)
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)]
    [EnoughInjectives (OriginalAbelianSheaves.{max a b,u,r} X)],
    ExactResolutionComparison (abelianSectionsValue.{a,u,r} X U)
      (abelianSectionsValue.{max a b,u,r} X U) (abelianCoefficientLift.{a,u,r,b} X)
      AddCommGrpCat.uliftFunctor.{b,max a u r} (abelianCoefficientSectionsIso.{a,u,r,b} X U)

section AbelianAmbientExt

open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

/-- On the same original open, enlargement identifies the extensions of the
integer unit by their distinguished sections. The map on shifted Hom agrees
with the normalized comparison of right-derived sections. -/
def abelianAmbientExtType : Prop :=
  ∀ (X : TopCat.{u}) (U : Opens (liftedSpace.{max a u r} X))
    (W : Opens (liftedSpace.{max a b u r} X)) (hW : opensEquiv X W = opensEquiv X U)
    (D : IntegerOpenData.{a,u,r} X U) (D' : IntegerOpenData.{max a b,u,r} X W)
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)]
    [EnoughInjectives (OriginalAbelianSheaves.{max a b,u,r} X)],
    let V := opensEquiv X U
    let L := abelianCoefficientLift.{a,u,r,b} X
    let H := AddCommGrpCat.uliftFunctor.{b,max a u r}
    let Γ := abelianSectionsValue.{a,u,r} X V
    let Γ' := abelianSectionsValue.{max a b,u,r} X V
    let P := originalAbelianUnit.{a,u,r} X U D
    let Q := originalAbelianUnit.{max a b,u,r} X W D'
    let s := originalAbelianUnitSection.{a,u,r} X U D
    let t : Γ'.obj Q := Eq.ndrec
      (motive := fun V ↦ ↥((abelianSectionsValue.{max a b,u,r} X V).obj Q))
      (originalAbelianUnitSection.{max a b,u,r} X W D') hW
    let k := abelianCoefficientSectionsIso.{a,u,r,b} X V
    ∃ (hlim : PreservesFiniteLimits L) (hcolim : PreservesFiniteColimits L),
      letI := hlim
      letI := hcolim
      ∃ (q : Q ≅ L.obj P) (c : ∀ n : ℕ, rightValue Γ n ⋙ H ≅ L ⋙ rightValue Γ' n)
        (E : ∀ (M : OriginalAbelianSheaves.{a,u,r} X) (n : ℕ),
          (rightValue Γ n).obj M ≃+ Ext P M (n : ℤ))
        (E' : ∀ (N : OriginalAbelianSheaves.{max a b,u,r} X) (n : ℕ),
          (rightValue Γ' n).obj N ≃+ Ext Q N (n : ℤ)),
        Γ'.map q.hom t = k.hom.app P (ULift.up s) ∧
        IsResolutionComparison Γ Γ' L H k c ∧
        IsSectionsExtModelComparison Γ P s E ∧
        IsSectionsExtModelComparison Γ' Q t E' ∧
        ∀ (M : OriginalAbelianSheaves.{a,u,r} X) (n : ℕ) (x : (rightValue Γ n).obj M),
          E' (L.obj M) n ((c n).hom.app M (ULift.up x)) = extTransportValue L q.hom (E M n x)

end AbelianAmbientExt


/-- The module and abelian ambient comparisons commute through the actual
objectwise lift and the scalar-forget maps. -/
def forgetAmbientCompatibilityType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{a} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    [EnoughInjectives (OriginalAbelianSheaves.{a,u,r} X)]
    [EnoughInjectives (OriginalAbelianSheaves.{max a b,u,r} X)],
    let F := sectionsValue.{a} R U
    let G := sectionsValue.{max a b} R U
    let C := abelianSectionsValue.{a,u,r} X U
    let D := abelianSectionsValue.{max a b,u,r} X U
    let J := liftSheafCoefficients.{b,u,r,max a u r} R
    let E := abelianCoefficientLift.{a,u,r,b} X
    let O := SheafOfModules.toSheaf.{max a u r} R
    let O' := SheafOfModules.toSheaf.{max a b u r} R
    let H := ModuleCat.uliftFunctor.{b,max a u r} (R.obj.obj (op U))
    let B := AddCommGrpCat.uliftFunctor.{b,max a u r}
    let K := forget₂ (SectionModules.{a} R U) AddCommGrpCat.{max a u r}
    let K' := forget₂ (SectionModules.{max a b} R U) AddCommGrpCat.{max a b u r}
    let c := (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{b,u,r,max a u r} X R U).symm
    ∃ (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n)
      (f : ∀ n : ℕ, rightValue F n ⋙ K ≅ O ⋙ rightValue C n)
      (s : ∀ n : ℕ, rightValue C n ⋙ B ≅ E ⋙ rightValue D n)
      (t : ∀ n : ℕ, rightValue G n ⋙ K' ≅ O' ⋙ rightValue D n),
      IsResolutionComparison F G J H c e ∧
      IsResolutionComparison F C O K (Iso.refl _) f ∧
      IsResolutionComparison C D E B (abelianCoefficientSectionsIso.{a,u,r,b} X U) s ∧
      IsResolutionComparison G D O' K' (Iso.refl _) t ∧
      ∀ (M : AmbientSheaves.{a} R) (n : ℕ),
        B.map ((f n).hom.app M) ≫ (s n).hom.app (O.obj M) =
          K'.map ((e n).hom.app M) ≫ (t n).hom.app (J.obj M) ≫
            (rightValue D n).map
              ((Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.forgetAbelianComparisonValue.{b,u,r,max a u r} X R).2.hom.app M)

universe c d e f g w

/-- The coefficient sequence uses the cohomology of the three given sheaves and
its differential is the right-derived boundary of their actual sectionwise maps. -/
def sectionwiseCoefficientLongExactType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{max a b c d} R)]
    (S : SectionwiseShortComplex.{u,r,b,c,d} R),
    S.GermLocallyShortExact →
    let T := S.lift.{a}
    let F := systemValue.{max a b c d} R U
    ∃ hT : T.ShortExact, (∀ n : ℕ,
      ExactPair (F.δ hT n) ((F.value (n + 1)).map T.f) ∧
      ExactPair ((F.value n).map T.f) ((F.value n).map T.g) ∧
      ExactPair ((F.value n).map T.g) (F.δ hT n)) ∧ Mono ((F.value 0).map T.f)

/-- Naturality for diagrams between the original sequences, with no agreement
required between the six coefficient-carrier levels. -/
def sectionwiseCoefficientNaturalityType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{max a b c d e f g} R)]
    (S : SectionwiseShortComplex.{u,r,b,c,d} R) (T : SectionwiseShortComplex.{u,r,e,f,g} R)
    (h : S.Hom T) (hs : S.GermLocallyShortExact) (ht : T.GermLocallyShortExact),
    let h' := h.lift.{a}
    let F := systemValue.{max a b c d e f g} R U
    ∃ (hs' : (S.lift.{max a e f g}).ShortExact) (ht' : (T.lift.{max a b c d}).ShortExact),
      ∀ n : ℕ, (F.value n).map h'.τ₃ ≫ F.δ ht' n =
        F.δ hs' n ≫ (F.value (n + 1)).map h'.τ₁

set_option maxHeartbeats 1200000 in
/-- The same normalized locality isomorphism intertwines the actual right-derived
boundary of the original sequence and that of its restriction to the given open. -/
def sectionwiseLocalityType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{max a b c d} R)]
    [EnoughInjectives (OpenModules.{max a b c d} R U)],
    letI := openModulesAbelian.{max a b c d} R U
    let F := sectionsValue.{max a b c d} R U
    let G := openSectionsValue.{max a b c d} R U
    let J := originalRestriction.{max a b c d} R U
    let c := sectionsRestrictionValue.{max a b c d} R U
    ∃ l : ∀ n : ℕ, rightValue F n ≅ J ⋙ rightValue G n,
      IsLocalityComparison J F G c l ∧
      rightDegreeZeroUnit F ≫ (l 0).hom = c.inv ≫ whiskerLeft J (rightDegreeZeroUnit G) ∧
      ∀ (S : SectionwiseShortComplex.{u,r,b,c,d} R), S.GermLocallyShortExact →
        let T := S.lift.{a}
        ∃ (hT : T.ShortExact) (hJT : (T.map J).ShortExact), ∀ n : ℕ,
          (l n).hom.app T.X₃ ≫ rightBoundary G hJT n =
            rightBoundary F hT n ≫ (l (n + 1)).hom.app T.X₁

set_option maxHeartbeats 1800000 in
/-- Comparison after raising the ambient size on the given sequence. The
short-complex isomorphism flattens the iterated lifts of the original sections. -/
def sectionwiseAmbientComparisonType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{max a b c d} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c d w} R)],
    letI := sectionHasSheafify.{max a b c d r w,u} X
    letI := sectionWEqualsLocallyBijective.{max a b c d r w,u} X
    let J := liftSheafCoefficients.{w,u,r,max a b c d u r} R
    let H := ModuleCat.uliftFunctor.{w,max a b c d u r} (R.obj.obj (op U))
    let F := sectionsValue.{max a b c d} R U
    let G := sectionsValue.{max a b c d w} R U
    let C := Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{w,u,r,max a b c d u r}
      X R U
    ∃ e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n,
      IsResolutionComparison F G J H C.symm e ∧
      whiskerRight (rightDegreeZeroUnit F) H ≫ (e 0).hom =
        C.inv ≫ whiskerLeft J (rightDegreeZeroUnit G) ∧
      ∀ (S : SectionwiseShortComplex.{u,r,b,c,d} R), S.GermLocallyShortExact →
        let T := S.lift.{a}
        let T' := S.lift.{max a w}
        ∃ (k : T.map J ≅ T') (hT : T.ShortExact) (hT' : T'.ShortExact),
          (∀ (V : (Opens X)ᵒᵖ) (x₁ : ((T.map J).X₁).val.obj V)
            (x₂ : ((T.map J).X₂).val.obj V) (x₃ : ((T.map J).X₃).val.obj V),
            k.hom.τ₁.val.app V x₁ = ULift.up x₁.down.down ∧
            k.hom.τ₂.val.app V x₂ = ULift.up x₂.down.down ∧
            k.hom.τ₃.val.app V x₃ = ULift.up x₃.down.down) ∧
          ∀ n : ℕ,
            (e n).hom.app T.X₃ ≫ (rightValue G n).map k.hom.τ₃ ≫ rightBoundary G hT' n =
              H.map (rightBoundary F hT n) ≫ (e (n + 1)).hom.app T.X₁ ≫
                (rightValue G (n + 1)).map k.hom.τ₁

/-- The types of the cohomology comparisons for one original coefficient level. -/
abbrev IndividualCohomologyComparison (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)] :=
  ∀ n : ℕ, (coefficientCohomologyValue.{b} X R U n ⋙
    ModuleCat.uliftFunctor.{a,max b u r} (R.obj.obj (op U))) ≅
    liftSheafCoefficients.{max a b u r,u,r,b} R ⋙ rightValue (sectionsValue.{max a b} R U) n

set_option maxHeartbeats 1800000 in
/-- The cohomology of each original sheaf in its individually adequate category
and in a common larger category is identified through the actual section lift. -/
def IsIndividualCohomologyComparison (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (i : IndividualCohomologyComparison.{a,u,r,b} X R U) : Prop :=
    let J₀ := liftSheafCoefficients.{max u r,u,r,b} R
    let J := liftSheafCoefficients.{a,u,r,max b u r} R
    let J' := liftSheafCoefficients.{max a b u r,u,r,b} R
    let H := ModuleCat.uliftFunctor.{a,max b u r} (R.obj.obj (op U))
    let F := sectionsValue.{b} R U
    let G := sectionsValue.{max a b} R U
    let C := Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{a,u,r,max b u r}
      X R U
    ∃ (k : J₀ ⋙ J ≅ J') (e : ∀ n : ℕ, rightValue F n ⋙ H ≅ J ⋙ rightValue G n),
      (∀ (M : SheafOfModules.{b} R) (V : (Opens X)ᵒᵖ) (s : ((J₀ ⋙ J).obj M).val.obj V),
        (k.hom.app M).val.app V s = ULift.up s.down.down) ∧
      IsResolutionComparison F G J H C.symm e ∧
      whiskerRight (rightDegreeZeroUnit F) H ≫ (e 0).hom =
        C.inv ≫ whiskerLeft J (rightDegreeZeroUnit G) ∧
      ∀ (M : SheafOfModules.{b} R) (n : ℕ),
        (i n).hom.app M =
          (e n).hom.app (J₀.obj M) ≫ (rightValue G n).map (k.hom.app M)

set_option maxHeartbeats 2300000 in
/-- The long exact sequence on the individual cohomologies. Each arrow is
characterized by conjugation to the corresponding actual derived arrow in the
common category, using the normalized comparison for each original sheaf. -/
def sectionwiseIndividualLongExactType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{c} R)]
    [EnoughInjectives (AmbientSheaves.{d} R)] [EnoughInjectives (AmbientSheaves.{max a b c d} R)]
    (S : SectionwiseShortComplex.{u,r,b,c,d} R), S.GermLocallyShortExact →
    let T := S.lift.{a}
    let F := sectionsValue.{max a b c d} R U
    let ring := R.obj.obj (op U)
    let A n := (coefficientCohomologyValue.{b} X R U n).obj S.first
    let B n := (coefficientCohomologyValue.{c} X R U n).obj S.middle
    let D n := (coefficientCohomologyValue.{d} X R U n).obj S.last
    ∃ (hT : T.ShortExact)
      (i₁ : IndividualCohomologyComparison.{max a c d,u,r,b} X R U)
      (i₂ : IndividualCohomologyComparison.{max a b d,u,r,c} X R U)
      (i₃ : IndividualCohomologyComparison.{max a b c,u,r,d} X R U)
      (α : ∀ n : ℕ, A n →ₗ[ring] B n)
      (β : ∀ n : ℕ, B n →ₗ[ring] D n)
      (δ : ∀ n : ℕ, D n →ₗ[ring] A (n + 1)),
      IsIndividualCohomologyComparison X R U i₁ ∧
      IsIndividualCohomologyComparison X R U i₂ ∧
      IsIndividualCohomologyComparison X R U i₃ ∧
      Function.Injective (α 0) ∧
      ∀ n : ℕ,
        Function.Exact (α n) (β n) ∧ Function.Exact (β n) (δ n) ∧
        Function.Exact (δ n) (α (n + 1)) ∧
        (∀ x : A n, (rightValue F n).map T.f ((i₁ n).hom.app S.first (ULift.up x)) =
          (i₂ n).hom.app S.middle (ULift.up (α n x))) ∧
        (∀ x : B n, (rightValue F n).map T.g ((i₂ n).hom.app S.middle (ULift.up x)) =
          (i₃ n).hom.app S.last (ULift.up (β n x))) ∧
        (∀ x : D n, rightBoundary F hT n ((i₃ n).hom.app S.last (ULift.up x)) =
          (i₁ (n + 1)).hom.app S.first (ULift.up (δ n x)))

end Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
