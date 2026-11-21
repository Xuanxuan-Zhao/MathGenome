import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FlasqueAcyclicity
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! HA-H01: source 3558–3603, with ringed-space conventions 3525–3556.
All definitions use the standard derived-category models, so no extra
existence or smallness assumption is imposed on the ringed space. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
universe u v w w'

namespace AdvancedHomologicalAlgebra.SheafTheory

/-- Derived sections on X, with their full R(U)-module structure. -/
def sectionCohomology {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) (n : ℕ) :
    Modules R ⥤ ModuleCat.{u} (sectionRing R U) := by
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
  exact rightValue (SheafOfModules.evaluation R (op U)) n

/-- The connecting maps are those of the derived short exact sequence. -/
def sectionCohomologySystem {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) :
    CohomologicalSystem (Modules R) (ModuleCat.{u} (sectionRing R U)) := by
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
  exact rightSystem (SheafOfModules.evaluation R (op U))

/-- Sections on the actual open subspace, using its equivalent over-site
presentation. The terminal over-open is U itself, so scalars are R(U). -/
def openSections {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) :
    SheafOfModules.{u} (U.sheafRestrict.obj R) ⥤ ModuleCat.{u} (sectionRing R U) :=
  (U.sheafOfModulesEquivOver R).inverse ⋙
    SheafOfModules.evaluation (R.over U) (op (Over.mk (𝟙 U)))

/-- Evaluation on the terminal over-open identifies sections after restriction
with the original sections. The inverse unit of the open-site equivalence
removes the passage through the actual open subspace. -/
def sectionsRestrictionIso {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) :
    restriction R U ⋙ openSections R U ≅ SheafOfModules.evaluation R (op U) := by
  let E := U.sheafOfModulesEquivOver R
  let F := SheafOfModules.overFunctor R U
  let Γ := SheafOfModules.evaluation (R.over U) (op (Over.mk (𝟙 U)))
  exact (Functor.associator (F ⋙ E.functor) E.inverse Γ).symm ≪≫
    isoWhiskerRight (Functor.associator F E.functor E.inverse ≪≫
      isoWhiskerLeft F E.unitIso.symm ≪≫ Functor.rightUnitor F) Γ

instance restrictionAdditive {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) :
    (restriction R U).Additive :=
  by
    letI : PreservesBinaryBiproducts (restriction R U) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _

instance openSectionsAdditive {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) :
    (openSections R U).Additive where
  map_add := by intros; ext x; rfl

/-- The right-derived sections functor on U, applied after restriction. -/
def openCohomology {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) (n : ℕ) :
    Modules R ⥤ ModuleCat.{u} (sectionRing R U) := by
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (U.sheafRestrict.obj R))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
  exact restriction R U ⋙ rightValue (openSections R U) n

/-- Ordinary abelian sheaves on X. -/
abbrev AbelianSheaves (X : TopCat.{u}) :=
  Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- The ordinary abelian section functor. -/
def abelianSections (X : TopCat.{u}) (U : Opens X) :
    AbelianSheaves X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

instance abelianSectionsAdditive (X : TopCat.{u}) (U : Opens X) :
    (abelianSections X U).Additive where
  map_add := by intros; rfl

/-- Ordinary cohomology of abelian sheaves, as right-derived sections. -/
def abelianCohomology (X : TopCat.{u}) (U : Opens X) (n : ℕ) :
    AbelianSheaves X ⥤ AddCommGrpCat.{u} := by
  letI := HasDerivedCategory.standard (AbelianSheaves X)
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  exact rightValue (abelianSections X U) n

/-- Extension by zero of the unit on U for the constant integer ring sheaf,
then forgetting the integer-module structure. This is j_! Z_U. -/
def abelianOpenUnit (X : TopCat.{u}) (U : Opens X) : AbelianSheaves X :=
  (SheafOfModules.toSheaf (constantIntegerRingSheaf X)).obj
    (openUnit (constantIntegerRingSheaf X) U)

/-- The actual shifted-Hom model of Ext in the abelian-sheaf category. -/
abbrev abelianExt (X : TopCat.{u}) (U : Opens X) (F : AbelianSheaves X) (n : ℕ) := by
  letI := HasDerivedCategory.standard (AbelianSheaves X)
  exact Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext (abelianOpenUnit X U) F (n : ℤ)

end AdvancedHomologicalAlgebra.SheafTheory

namespace Specs.AdvancedHomologicalAlgebra.SheafCohomology

def cohomologyType := ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) (n : ℕ),
  Modules R ⥤ ModuleCat.{u} (sectionRing R U)
def cohomologyValue : cohomologyType := @sectionCohomology

/-- Every ordinary injective resolution on X computes H^n(U,-). -/
def resolutionType : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) (M : Modules R)
    (I : CochainComplex (Modules R) ℤ) [I.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I),
    QuasiIso ι → (∀ q : ℤ, Injective (I.X q)) → ∀ n : ℕ,
    Nonempty ((sectionCohomology R U n).obj M ≅
      (((SheafOfModules.evaluation R (op U)).mapHomologicalComplex (.up ℤ)).obj I).homology
        (n : ℤ))

/-- The degree-zero identification is the inverse of the actual derived unit
on the stalk complex. -/
def zeroType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
  ∃ e : sectionCohomology R U 0 ≅ SheafOfModules.evaluation R (op U),
    e.inv = rightDegreeZeroUnit (SheafOfModules.evaluation R (op U))

def longExactType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
  IsCohomological (sectionCohomologySystem R U)

def flasqueType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X)
    (M : Modules R), IsFlasque R M → ∀ n : ℕ,
  IsZero ((sectionCohomology R U (n + 1)).obj M)

end Specs.AdvancedHomologicalAlgebra.SheafCohomology

namespace Specs.AdvancedHomologicalAlgebra.SheafCohomology

/-- The canonical section identification, over the original section ring. -/
def sectionsRestrictionType :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
    restriction R U ⋙ openSections R U ≅ SheafOfModules.evaluation R (op U)

def sectionsRestrictionValue : sectionsRestrictionType := @sectionsRestrictionIso

end Specs.AdvancedHomologicalAlgebra.SheafCohomology

namespace Specs.AdvancedHomologicalAlgebra.SheafCohomology

attribute [local instance] HasDerivedCategory.standard

open CochainComplex CochainComplex.HomComplex
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

/-- Map from the cohomology of an augmented model to the right-derived value.
It uses the actual unit on the model and the inverse of the localized
augmentation. For an acyclic model this map is an isomorphism. -/
def resolutionModelMap {A : Type u} {B : Type v} [Category.{w} A] [Category.{w'} B]
    [Abelian A] [Abelian B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hι : QuasiIso ι) (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj I).homology (n : ℤ) ⟶ (rightValue F n).obj M := by
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let L : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  let q : L ⟶ K := ObjectProperty.homMk ι
  haveI : IsIso (DerivedCategory.Plus.Q.map q) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A) q hι
  exact (DerivedCategory.homologyFunctorFactors B (n : ℤ)).inv.app _ ≫
    (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
      (F.rightDerivedFunctorPlusUnit.app K ≫ F.rightDerivedFunctorPlus.map
        (inv (DerivedCategory.Plus.Q.map q)))

/-- The restricted augmentation, with the canonical comparison of the
restricted stalk with the stalk of the restricted coefficient. -/
def restrictedAugmentation {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X)
    {M : Modules R} {I : CochainComplex (Modules R) ℤ}
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I) :
    (CochainComplex.singleFunctor _ 0).obj ((restriction R U).obj M) ⟶
      (((restriction R U).mapHomologicalComplex (.up ℤ)).obj I) :=
  ((restriction R U).mapCochainComplexSingleFunctor 0).inv.app M ≫
    ((restriction R U).mapHomologicalComplex (.up ℤ)).map ι

/-- The comparison is induced on each augmented injective resolution and its
actual restriction, using the termwise section identification. Its degree-zero
and coefficient boundary maps are those of the two derived functors. -/
def localityType : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
    let Γ := SheafOfModules.evaluation R (op U)
    let J := restriction R U
    let ΓU := openSections R U
    ∃ e : ∀ n : ℕ, sectionCohomology R U n ≅ openCohomology R U n,
      rightDegreeZeroUnit Γ ≫ (e 0).hom =
        (sectionsRestrictionIso R U).inv ≫ whiskerLeft J (rightDegreeZeroUnit ΓU) ∧
      (∀ (S : ShortComplex (Modules R)) (hS : S.ShortExact),
        ∃ hJS : (S.map J).ShortExact, ∀ n : ℕ,
          (e n).hom.app S.X₃ ≫ rightBoundary ΓU hJS n =
            rightBoundary Γ hS n ≫ (e (n + 1)).hom.app S.X₁) ∧
      ∀ (M : Modules R) (I : CochainComplex (Modules R) ℤ) [I.IsStrictlyGE 0]
        (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I)
        (hι : QuasiIso ι), (∀ q : ℤ, Injective (I.X q)) →
        ∃ hJι : QuasiIso (restrictedAugmentation R U ι),
          (∀ q : ℤ, Injective (J.obj (I.X q))) ∧
          ∀ n : ℕ,
            let comparison : (Γ.mapHomologicalComplex (.up ℤ)).obj I ⟶
                (ΓU.mapHomologicalComplex (.up ℤ)).obj
                  ((J.mapHomologicalComplex (.up ℤ)).obj I) :=
              (Functor.mapHomologicalComplexCompIso (sectionsRestrictionIso R U)
                (.up ℤ)).inv.app I
            resolutionModelMap Γ ι hι n ≫ (e n).hom.app M =
              HomologicalComplex.homologyMap comparison (n : ℤ) ≫
                resolutionModelMap ΓU (restrictedAugmentation R U ι) hJι n

/-- The comparison on sections before deriving is the identity of additive groups. -/
def forgetSectionsIso {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) :
    SheafOfModules.evaluation R (op U) ⋙
      forget₂ (ModuleCat.{u} (sectionRing R U)) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf R ⋙ abelianSections X U :=
  Iso.refl _

/-- The augmentation after forgetting scalars, including the canonical
identification of the two stalk complexes. -/
def forgottenAugmentation {X : TopCat.{u}} (R : RingSheaf X) {M : Modules R}
    {I : CochainComplex (Modules R) ℤ}
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I) :
    (CochainComplex.singleFunctor (AbelianSheaves X) 0).obj ((SheafOfModules.toSheaf R).obj M) ⟶
      ((SheafOfModules.toSheaf R).mapHomologicalComplex (.up ℤ)).obj I :=
  ((SheafOfModules.toSheaf R).mapCochainComplexSingleFunctor 0).inv.app M ≫
    ((SheafOfModules.toSheaf R).mapHomologicalComplex (.up ℤ)).map ι

/-- The module-injective resolution becomes a flasque abelian resolution. -/
def forgottenResolutionType : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (M : Modules R)
    (I : CochainComplex (Modules R) ℤ) [I.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I),
    QuasiIso ι → (∀ q : ℤ, Injective (I.X q)) →
    QuasiIso (forgottenAugmentation R ι) ∧
    (∀ q : ℤ, TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj (I.X q)))

/-- Forgetting scalars identifies the two derived section functors in each
degree. The isomorphism intertwines the actual resolution-model maps on
every module-injective resolution and its forgotten flasque resolution. -/
def forgetType : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
    let Γ := SheafOfModules.evaluation R (op U)
    let F := SheafOfModules.toSheaf R
    let G := forget₂ (ModuleCat.{u} (sectionRing R U)) AddCommGrpCat.{u}
    ∃ e : ∀ n : ℕ, sectionCohomology R U n ⋙ G ≅ F ⋙ abelianCohomology X U n,
      ∀ (M : Modules R) (I : CochainComplex (Modules R) ℤ) [I.IsStrictlyGE 0]
        (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I)
        (hι : QuasiIso ι), (∀ q : ℤ, Injective (I.X q)) →
        ∃ hFι : QuasiIso (forgottenAugmentation R ι), ∀ n : ℕ,
          let K := (Γ.mapHomologicalComplex (.up ℤ)).obj I
          let comparison : (G.mapHomologicalComplex (.up ℤ)).obj K ⟶
              ((abelianSections X U).mapHomologicalComplex (.up ℤ)).obj
                ((F.mapHomologicalComplex (.up ℤ)).obj I) :=
            (Functor.mapHomologicalComplexCompIso (forgetSectionsIso R U) (.up ℤ)).inv.app I
          ((K.sc (n : ℤ)).mapHomologyIso G).hom ≫
              G.map (resolutionModelMap Γ ι hι n) ≫ (e n).hom.app M =
            HomologicalComplex.homologyMap comparison (n : ℤ) ≫
              resolutionModelMap (abelianSections X U) (forgottenAugmentation R ι) hFι n

/-- The universal section of the open unit is the image of 1 under the
unit of the extension-by-zero/restriction adjunction. -/
def abelianOpenUnitSection (X : TopCat.{u}) (U : Opens X) :
    (abelianSections X U).obj (abelianOpenUnit X U) :=
  openUnitGenerator (constantIntegerRingSheaf X) U

/-- The free abelian open unit represents sections by evaluation at its
universal section. -/
def abelianOpenUnitType : Prop := ∀ (X : TopCat.{u}) (U : Opens X),
  ∃ e : preadditiveCoyoneda.obj (op (abelianOpenUnit X U)) ≅ abelianSections X U,
    ∀ (F : AbelianSheaves X) (f : abelianOpenUnit X U ⟶ F),
      e.hom.app F f = (abelianSections X U).map f (abelianOpenUnitSection X U)

/-- The Ext comparison on every augmented injective resolution agrees with
evaluation in each cochain degree and the actual map of the resulting
cohomology class into shifted derived Hom. -/
def extType : Prop := ∀ (X : TopCat.{u}) (U : Opens X),
  let Γ := abelianSections X U
  let A := abelianOpenUnit X U
  ∃ e : ∀ (F : AbelianSheaves X) (n : ℕ),
    ((abelianCohomology X U n).obj F) ≃+ abelianExt X U F n,
    (∀ (F G : AbelianSheaves X) (f : F ⟶ G) (n : ℕ)
      (x : (abelianCohomology X U n).obj F),
      e G n ((abelianCohomology X U n).map f x) =
        extMap (𝟙 A) f (n : ℤ) (e F n x)) ∧
    ∀ (F : AbelianSheaves X) (I : CochainComplex (AbelianSheaves X) ℤ) [I.IsStrictlyGE 0]
      (ι : (CochainComplex.singleFunctor (AbelianSheaves X) 0).obj F ⟶ I)
      (hι : QuasiIso ι), (∀ q : ℤ, Injective (I.X q)) →
      let L := (CochainComplex.singleFunctor (AbelianSheaves X) 0).obj A
      ∃ c : HomComplex L I ≅ (Γ.mapHomologicalComplex (.up ℤ)).obj I,
        (∀ (q : ℤ) (f : Cochain L I q),
          c.hom.f q f = Γ.map (Cochain.fromSingleEquiv (zero_add q) f)
            (abelianOpenUnitSection X U)) ∧
        ∀ (n : ℕ) (x : CohomologyClass L I (n : ℤ)),
          e F n (resolutionModelMap Γ ι hι n
            (HomologicalComplex.homologyMap c.hom (n : ℤ)
              ((HomComplex.homologyAddEquiv L I (n : ℤ)).symm x))) =
            injectiveClassMap A F I ι hι (n : ℤ) x

end Specs.AdvancedHomologicalAlgebra.SheafCohomology
