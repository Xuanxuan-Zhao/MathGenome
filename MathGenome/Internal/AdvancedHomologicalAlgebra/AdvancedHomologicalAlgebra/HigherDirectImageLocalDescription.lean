import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FlasqueAcyclicity
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveComplexReplacement
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

noncomputable section
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.HigherDirectImageLocalTheory
open Specs.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
universe u

namespace AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription

theorem pushforwardFlasque : pushforwardFlasqueType.{u} := by
  intro X Y R S f φ F hF V W h
  exact hF ((Opens.map f).obj V) ((Opens.map f).obj W)
    ((Opens.map f).map (homOfLE h)).le

theorem injectivePushforwardFlasque : injectivePushforwardFlasqueType.{u} := by
  intro X Y R S f φ I hI
  exact pushforwardFlasque R S f φ I
    (SheafInjectivesAndRestriction.Expected.injectives_flasque R I hI)

theorem injectivePushforwardAcyclic : injectivePushforwardAcyclicType.{u} := by
  intro X Y R S f φ I hI V n
  letI := HasDerivedCategory.standard (Modules S)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing S V))
  exact FlasqueAcyclicity.flasqueAcyclic S V _ (injectivePushforwardFlasque R S f φ I hI) n

variable {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
  (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)

instance associateAdditive : (associate S).Additive := by
  letI : PreservesBinaryBiproducts (associate S) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Sheafification of the underlying presheaf of a sheaf recovers the sheaf. -/
def forgetAssociateIso : SheafOfModules.forget S ⋙ associate S ≅ 𝟭 (Modules S) :=
  asIso (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).counit

/-- Exact sheafification commutes with cohomology. -/
def sheafifyHomologyIso (K : CochainComplex (Modules S) ℤ) (q : ℤ) :
    (associate S).obj (((SheafOfModules.forget S).mapHomologicalComplex (.up ℤ)).obj K |>.homology q) ≅
      K.homology q := by
  let P := ((SheafOfModules.forget S).mapHomologicalComplex (.up ℤ)).obj K
  exact ((P.sc q).mapHomologyIso (associate S)).symm ≪≫
    (HomologicalComplex.homologyFunctor (Modules S) (.up ℤ) q).mapIso
      ((Functor.mapHomologicalComplexCompIso (forgetAssociateIso S) (.up ℤ)).app K ≪≫
        (Functor.mapHomologicalComplexIdIso (Modules S) (.up ℤ)).app K)

/-- Taking sections of a direct image is taking sections on the inverse image,
with the prescribed restriction of scalars. -/
def directImageEvaluationIso (V : Opens Y) :
    directImage R S f φ ⋙ SheafOfModules.evaluation S (op V) ≅
      SheafOfModules.evaluation R (op ((Opens.map f).obj V)) ⋙
        ModuleCat.restrictScalars (φ.hom.app (op V)).hom := Iso.refl _

theorem localDescriptionOnResolution : localDescriptionOnResolutionType.{u} := by
  intro X Y R S f φ F I hb ι hι hI q
  letI := hb
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (Modules S)
  let D := directImage R S f φ
  let K := (D.mapHomologicalComplex (.up ℤ)).obj I
  let P := ((SheafOfModules.forget S).mapHomologicalComplex (.up ℤ)).obj K
  constructor
  · intro V
    let U := (Opens.map f).obj V
    let E := PresheafOfModules.evaluation S.obj (op V)
    let H := SheafOfModules.evaluation R (op U)
    let T := ModuleCat.restrictScalars (φ.hom.app (op V)).hom
    letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
    obtain ⟨e⟩ := ClassicalDerivedValues.rightComputation
      (Modules R) (ModuleCat.{u} (sectionRing R U)) H F I ι hι hI q
    let e₁ : E.obj (P.homology (q : ℤ)) ≅
        ((E.mapHomologicalComplex (.up ℤ)).obj P).homology (q : ℤ) :=
      ((P.sc (q : ℤ)).mapHomologyIso E).symm
    let e₂ : ((E.mapHomologicalComplex (.up ℤ)).obj P).homology (q : ℤ) ≅
        ((T.mapHomologicalComplex (.up ℤ)).obj
          ((H.mapHomologicalComplex (.up ℤ)).obj I)).homology (q : ℤ) := Iso.refl _
    let J := (H.mapHomologicalComplex (.up ℤ)).obj I
    exact ⟨e₁ ≪≫ e₂ ≪≫ (J.sc (q : ℤ)).mapHomologyIso T ≪≫ T.mapIso e.symm⟩
  · obtain ⟨e⟩ := ClassicalDerivedValues.rightComputation
      (Modules R) (Modules S) D F I ι hι hI q
    exact ⟨e ≪≫ (sheafifyHomologyIso S K (q : ℤ)).symm⟩

theorem localDescription : localDescriptionType.{u} := by
  intro X Y R S f φ F
  obtain ⟨I, ι, _, hι, hI, hb⟩ := InjectiveComplexReplacement.replacement
    (Modules R) ((CochainComplex.singleFunctor (Modules R) 0).obj F) 0 (by infer_instance)
  refine ⟨I, ι, hb, hι, hI, ?_⟩
  letI := hb
  exact localDescriptionOnResolution R S f φ F I ι hι hI

end AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
