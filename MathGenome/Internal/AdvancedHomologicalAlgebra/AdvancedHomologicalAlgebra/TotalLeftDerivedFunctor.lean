import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ProjectiveComplexReplacement
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.KModelMorphisms
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
HA-R07. The full subcategory of bounded above K-projectives is equivalent to
D⁻ by projective replacement and orthogonality to acyclics. Its inverse,
followed by inclusion into K⁻, is left adjoint to Q⁻: the adjunction bijection
is precisely localization on maps from K-projectives. Whiskering this
adjunction gives the R05 counit and its universal property for every functor
H. The adjoint shift structure makes the counit commute with the standard
cochain shifts; the left adjoint of the exact Q⁻ is exact. Composition with
termwise F and Q⁻_B therefore constructs the required exact LF.

The use of K-projectives instead of termwise projectives is an equivalent
complete construction: every bounded above termwise projective is a model,
and the comparison is invertible on all of them. The final computation and
transformation formulas quantify over every such model and every replacement.
-/

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u w' v' u'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels

namespace AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Bounded above K-projective objects, expressed by the acyclic orthogonal. -/
def models : ObjectProperty (KMinus A) :=
  (HomotopyCategory.subcategoryAcyclic A).leftOrthogonal.inverseImage (minusInclusion A)

abbrev Models := (models A).FullSubcategory
abbrev modelInclusion : Models A ⥤ KMinus A := (models A).ι

lemma projective_mem (P : KMinus A) (hP : ∀ n : ℤ, Projective (P.obj.as.X n)) :
    models A P := by
  obtain ⟨b, hb⟩ := P.property
  let : CochainComplex.IsStrictlyLE P.obj.as b := hb
  let : ∀ n : ℤ, Projective (P.obj.as.X n) := hP
  let := CochainComplex.isKProjective_of_projective P.obj.as b
  exact CochainComplex.IsKProjective.leftOrthogonal P.obj.as

variable [HasDerivedCategory.{w} A]

/-- Localization on maps out of a model is a bijection, even for arbitrary targets. -/
lemma model_map_bijective (P : Models A) (X : KMinus A) :
    Function.Bijective ((QMinus A).map : (P.obj ⟶ X) → _) := by
  have h := P.property.map_bijective_of_isTriangulated
    (DerivedCategory.Qh (C := A)) X.obj
  constructor
  · intro f g hfg
    apply (minusInclusion A).map_injective
    apply h.injective
    exact congrArg (fun f => f.hom) hfg
  · intro f
    obtain ⟨g, hg⟩ := h.surjective f.hom
    exact ⟨(minus A).homMk g, by ext : 1; exact hg⟩

noncomputable abbrev modelLocalization : Models A ⥤ DerivedCategory.Minus A :=
  modelInclusion A ⋙ QMinus A

instance modelLocalizationFull : (modelLocalization A).Full where
  map_surjective f := by
    obtain ⟨g, hg⟩ := (model_map_bijective A _ _).surjective f
    exact ⟨(models A).homMk g, hg⟩

instance modelLocalizationFaithful : (modelLocalization A).Faithful where
  map_injective h := by
    ext : 1
    exact (model_map_bijective A _ _).injective h

variable [EnoughProjectives A]

instance modelLocalizationEssSurj : (modelLocalization A).EssSurj where
  mem_essImage X := by
    obtain ⟨b, P, hb, hP, ⟨e⟩⟩ := ProjectiveComplexReplacement.derivedRepresentative A X
    let P' : KMinus A := ⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, b, hb⟩
    refine ⟨⟨P', projective_mem A P' hP⟩, ⟨?_⟩⟩
    exact DerivedCategory.Minus.ι.preimageIso
      ((DerivedCategory.quotientCompQhIso A).symm.app P ≪≫ e.symm)

instance modelLocalizationIsEquivalence : (modelLocalization A).IsEquivalence := {}

noncomputable abbrev modelEquivalence : Models A ≌ DerivedCategory.Minus A :=
  (modelLocalization A).asEquivalence

noncomputable abbrev resolution : DerivedCategory.Minus A ⥤ KMinus A :=
  (modelEquivalence A).inverse ⋙ modelInclusion A

noncomputable abbrev resolutionHomEquiv (X : DerivedCategory.Minus A) (Y : KMinus A) :
    ((resolution A).obj X ⟶ Y) ≃ (X ⟶ (QMinus A).obj Y) :=
  (Equiv.ofBijective _ (model_map_bijective A _ Y)).trans
    (Iso.homFromEquiv ((modelEquivalence A).counitIso.app X))

noncomputable def resolutionAdjunction : resolution A ⊣ QMinus A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := resolutionHomEquiv A
      homEquiv_naturality_left_symm := by
        intro X X' Y f g
        apply (resolutionHomEquiv A X Y).injective
        rw [Equiv.apply_symm_apply]
        change f ≫ g = (modelEquivalence A).counitIso.inv.app X ≫
          (QMinus A).map ((resolution A).map f ≫ (resolutionHomEquiv A X' Y).symm g)
        rw [Functor.map_comp]
        have h := (modelEquivalence A).counitIso.inv.naturality f
        change f ≫ (modelEquivalence A).counitIso.inv.app X' =
          (modelEquivalence A).counitIso.inv.app X ≫ (QMinus A).map ((resolution A).map f) at h
        rw [← Category.assoc, ← h, Category.assoc]
        exact congrArg (f ≫ ·) (Equiv.apply_symm_apply (resolutionHomEquiv A X' Y) g).symm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        change (modelEquivalence A).counitIso.inv.app X ≫ (QMinus A).map (f ≫ g) =
          ((modelEquivalence A).counitIso.inv.app X ≫ (QMinus A).map f) ≫ (QMinus A).map g
        rw [Functor.map_comp, Category.assoc] }

instance resolutionFull : (resolution A).Full := by dsimp [resolution]; infer_instance
instance resolutionFaithful : (resolution A).Faithful := by dsimp [resolution]; infer_instance

lemma resolution_counit_iso (P : Models A) :
    IsIso ((resolutionAdjunction A).counit.app P.obj) :=
  (resolutionAdjunction A).isIso_counit_app_of_iso
    ((modelInclusion A).mapIso ((modelEquivalence A).unitIso.app P))

open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty

section Exactness
variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]

noncomputable instance termwiseMinusShift (F : A ⥤ B) [F.Additive] :
    (termwiseMinusValue F).CommShift ℤ := termwiseShift F

instance termwiseMinusTriangulated (F : A ⥤ B) [F.Additive] :
    (termwiseMinusValue F).IsTriangulated := by
  dsimp [termwiseMinusValue]
  infer_instance

noncomputable def derivedCounit (F : A ⥤ B) [F.Additive] :
    QMinus A ⋙ (resolution A ⋙ minusUValue F) ⟶ minusUValue F :=
  (associator _ _ _).inv ≫ whiskerRight (resolutionAdjunction A).counit _ ≫
    (leftUnitor _).hom

/-- Whiskering the resolution adjunction proves the full R05 universal property. -/
lemma derivedUniversal (F : A ⥤ B) [F.Additive] (H : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) :
    Function.Bijective (fun α : H ⟶ resolution A ⋙ minusUValue F =>
      whiskerLeft (QMinus A) α ≫ derivedCounit A F) := by
  exact (((resolutionAdjunction A).whiskerLeft (DerivedCategory.Minus B)).homEquiv H
    (minusUValue F)).symm.bijective

lemma derivedCounit_model_iso (F : A ⥤ B) [F.Additive] (P : KMinus A)
    (hP : ∀ n : ℤ, Projective (P.obj.as.X n)) :
    IsIso ((derivedCounit A F).app P) := by
  have := resolution_counit_iso A ⟨P, projective_mem A P hP⟩
  dsimp [derivedCounit]
  infer_instance

end Exactness

theorem existence : existenceType := by
  intro A B _ _ _ _ _ _ _ F _
  refine ⟨inferInstance, inferInstance, ?_⟩
  let : (QMinus A).CommShift ℤ := quotientShift
  let : (QMinus B).CommShift ℤ := quotientShift
  let : (minusUValue F).CommShift ℤ := inputShift F
  let : (resolution A).CommShift ℤ := (resolutionAdjunction A).leftAdjointCommShift ℤ
  let : (resolutionAdjunction A).CommShift ℤ :=
    (resolutionAdjunction A).commShift_of_rightAdjoint ℤ
  let : (resolution A).IsTriangulated := (resolutionAdjunction A).isTriangulated_leftAdjoint
  have : (minusUValue F).IsTriangulated := by
    dsimp only [minusUValue]
    infer_instance
  exact ⟨{
    functor := resolution A ⋙ minusUValue F
    counit := derivedCounit A F
    universal := derivedUniversal A F
    commShift := inferInstance
    triangulated := inferInstance
    counit_shift := by dsimp [derivedCounit]; infer_instance
    model_iso := derivedCounit_model_iso A F }⟩

/-- The formula applies to every projective quasi-isomorphism, not just the
chosen representative used to construct the adjunction. -/
theorem computation : computationType := by
  intro A B _ _ _ _ _ _ hA hB F _ R P X p hP hp
  let := hA
  let := hB
  have : IsIso ((QMinus A).map p) := Localization.inverts (QMinus A) (WMinus A) p hp
  have := R.model_iso P hP
  let e := (R.functor.mapIso (asIso ((QMinus A).map p))).symm ≪≫
    asIso (R.counit.app P)
  refine ⟨e, ?_, ?_⟩
  · dsimp [e]
    rw [Category.assoc, ← R.counit.naturality p]
    simp
  · simp [e]

theorem transformations : transformationsType := by
  intro A B _ _ _ _ _ _ hA hB F G _ _ R S τ
  let := hA
  let := hB
  exact TotalDerivedUniversalProperty.leftOriginalMap A B F G R.toLeftData S.toLeftData τ

theorem transformationModels : transformationModelsType := by
  intro A B _ _ _ _ _ _ hA hB F G _ _ R S τ α h P hP
  let := hA
  let := hB
  have := S.model_iso P hP
  rw [← cancel_mono (S.counit.app P)]
  simpa using congr_app h P

end AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
