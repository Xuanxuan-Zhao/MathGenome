import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicTermComparison

/-! HA-R12. The comparison is induced by the universal property of HA-R05.
On an injective model its component differs from the comparison for G on F(I)
only by invertible factors. HA-R08 gives sufficiency. Essential surjectivity
of the injective models extends this to all of D⁺(A); injective stalks give
necessity. No assumption that F preserves injectives is used. -/
noncomputable section
set_option linter.checkUnivs false
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
open Specs.AdvancedHomologicalAlgebra.RightDerivedComposition

namespace AdvancedHomologicalAlgebra.RightDerivedComposition

def comparison : comparisonDeclarationType := @comparisonValue

theorem comparisonUniversal : comparisonUniversalType := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ F G _ _
  have h := (F ⋙ G).rightDerivedFunctorPlus.rightDerived_fac
    (F ⋙ G).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A)
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) (inputComparisonValue F G)
  refine ⟨h, ?_⟩
  intro α hα
  exact (TotalRightDerivedFunctor.universal A C (F ⋙ G)
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)).1 (hα.trans h.symm)

section
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- On injective models the only possibly noninvertible factor is η_G. -/
lemma comparison_model_iff (I : HomotopyCategory.Plus A)
    (hI : ∀ n : ℤ, Injective (I.obj.as.X n)) :
    IsIso ((comparisonValue F G).app (DerivedCategory.Plus.Qh.obj I)) ↔
      IsIso (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj I)) := by
  have h := congrArg (fun τ => τ.app I) (comparisonUniversal A B C F G).1
  have : IsIso ((F ⋙ G).rightDerivedFunctorPlusUnith.app I) :=
    TotalRightDerivedFunctor.modelComparison A C (F ⋙ G) I hI
  have : IsIso (F.rightDerivedFunctorPlusUnith.app I) :=
    TotalRightDerivedFunctor.modelComparison A B F I hI
  simp only [inputComparisonValue, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id] at h
  rw [← isIso_comp_left_iff ((F ⋙ G).rightDerivedFunctorPlusUnith.app I), h]
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-- Termwise application sends a stalk to the stalk of its image. -/
def mapStalkIso (X : A) :
    F.mapHomotopyCategoryPlus.obj (plusStalkValue X) ≅ plusStalkValue (F.obj X) :=
  (HomotopyCategory.plus B).isoMk
    ((HomotopyCategory.quotient B (.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X))

end

theorem comparisonIsoIff : comparisonIsoIffType := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ F G _ _ _ _
  constructor
  · intro h I hI
    have hs : ∀ n : ℤ, Injective ((plusStalkValue I).obj.as.X n) := by
      intro n
      let _ := hI
      change Injective (((HomologicalComplex.single A (.up ℤ) 0).obj I).X n)
      infer_instance
    have hm := (comparison_model_iff F G (plusStalkValue I) hs).mp
      (h (DerivedCategory.Plus.Qh.obj (plusStalkValue I)))
    exact (NatTrans.isIso_app_iff_of_iso G.rightDerivedFunctorPlusUnith
      (mapStalkIso F I)).mp hm
  · intro h X
    have hm (I : HomotopyCategory.Plus A)
        (hI : ∀ n : ℤ, Injective (I.obj.as.X n)) :
        IsIso ((comparisonValue F G).app (DerivedCategory.Plus.Qh.obj I)) := by
      apply (comparison_model_iff F G I hI).mpr
      apply AcyclicTermComparison.rightComparison B C G
      intro n
      exact h (I.obj.as.X n) (hI n)
    let J := (InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
    apply (NatTrans.isIso_app_iff_of_iso (comparisonValue F G)
      (J.objObjPreimageIso X)).mp
    exact hm ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj (J.objPreimage X))
      (fun n => inferInstance)

end AdvancedHomologicalAlgebra.RightDerivedComposition
