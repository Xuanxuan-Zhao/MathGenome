import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Permanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Permanence

/-! The permanence part of ET-04. We combine finite-presentation
permanence with the square-zero lifting results FL-09 and FL-10.
No nontriviality or restriction on the element being inverted is needed.
-/
namespace AdvCommAlg.Etale

universe u v w

open scoped TensorProduct
open Specs.AdvCommAlg.Etale.Permanence

theorem etale_base_change : etaleBaseChange.{u,v,w} := by
  intro A B A' _ _ _ _ _ h
  obtain ⟨hfp, hformal⟩ := (etale_iff A B).mp h
  let : Algebra.FinitePresentation A B := hfp
  apply (etale_iff A' (A' ⊗[A] B)).mpr
  exact ⟨inferInstance, FormalLifting.etale_base_change A B A' hformal⟩

theorem etale_composition : etaleComposition.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ hAB hBC
  obtain ⟨hfpAB, hformalAB⟩ := (etale_iff A B).mp hAB
  obtain ⟨hfpBC, hformalBC⟩ := (etale_iff B C).mp hBC
  let : Algebra.FinitePresentation A B := hfpAB
  let : Algebra.FinitePresentation B C := hfpBC
  apply (etale_iff A C).mpr
  exact ⟨Algebra.FinitePresentation.trans A B C,
    FormalLifting.etale_composition A B C hformalAB hformalBC⟩

theorem etale_target_localization : etaleTargetLocalization.{u,v,w} := by
  intro A B L _ _ _ _ _ _ _ b _ h
  obtain ⟨hfp, hformal⟩ := (etale_iff A B).mp h
  let : Algebra.FinitePresentation A B := hfp
  apply (etale_iff A L).mpr
  exact ⟨Algebra.FinitePresentation.of_isLocalizationAway b,
    FormalLifting.etale_target_localization A B L (Submonoid.powers b) hformal⟩

theorem etale_localization_away : etaleLocalizationAway.{u,v} := by
  intro A B _ _ _ b h
  exact etale_target_localization A B (Localization.Away b) b h

end AdvCommAlg.Etale
