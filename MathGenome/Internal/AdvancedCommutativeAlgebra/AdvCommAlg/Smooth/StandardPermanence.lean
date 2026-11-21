import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.StandardPresentation
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.StandardPermanence

/-! Permanence of standard smoothness and of the counts of displayed
presentations (SM-11). -/
namespace AdvCommAlg.Smooth

universe u v w
noncomputable section
open Specs.AdvCommAlg.Smooth

theorem standard_smooth_composition : standardSmoothComposition.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ hP hQ
  haveI : Algebra.IsStandardSmooth A B := hP
  haveI : Algebra.IsStandardSmooth B C := hQ
  exact Algebra.IsStandardSmooth.trans A B C

theorem standard_smooth_base_change : standardSmoothBaseChange.{u,v,w} := by
  intro A B T _ _ _ _ _ hP
  haveI : Algebra.IsStandardSmooth A B := hP
  exact Algebra.IsStandardSmooth.baseChange T

theorem standard_smooth_target_localization : standardSmoothTargetLocalization.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ g _ hP
  haveI : Algebra.IsStandardSmooth A B := hP
  haveI := Algebra.IsStandardSmooth.localization_away (S := C) g
  exact Algebra.IsStandardSmooth.trans A B C

theorem composition_presentation : compositionPresentation.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ n c m d P Q hP hQ
  have hc := presentation_standard_smooth_bounds P hP
  have hd := presentation_standard_smooth_bounds Q hQ
  obtain ⟨P', rfl⟩ := (presentation_standard_smooth_iff_submersive P).mp hP
  obtain ⟨Q', rfl⟩ := (presentation_standard_smooth_iff_submersive Q).mp hQ
  constructor
  · apply (presentation_standard_smooth_iff_submersive _).mpr
    exact ⟨(Q'.comp P').reindex finSumFinEquiv.symm finSumFinEquiv.symm, rfl⟩
  · simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    omega

theorem base_change_presentation : baseChangePresentation.{u,v,w} := by
  intro A B T _ _ _ _ _ n c P hP
  obtain ⟨P', rfl⟩ := (presentation_standard_smooth_iff_submersive P).mp hP
  constructor
  · apply (presentation_standard_smooth_iff_submersive _).mpr
    exact ⟨P'.baseChange T, rfl⟩
  · simp [Algebra.Presentation.dimension]

theorem target_localization_presentation : targetLocalizationPresentation.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ g _ n c P hP
  obtain ⟨P', rfl⟩ := (presentation_standard_smooth_iff_submersive P).mp hP
  constructor
  · apply (presentation_standard_smooth_iff_submersive _).mpr
    exact ⟨((Algebra.SubmersivePresentation.localizationAway C g).comp P').reindex
      (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _)))
      (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _))), rfl⟩
  · simp [Algebra.Presentation.dimension, Nat.add_sub_add_left]

end
end AdvCommAlg.Smooth
