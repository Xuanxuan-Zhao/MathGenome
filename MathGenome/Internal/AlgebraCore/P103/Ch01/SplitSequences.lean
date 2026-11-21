import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.SplitSequences

namespace P103.Ch01.SplitSequences

open P103.Specs.Ch01.SplitSequences

theorem section_iff_retraction : section_iff_retractionType := by
  intro R A B C _ _ _ _ _ _ _ i p hi hp h
  exact (h.split_tfae hi hp).out 1 2

theorem section_iff_sequenceIsomorphism : section_iff_sequenceIsomorphismType := by
  intro R A B C _ _ _ _ _ _ _ i p hi hp h
  exact (h.split_tfae hi hp).out 1 3

noncomputable def splitting : splittingType := splittingValue

theorem splitting_apply : splitting_applyType := by
  intro R A B C _ _ _ _ _ _ _ i p hi h s hs a c
  rfl

theorem residual_mem_range : residual_mem_rangeType := by
  intro R A B C _ _ _ _ _ _ _ i p h s hs b
  apply (h _).mp
  have hs' : ∀ c, p (s c) = c := LinearMap.congr_fun hs
  simp [map_sub, hs']

noncomputable def inverseOnImage : inverseOnImageType := inverseOnImageValue

theorem splitting_inverse_formula : splitting_inverse_formulaType := by
  intro R A B C _ _ _ _ _ _ _ i p hi h s hs b hb
  apply (splittingValue R A B C i p hi h s hs).injective
  rw [LinearEquiv.apply_symm_apply, splitting_apply]
  have hx : i (inverseOnImageValue R A B i hi ⟨b - s (p b), hb⟩) =
      b - s (p b) := by
    exact congrArg Subtype.val ((LinearEquiv.ofInjective i hi).apply_symm_apply
      ⟨b - s (p b), hb⟩)
  rw [hx, sub_add_cancel]

theorem splitting_mutualInverse : splitting_mutualInverseType := by
  intro R A B C _ _ _ _ _ _ _ i p hi h s hs
  exact ⟨(splittingValue R A B C i p hi h s hs).left_inv,
    (splittingValue R A B C i p hi h s hs).right_inv⟩

end P103.Ch01.SplitSequences
