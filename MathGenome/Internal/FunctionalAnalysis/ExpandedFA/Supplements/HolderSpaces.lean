import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.HolderSpaces

/-! Function spaces and their exact norms for paper.tex:5802–5839.
The canonical definitions are in the independent Specs so downstream files
can use the same objects. No completeness assertion is assumed here. -/
noncomputable section
open Set
open scoped NNReal
namespace ExpandedFA.Supplements

abbrev Cm := @HolderSpacesSpec.Cm
abbrev CmHolder := @HolderSpacesSpec.CmHolder
abbrev BoundedHolder := @HolderSpacesSpec.BoundedHolder
abbrev holderSeminorm := @HolderSpacesSpec.holderSeminorm
abbrev intervalDerivative := @HolderSpacesSpec.Cm.derivative

open HolderSpacesSpec

theorem cm_norm_formula : CmNormFormula := by
  intro 𝕜 _ m a b hab f
  rfl

theorem cm_holder_norm_formula : CmHolderNormFormula := by
  intro 𝕜 _ m a b hab α f
  rfl

theorem bounded_holder_norm_formula : BoundedHolderNormFormula := by
  intro X 𝕜 _ _ α f
  rfl

/-- Real-distance characterization of Mathlib's extended-distance Hölder predicate. -/
theorem holderWith_iff_dist {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜]
    (C r : ℝ≥0) (f : X → 𝕜) :
    HolderWith C r f ↔ ∀ s t, ‖f s - f t‖ ≤ C * dist s t ^ (r : ℝ) := by
  constructor
  · intro h s t
    simpa only [dist_eq_norm] using h.dist_le s t
  · intro h s t
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) r.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using h s t)

/-- Every difference quotient is bounded by the declared seminorm. -/
theorem quotient_le_holderSeminorm {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜]
    (α : HolderExponent) (f : X → 𝕜) (hf : MemHolder α.val f) (s t : X) (hst : s ≠ t) :
    ‖f s - f t‖ / dist s t ^ (α.val : ℝ) ≤ holderSeminorm α f := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hst) _)).mpr
  simpa only [HolderSpacesSpec.holderSeminorm, dist_eq_norm] using hf.holderWith.dist_le s t

theorem quotient_supremum_formula : QuotientSupremumFormula := by
  intro X 𝕜 _ _ α f hf
  let S := holderQuotients α f
  have h0 : (0 : ℝ) ∈ S := Set.mem_insert _ _
  have hbd : BddAbove S := by
    refine ⟨holderSeminorm α f, ?_⟩
    intro q hq
    rcases hq with rfl | ⟨s, t, hst, rfl⟩
    · exact NNReal.coe_nonneg _
    · exact quotient_le_holderSeminorm α f hf s t hst
  have hs0 : 0 ≤ sSup S := le_csSup hbd h0
  apply le_antisymm
  · have hh : HolderWith ⟨sSup S, hs0⟩ α.val f := by
      apply (holderWith_iff_dist _ _ _).mpr
      intro s t
      by_cases hst : s = t
      · subst t
        simp only [sub_self, norm_zero, dist_self]
        exact mul_nonneg hs0 (Real.rpow_nonneg (by rfl) _)
      · apply (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hst) _)).mp
        exact le_csSup hbd (Set.mem_insert_of_mem _ ⟨s, t, hst, rfl⟩)
    exact_mod_cast hh.nnholderNorm_le
  · apply csSup_le ⟨0, h0⟩
    intro q hq
    rcases hq with rfl | ⟨s, t, hst, rfl⟩
    · exact NNReal.coe_nonneg _
    · exact quotient_le_holderSeminorm α f hf s t hst

theorem empty_quotient_convention : EmptyQuotientConvention := by
  intro X 𝕜 _ _ _ α f
  have h : HolderWith 0 α.val f := holderWith_zero_iff.mpr (fun _ _ => congrArg f (Subsingleton.elim _ _))
  have hh := h.nnholderNorm_le
  change (nnHolderNorm α.val f : ℝ) = 0
  exact_mod_cast le_antisymm hh (bot_le : (0 : ℝ≥0) ≤ _)

theorem bounded_holder_membership : BoundedHolderMembership := by
  intro X 𝕜 _ _ α f
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨‖g.val‖, g.val.norm_coe_le_norm⟩, g.property⟩
  · rintro ⟨⟨M, hM⟩, hf⟩
    let g : BoundedContinuousFunction X 𝕜 :=
      BoundedContinuousFunction.ofNormedAddCommGroup f
        (hf.holderWith.continuous α.property.1) M hM
    exact ⟨⟨g, hf⟩, rfl⟩

end ExpandedFA.Supplements
