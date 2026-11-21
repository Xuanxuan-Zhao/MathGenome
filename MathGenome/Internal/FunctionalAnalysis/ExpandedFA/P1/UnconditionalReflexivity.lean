import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UnconditionalReflexivity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.UnconditionalL1Obstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.UnconditionalC0Obstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DualBases

/-! Assemble the two sequence-space obstructions with the accepted shrinking /
bounded completeness characterization of surjectivity of the canonical map.
The same continuous basis supplied by the ℓ¹ criterion is used in all clauses;
its vectors are exactly the original raw basis. -/

noncomputable section
namespace ExpandedFA.P1.UnconditionalReflexivity

theorem unconditional_basis_characterization : Spec.UnconditionalBasisCharacterization := by
  intro 𝕜 E _ _ _ _ e hu
  obtain ⟨b, hb, hs⟩ := UnconditionalL1Obstruction.raw_shrinking_criterion hu
  have hc : DualBasisBasicity.Spec.IsBoundedlyComplete (𝕜 := 𝕜) b.basis ↔
      ¬ UnconditionalC0Obstruction.Spec.ContainsC0 𝕜 E := by
    simpa only [hb] using UnconditionalC0Obstruction.boundedCompleteness_criterion hu
  refine ⟨b, hb, hs, hc, ?_⟩
  rw [DualBases.reflexivity_characterization b, hs, hc, and_comm]

theorem reflexivity_criterion : Spec.ReflexivityCriterion := by
  intro 𝕜 E _ _ _ _ e hu
  obtain ⟨b, _, _, _, hr⟩ := unconditional_basis_characterization hu
  exact hr

theorem reflexivity_alternative : Spec.ReflexivityAlternative := by
  intro 𝕜 E _ _ _ _ e hu
  classical
  by_cases hc : UnconditionalC0Obstruction.Spec.ContainsC0 𝕜 E
  · exact Or.inr (Or.inl hc)
  by_cases hl : UnconditionalL1Obstruction.Spec.ContainsClosedL1 𝕜 E
  · exact Or.inr (Or.inr hl)
  exact Or.inl ((reflexivity_criterion hu).mpr ⟨hc, hl⟩)

theorem finite_basis_characterization : Spec.FiniteBasisCharacterization := by
  intro 𝕜 E _ _ _ _ d e he
  obtain ⟨b, hb, hs⟩ := UnconditionalL1Obstruction.raw_finite_shrinking_criterion he
  have hc : DualBases.Spec.finiteBoundedlyComplete (𝕜 := 𝕜) b.basis ↔
      ¬ UnconditionalC0Obstruction.Spec.ContainsC0 𝕜 E := by
    simpa only [hb] using
      UnconditionalC0Obstruction.finite_boundedCompleteness_criterion he
  refine ⟨b, hb, hs, hc, ?_⟩
  constructor
  · intro _
    exact ⟨hc.mp (DualBases.finite_boundedly_complete b.basis),
      hs.mp (DualBases.finite_shrinking b)⟩
  · intro _
    exact DualBases.finite_reflexive b

theorem finite_reflexivity_criterion : Spec.FiniteReflexivityCriterion := by
  intro 𝕜 E _ _ _ _ d e he
  obtain ⟨b, _, _, _, hr⟩ := finite_basis_characterization he
  exact hr

end ExpandedFA.P1.UnconditionalReflexivity
