import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceBanachBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceShrinking
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceBidual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceBidualIsometry

/-! Assembly of the cyclic-variation James space theorem. All components
concern the same prescribed real sequence space and its native norm. -/
noncomputable section

namespace ExpandedFA.P1.JamesSpace

/-- The real James space has a normalized monotone shrinking basis, a
codimension-one canonical bidual image, and the stated noncanonical isometry. -/
theorem james_space : Spec.JamesSpaceConclusion := by
  exact ⟨James.banach_basis, JamesShrinking.shrinking,
    JamesBidual.codimension_one, JamesBidualIsometry.explicit_isometry,
    JamesBidualIsometry.nonreflexive_isometric⟩

/-- An isometric isomorphism onto the bidual does not ensure reflexivity. -/
theorem isometry_does_not_imply_reflexivity : Spec.IsometryDoesNotImplyReflexivity := by
  obtain ⟨m⟩ := James.banach_basis
  obtain ⟨⟨e⟩, _, hnonreflexive⟩ := JamesBidualIsometry.nonreflexive_isometric m
  exact ⟨m, ⟨e.symm⟩, hnonreflexive⟩

end ExpandedFA.P1.JamesSpace
