import MathGenome.Internal.RealAnalysis.D11.Ch21.CompactContentRadonMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarExistence

/-!
# Existence of left Haar measure

This assembles the compact-content construction of Chapter 21, as in
`paper.tex:5864–5871`. Local compactness supplies a compact set with nonempty
interior. The compact-product construction supplies its normalized invariant
content, and the Borel restriction of the associated outer measure is Radon,
left invariant, and nonzero. No countability assumption is used.
-/

namespace D11.Ch21

open TopologicalSpace MeasureTheory

universe u

/-- Every Hausdorff locally compact topological group has a left Haar measure. -/
theorem haar_existence (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] :
    ∃ μ : @Measure G (borel G), isLeftHaarMeasure μ := by
  let K₀ : PositiveCompacts G := Classical.choice inferInstance
  obtain ⟨h, _hproduct, _hcluster, hh⟩ := compact_content_cluster G K₀
  let μ := CompactContentOuterMeasure.borelMeasure
    (CompactContentOuterMeasure.sourceContent K₀ h hh)
  have hμ := CompactContentRadonMeasure.compact_content_radon_measure K₀ h hh
  exact ⟨μ, hμ.2.2.2.2, hμ.1, hμ.2.1⟩

end D11.Ch21
