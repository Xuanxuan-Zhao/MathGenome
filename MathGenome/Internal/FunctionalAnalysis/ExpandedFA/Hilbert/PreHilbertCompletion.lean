import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertCompletion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02Completion

/-!
The Hilbert completion of an inner-product space (paper.tex 7682–7707).

The canonical uniform completion carries the continuous extension of the given
inner product. Mathlib proves the inner-product axioms for this extension and
its agreement with the original inner product on embedded vectors.
For uniqueness, inner-product-preserving linear maps are linear isometries.
The accepted normed-completion uniqueness theorem gives the unique intertwining
surjective linear isometry, which preserves inner products by polarization.
-/

namespace ExpandedFA.Hilbert.PreHilbertCompletion

theorem canonical_completion_properties : Spec.CanonicalCompletionProperties := by
  intro 𝕜 E _ _ _
  refine ⟨inferInstance, ?_, UniformSpace.Completion.toComplₗᵢ.injective,
    UniformSpace.Completion.denseRange_coe⟩
  intro x y
  exact UniformSpace.Completion.inner_coe x y

theorem completion_exists : Spec.CompletionExists := by
  intro 𝕜 E _ _ _
  refine ⟨UniformSpace.Completion E, inferInstance, inferInstance, inferInstance,
    UniformSpace.Completion.toComplₗᵢ.toLinearMap, ?_⟩
  exact (canonical_completion_properties 𝕜 E).2

theorem completion_uniqueness : Spec.CompletionUniqueness := by
  intro 𝕜 E H G _ _ _ _ _ _ _ _ _ i j hi hdi hj hdj
  let i' := i.isometryOfInner hi
  let j' := j.isometryOfInner hj
  obtain ⟨U, hU, huniq⟩ :=
    ExpandedFA.P1.C02Completion.completion_uniqueness 𝕜 E H G i' j' hdi hdj
  refine ⟨U, ⟨U.inner_map_map, hU⟩, ?_⟩
  intro V hV
  exact huniq V hV.2

end ExpandedFA.Hilbert.PreHilbertCompletion
