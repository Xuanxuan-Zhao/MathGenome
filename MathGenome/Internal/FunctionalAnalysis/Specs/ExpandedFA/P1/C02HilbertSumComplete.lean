import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02HilbertSum

/-!
Independent statement of Proposition `fa2:p1:c02:hilbert-sum-complete`
(paper.tex 497–503).

The space and maps are exactly the canonical square-summable-family objects
of the upstream definition. Its existing `InnerProductSpace` instance has
the coordinate-sum inner product and the square-sum norm; completeness below
therefore says that this same space is Hilbert. Both operator-norm and
distance forms of contractivity are recorded. There is no countability,
nonemptiness, separability, or nonzero-summand hypothesis.
-/

universe u v w

namespace ExpandedFA.P1.C02HilbertSumComplete.Spec

open ExpandedFA.P1.C02HilbertSum.Spec

/-- All conclusions of completeness and finite-support density, for every
family of real or complex Hilbert spaces over an arbitrary index type. -/
def CompletenessAndDensity : Prop :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)]
    [∀ i, CompleteSpace (H i)],
    CompleteSpace (Space H) ∧
    (∀ i : I, ‖coordinate (𝕜 := 𝕜) H i‖ ≤ 1 ∧
      LipschitzWith 1 (coordinate (𝕜 := 𝕜) H i)) ∧
    (∀ i : I, ‖inclusion (𝕜 := 𝕜) H i‖ ≤ 1 ∧
      LipschitzWith 1 (inclusion (𝕜 := 𝕜) H i)) ∧
    Dense (finiteSupport H) ∧
    ∀ x : Space H, Set.Countable {i | x i ≠ 0}

end ExpandedFA.P1.C02HilbertSumComplete.Spec
