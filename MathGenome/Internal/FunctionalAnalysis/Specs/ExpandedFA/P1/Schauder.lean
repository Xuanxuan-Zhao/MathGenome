import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions

/-!
Independent statement of Schauder--Tychonoff, `fa2:p1:schauder`,
paper.tex:5637–5641. Compactness and continuity use the given locally
convex topology and its induced subtype topology. No norm, metrizability,
completeness, or finite-dimensionality is assumed.

The compatible real structure expresses real convexity over either of the
manuscript's scalar fields, just as in the shared `LCS` interface.
-/

universe u v

namespace ExpandedFA.P1.Schauder.Spec

def SchauderTychonoff : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [T2Space E], LCS 𝕜 E →
    ∀ (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
      ∀ (T : K → K), Continuous T → ∃ x : K, T x = x

end ExpandedFA.P1.Schauder.Spec
