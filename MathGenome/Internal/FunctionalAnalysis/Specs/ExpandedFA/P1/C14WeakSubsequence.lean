import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Defs.Sequences

/-!
Theorem `fa2:p1:c14:weak-subsequence`, paper.tex:2822–2827.
The dual is formed using the given norm before introducing the weak
topology σ(E,E′). Reflexivity means surjectivity of canonical evaluation.
The ambient Banach space may be nonseparable or zero, over ℝ or ℂ.
-/

namespace ExpandedFA.P1.C14WeakSubsequence.Spec

universe u v
open Filter

/-- Every norm-bounded sequence in a reflexive Banach space has a
strictly increasing extraction converging in its weak topology. -/
def WeakSubsequence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ a : ℕ → E, Bornology.IsBounded (Set.range a) →
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ x : E,
        Tendsto (a ∘ k) atTop
          (@nhds E
            (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
              (topDualPairing 𝕜 E)) x)

end ExpandedFA.P1.C14WeakSubsequence.Spec
