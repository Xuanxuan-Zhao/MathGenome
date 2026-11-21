import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Topology.UniformSpace.Cauchy

/-!
Independent specifications for `fa2:p1:weak-sequential-completeness`,
paper.tex 6452–6467 (parts/part1-supplements.tex).
Cauchy hypotheses are scalar Cauchy tests in the original norm-continuous,
scalar-linear dual. Conclusions use the shared weak and weak-star topologies,
and the limit in the second statement is a continuous linear functional.
-/
namespace ExpandedFA.Supplements.WeakSequentialCompleteness.Spec

universe u v
open Filter
open scoped Topology

/-- Every weakly Cauchy sequence in a reflexive Banach space converges weakly. -/
def ReflexiveWeakSequentialCompleteness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ x : ℕ → E, (∀ f : E →L[𝕜] 𝕜, CauchySeq (fun n => f (x n))) →
      ∃ z : E, Tendsto x atTop
        (@nhds E (P1.C12DualPairSpec.DualPairTopologyValue 𝕜 E
          (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) z)

/-- A weak-star Cauchy sequence in the dual of a Banach space has a limit
in that continuous dual, with its weak-star topology. -/
def DualWeakStarSequentialCompleteness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    ∀ f : ℕ → (E →L[𝕜] 𝕜), (∀ x : E, CauchySeq (fun n => f n x)) →
      ∃ g : E →L[𝕜] 𝕜, Tendsto f atTop
        (@nhds (E →L[𝕜] 𝕜) (P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) g)

end ExpandedFA.Supplements.WeakSequentialCompleteness.Spec
