import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
Independent statements for `fa2:p1:c12:bounded-sequences`, paper.tex 2363–2372.
The weak topology is the shared initial topology of the original norm-continuous
scalar-linear dual. Norms always refer to the original normed structures.
Completeness is required only for the weak-star sequence statements. Whole
sequences are bounded, and the compact-set statement includes the empty set.
The finite upper bounds ensure that the real-valued norm liminfs are meaningful.
-/

namespace ExpandedFA.P1.C12BoundedSequences.Spec

universe u v
open Filter
open scoped Topology
noncomputable section

def WeakSequenceBounded : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (s : ℕ → E) (x : E),
    Tendsto s atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) x) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖s n‖ ≤ C

def WeakSequenceNormLiminf : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (s : ℕ → E) (x : E),
    Tendsto s atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) x) →
    ‖x‖ ≤ liminf (fun n => ‖s n‖) atTop

def WeakStarSequenceBounded : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (s : ℕ → (E →L[𝕜] 𝕜)) (f : E →L[𝕜] 𝕜),
    Tendsto s atTop
      (@nhds (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) f) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖s n‖ ≤ C

def WeakStarSequenceNormLiminf : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (s : ℕ → (E →L[𝕜] 𝕜)) (f : E →L[𝕜] 𝕜),
    Tendsto s atTop
      (@nhds (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) f) →
    ‖f‖ ≤ liminf (fun n => ‖s n‖) atTop

def WeakCompactNormBounded : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : Set E),
    @IsCompact E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
      (topDualPairing 𝕜 E)) K →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖x‖ ≤ C

end
end ExpandedFA.P1.C12BoundedSequences.Spec
