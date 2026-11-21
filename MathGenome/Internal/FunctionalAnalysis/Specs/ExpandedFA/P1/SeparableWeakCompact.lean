import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12BoundedSequences
import Mathlib.Topology.Metrizable.Basic

/-!
Independent statements for `fa2:p1:separable-weak-compact`, paper.tex 3056–3062.
Separability uses the original norm topology on the subspace. Compactness and
metrizability use the restriction of the ambient weak topology, defined by the
original continuous scalar-linear dual. No completeness or closedness of the
subspace is assumed. The zero subspace and empty compact subset are included.
-/

namespace ExpandedFA.P1.SeparableWeakCompact.Spec

universe u v
open Filter
open scoped Topology

/-- A sequence in the closed dual unit ball separates all points of Y. -/
def CountableSeparatingFamily : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Y : Submodule 𝕜 E) [TopologicalSpace.SeparableSpace Y],
    ∃ f : ℕ → (E →L[𝕜] 𝕜), (∀ n, ‖f n‖ ≤ 1) ∧
      ∀ x y : Y, x ≠ y → ∃ n, f n (x : E) ≠ f n (y : E)

/-- Every weakly compact ambient subset contained in Y is weakly metrizable. -/
def WeakCompactMetrizable : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Y : Submodule 𝕜 E) [TopologicalSpace.SeparableSpace Y]
    (K : Set E), K ⊆ (Y : Set E) →
    letI : TopologicalSpace E :=
      C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
    IsCompact K → TopologicalSpace.MetrizableSpace K

/-- Weak convergence bounds the whole sequence in the original norm. -/
def WeakSequenceBounded : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (s : ℕ → E) (x : E),
    Tendsto s atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) x) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖s n‖ ≤ C

end ExpandedFA.P1.SeparableWeakCompact.Spec
