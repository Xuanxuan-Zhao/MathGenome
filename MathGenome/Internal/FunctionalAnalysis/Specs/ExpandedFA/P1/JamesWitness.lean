import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13Embedding
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.Sequences

/-! Independent specification of paper.tex, fa2:p1:james-witness.
The dual is continuous and scalar-linear; convex combinations use real
coefficients even over the complex field. All closed unit balls are inclusive.
Separability uses the original norm topology, while closedness and compactness
use the shared weak topology. -/
namespace ExpandedFA.P1.JamesWitness.Spec
universe u v
open Filter
open scoped Topology
noncomputable section

def SeparableWitness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (A : Set E), A.Nonempty → A ⊆ {x | ‖x‖ ≤ 1} →
    TopologicalSpace.IsSeparable A →
    @IsClosed E (C12DualPairSpec.DualPairTopologyValue 𝕜 E
      (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) A →
    ¬ @IsCompact E (C12DualPairSpec.DualPairTopologyValue 𝕜 E
      (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) A →
    ∃ (θ : ℝ) (f : ℕ → E →L[𝕜] 𝕜),
      0 < θ ∧ θ < 1 ∧ (∀ n, ‖f n‖ ≤ 1) ∧
      (∀ x ∈ A, Tendsto (fun n => f n x) atTop (𝓝 0)) ∧
      ∀ g ∈ convexHull ℝ (Set.range f),
        θ ≤ sSup ((fun x => ‖g x‖) '' A)

end
end ExpandedFA.P1.JamesWitness.Spec
