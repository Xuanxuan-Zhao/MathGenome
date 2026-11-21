import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.ProjectionLattice
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PositiveQuadraticEstimates
import Mathlib.Topology.Order.MonotoneConvergence

/-! The monotone-limit assertion of `fa2:p2:projection-lattice`, paper.tex
7415–7418. The projection lattice itself is the accepted upstream interface.
The native order is the Loewner order, and convergence is pointwise in norm.
No commutativity, dimension, separability, or nonzero hypothesis is imposed. -/
noncomputable section
open scoped InnerProductSpace Topology
namespace ExpandedFA.Hilbert.MonotoneOperatorLimits.Spec
universe u v

def MonotoneStrongSupremum : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H),
    (∀ n, IsSelfAdjoint (A n)) → IsSelfAdjoint B →
    (∀ n, A n ≤ A (n + 1)) → (∀ n, A n ≤ B) →
    ∃ L : H →L[𝕜] H, IsSelfAdjoint L ∧
      (∀ x : H, Filter.Tendsto (fun n => A n x) Filter.atTop (𝓝 (L x))) ∧
      IsLUB (Set.range A) L ∧ L ≤ B

end ExpandedFA.Hilbert.MonotoneOperatorLimits.Spec
