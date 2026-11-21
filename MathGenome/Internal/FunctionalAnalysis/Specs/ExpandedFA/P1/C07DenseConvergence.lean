import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-!
Independent statements for Theorem `fa2:p1:c07:dense-convergence`, paper.tex
1477–1502. Density and convergence use the native norm topology. The finite uniform bound is expressed pointwise as `∀ n, ‖Tn n‖ ≤ M`,
which implies `0 ≤ M` since the sequence has a zeroth term. The sequence
consists of the canonical bounded linear maps from the shared operator interface.
The domain is an arbitrary normed space; neither statement assumes it complete.
-/

namespace ExpandedFA.P1.C07DenseConvergence.Spec

open scoped Topology

universe u v w

/-- Convergence on an arbitrary dense subset and a uniform operator norm bound
give a bounded pointwise limit when the target is Banach, with the same bound. -/
def DenseConvergence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (D : Set E) (M : ℝ) (Tn : ℕ → E →L[𝕜] F),
    Dense D → (∀ n, ‖Tn n‖ ≤ M) →
    (∀ d ∈ D, ∃ y : F, Filter.Tendsto (fun n => Tn n d) Filter.atTop (𝓝 y)) →
    ∃ T : E →L[𝕜] F,
      (∀ x : E, Filter.Tendsto (fun n => Tn n x) Filter.atTop (𝓝 (T x))) ∧
      ‖T‖ ≤ M

/-- When the bounded candidate limit is given, the target may be incomplete.
No bound on its norm is an extra hypothesis. -/
def DenseConvergenceToGivenOperator : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (D : Set E) (M : ℝ) (Tn : ℕ → E →L[𝕜] F) (T : E →L[𝕜] F),
    Dense D → (∀ n, ‖Tn n‖ ≤ M) →
    (∀ d ∈ D, Filter.Tendsto (fun n => Tn n d) Filter.atTop (𝓝 (T d))) →
    ∀ x : E, Filter.Tendsto (fun n => Tn n x) Filter.atTop (𝓝 (T x))

end ExpandedFA.P1.C07DenseConvergence.Spec
