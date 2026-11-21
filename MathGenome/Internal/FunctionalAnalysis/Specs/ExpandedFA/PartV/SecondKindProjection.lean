import Mathlib.Analysis.Normed.Operator.Basic
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent statement of paper.tex:22949–22967,
`fa2:p5:second-kind-projection`, including the quantitative conclusions
required by this goal. The subspaces need not be nested or finite dimensional.
The two projection hypotheses express that Pₙ maps into Xₙ and fixes Xₙ.
The inverse maps are defined at every index, with their inverse properties
and solution conclusions required only on a common tail. Both real and
complex Banach spaces, including the zero space, are covered. -/

open Filter
open scoped Topology

namespace ExpandedFA.PartV.SecondKindProjection.Spec
universe u v

def ConvergenceAndError : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (K : X →L[𝕜] X),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    Function.Injective (ContinuousLinearMap.id 𝕜 X - K) →
    ∀ (Xn : ℕ → Submodule 𝕜 X) (P : ℕ → X →L[𝕜] X),
    (∀ n x, P n x ∈ Xn n) →
    (∀ n x, x ∈ Xn n → P n x = x) →
    (∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) →
    ∃ (Ai : X →L[𝕜] X) (R : ℕ → X →L[𝕜] X)
      (C M : ℝ) (N : ℕ),
      0 < C ∧ 0 ≤ M ∧ (∀ n, ‖P n‖ ≤ M) ∧
      (ContinuousLinearMap.id 𝕜 X - K).comp Ai = ContinuousLinearMap.id 𝕜 X ∧
      Ai.comp (ContinuousLinearMap.id 𝕜 X - K) = ContinuousLinearMap.id 𝕜 X ∧
      Tendsto (fun n => ‖(P n).comp K - K‖) atTop (𝓝 0) ∧
      (∀ n, N ≤ n →
        (ContinuousLinearMap.id 𝕜 X - (P n).comp K).comp (R n) =
          ContinuousLinearMap.id 𝕜 X ∧
        (R n).comp (ContinuousLinearMap.id 𝕜 X - (P n).comp K) =
          ContinuousLinearMap.id 𝕜 X ∧ ‖R n‖ ≤ C) ∧
      ∀ f : X,
        Tendsto (fun n => R n (P n f)) atTop (𝓝 (Ai f)) ∧
        ∀ n, N ≤ n →
          R n (P n f) ∈ Xn n ∧
          R n (P n f) - P n (K (R n (P n f))) = P n f ∧
          (∀ v : X, v ∈ Xn n → v - P n (K v) = P n f → v = R n (P n f)) ∧
          R n (P n f) - Ai f = R n (P n (Ai f) - Ai f) ∧
          ‖R n (P n f) - Ai f‖ ≤
            C * (1 + M) * Metric.infDist (Ai f) (Xn n : Set X)

end ExpandedFA.PartV.SecondKindProjection.Spec
