import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.Normed.Operator.Basic

/-! Independent statements of collectively compact stability,
`paper.tex:22865–22896`. All closures are in the original Banach space.
The pointwise limit starts as an arbitrary function; its bounded linear
representative is a conclusion. Scalars can be real or complex, and the
zero space is included. The error estimate applies at every sufficiently
large index and to every pair of solutions, without assumptions on the data.
-/

open Filter
open scoped Topology

namespace ExpandedFA.PartV.CollectiveCompact.Spec

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The closed collective image of the closed unit ball. -/
def collectiveClosure (Kn : ℕ → X →L[𝕜] X) : Set X :=
  closure (⋃ n, Kn n '' Metric.closedBall (0 : X) 1)

/-- Relative compactness of the union, rather than compactness of each term. -/
def IsCollectivelyCompact (Kn : ℕ → X →L[𝕜] X) : Prop :=
  IsCompact (collectiveClosure Kn)

/-- Compactness of the individual maps and the limit, a common operator bound,
and both uniform compact-composition estimates used in the stability proof. -/
def CompactnessAndCompositions : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (Kn : ℕ → X →L[𝕜] X) (K : X → X),
    IsCollectivelyCompact Kn →
    (∀ x, Tendsto (fun n => Kn n x) atTop (𝓝 (K x))) →
    (∀ n, Compactness.DefinitionsSpec.IsCompactLinearMapValue (Kn n).toLinearMap) ∧
    ∃ L : X →L[𝕜] X, (∀ x, L x = K x) ∧
      Compactness.DefinitionsSpec.IsCompactLinearMapValue L.toLinearMap ∧
      ∃ M : ℝ, 0 ≤ M ∧ (∀ n, ‖Kn n‖ ≤ M) ∧ ‖L‖ ≤ M ∧
        Tendsto (fun n => ‖(Kn n - L).comp (Kn n)‖) atTop (𝓝 0) ∧
        Tendsto (fun n => ‖(Kn n - L).comp L‖) atTop (𝓝 0)

/-- Two-sided bounded inverses for the limit and all sufficiently late maps,
a common inverse bound, and the source's quantitative solution estimate. -/
def Stability : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (Kn : ℕ → X →L[𝕜] X) (K : X → X),
    IsCollectivelyCompact Kn →
    (∀ x, Tendsto (fun n => Kn n x) atTop (𝓝 (K x))) →
    Function.Injective (fun x => x - K x) →
    ∃ L : X →L[𝕜] X, (∀ x, L x = K x) ∧
      Compactness.DefinitionsSpec.IsCompactLinearMapValue L.toLinearMap ∧
      ∃ R : X →L[𝕜] X,
        (ContinuousLinearMap.id 𝕜 X - L).comp R = ContinuousLinearMap.id 𝕜 X ∧
        R.comp (ContinuousLinearMap.id 𝕜 X - L) = ContinuousLinearMap.id 𝕜 X ∧
        ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
          ∃ Rn : X →L[𝕜] X,
            (ContinuousLinearMap.id 𝕜 X - Kn n).comp Rn = ContinuousLinearMap.id 𝕜 X ∧
            Rn.comp (ContinuousLinearMap.id 𝕜 X - Kn n) = ContinuousLinearMap.id 𝕜 X ∧
            ‖Rn‖ ≤ C ∧
            ∀ un u fn f : X, un - Kn n un = fn → u - K u = f →
              ‖un - u‖ ≤ C * (‖(Kn n - L) u‖ + ‖fn - f‖)

end ExpandedFA.PartV.CollectiveCompact.Spec
