import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statements for fa2:p1:c13:metric, paper.tex 2564–2573.
The natural index `n` represents the manuscript index `n + 1`. Tests are
points of the closed unit ball with its inherited norm topology. The dual
always means the continuous scalar-linear dual for the original norm on E.
The metric conclusion includes its distance formula and equality with the
relative weak-star topology. No completeness, nonemptiness of A, or
nontriviality of E is assumed. -/

namespace ExpandedFA.P1.C13Metric.Spec

universe u v
open scoped Topology
noncomputable section

def DistanceType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (ℕ → Metric.closedBall (0 : E) 1) → (E →L[𝕜] 𝕜) → (E →L[𝕜] 𝕜) → ℝ

def DistanceValue : DistanceType :=
  fun _ _ _ _ _ x f g =>
    ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * min 1 ‖(f - g) (x n)‖

def SeriesConvergence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → Metric.closedBall (0 : E) 1) (f g : E →L[𝕜] 𝕜),
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * min 1 ‖(f - g) (x n)‖)

def PositiveDefiniteness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → Metric.closedBall (0 : E) 1), DenseRange x →
    ∀ (f g : E →L[𝕜] 𝕜), DistanceValue 𝕜 E x f g = 0 ↔ f = g

def Metrization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace.SeparableSpace E]
    (x : ℕ → Metric.closedBall (0 : E) 1), DenseRange x →
    ∀ A : Set (E →L[𝕜] 𝕜), Bornology.IsBounded A →
    ∃ m : MetricSpace A,
      (∀ f g : A, @dist A m.toDist f g = DistanceValue 𝕜 E x f.val g.val) ∧
      m.toUniformSpace.toTopologicalSpace =
        TopologicalSpace.induced (Subtype.val : A → (E →L[𝕜] 𝕜))
          (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)

/-- The choice of dense tests is possible under exactly the source's separability
hypothesis; the closed unit ball contains zero even in dimension zero. -/
def DenseTestsExistence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace.SeparableSpace E],
    ∃ x : ℕ → Metric.closedBall (0 : E) 1, DenseRange x

/-- In the zero-space case the continuous dual is a singleton and the
specified series distance is identically zero. -/
def ZeroSpaceDistance : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E],
    Subsingleton (E →L[𝕜] 𝕜) ∧
    ∀ (x : ℕ → Metric.closedBall (0 : E) 1) (f g : E →L[𝕜] 𝕜),
      DistanceValue 𝕜 E x f g = 0

end
end ExpandedFA.P1.C13Metric.Spec
