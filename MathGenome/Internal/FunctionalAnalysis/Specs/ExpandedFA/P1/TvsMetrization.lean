import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsNormability
import Mathlib.Topology.Metrizable.Uniformity

/-! Independent statements of `fa2:p1:tvs-metrization`, paper.tex:1848–1854.
All metrics below induce the original topology. Balls called balanced are
centered at zero; convexity holds for balls at every center. -/

open Set Filter TopologicalSpace
open scoped Topology

namespace ExpandedFA.P1.TvsMetrizationSpec

/-- Countability is countability of the neighborhood filter at zero, rather
than a countable base for the entire topology. -/
def Metrization : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [T2Space E], TVS 𝕜 E →
      (MetrizableSpace E ↔ (𝓝 (0 : E)).IsCountablyGenerated)

/-- Translation invariance and balance are required of the same compatible
metric, for every positive radius and over the original scalar field. -/
def BalancedMetric : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [t : TopologicalSpace E] [T2Space E], TVS 𝕜 E →
      (𝓝 (0 : E)).IsCountablyGenerated →
      ∃ m : MetricSpace E, m.toUniformSpace.toTopologicalSpace = t ∧
        (letI := m
         (∀ x y z : E, dist (x + z) (y + z) = dist x y) ∧
         ∀ r : ℝ, 0 < r → Balanced 𝕜 (Metric.ball (0 : E) r))

/-- In an LCS one can simultaneously require balance and convexity. -/
def ConvexMetric : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [t : TopologicalSpace E] [T2Space E],
      LCS 𝕜 E → (𝓝 (0 : E)).IsCountablyGenerated →
      ∃ m : MetricSpace E, m.toUniformSpace.toTopologicalSpace = t ∧
        (letI := m
         (∀ x y z : E, dist (x + z) (y + z) = dist x y) ∧
         (∀ r : ℝ, 0 < r → Balanced 𝕜 (Metric.ball (0 : E) r)) ∧
         ∀ x : E, ∀ r : ℝ, 0 < r → Convex ℝ (Metric.ball x r))

/-- The final clause uses a positive definite compatible scalar seminorm,
which is a genuine norm; it is the accepted normability interface. -/
def Normability.{u, v} : Prop := TvsNormabilitySpec.Normability.{u, v}

end ExpandedFA.P1.TvsMetrizationSpec
