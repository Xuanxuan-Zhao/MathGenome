import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions

/-! Independent statements for the first two conclusions of
`paper.tex`, Proposition `d10:13:uniform-complete`.
The uniform topology and distance are the canonical Chapter 13 objects.
There are no compactness, separation, or nonemptiness assumptions on X or Y.
Ordinary convergence filters are proper; net indices are nonempty directed
preorders. Completeness below concerns exactly the truncated supremum metric,
in both the sequence and proper-Cauchy-filter conventions of the paper. -/
noncomputable section
open Filter
open scoped Topology
universe u v w
namespace Specs.D10Topology.Ch13.UniformLimitsCompleteness

open FunctionTopologies

def uniform_limit_continuous_filter : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    {I : Type w} (l : Filter I) [l.NeBot]
    (F : I → X → Y) (f : X → Y),
    (∀ i, Continuous (F i)) →
    Tendsto F l (@nhds (X → Y) uniformTopology f) → Continuous f

def uniform_limit_continuous_net : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I → X → Y) (f : X → Y),
    (∀ i, Continuous (F i)) →
    (∀ ε : ℝ, 0 < ε → ∃ i₀, ∀ i, i₀ ≤ i → uniformDistance (F i) f < ε) →
    Continuous f

def uniform_limit_continuous_sequence : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y),
    (∀ n, Continuous (F n)) →
    (∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n → uniformDistance (F n) f < ε) →
    Continuous f

def uniform_continuous_complete : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [mY : MetricSpace Y],
    Ch09.MetricConventions.SequentiallyComplete mY.toPseudoMetricSpace →
    ∃ m : MetricSpace (ContinuousMaps X Y),
      (∀ f g, @dist _ m.toDist f g = uniformDistance (f : X → Y) (g : X → Y)) ∧
      m.toUniformSpace.toTopologicalSpace = uniformContinuousTopology ∧
      Ch09.MetricConventions.SequentiallyComplete m.toPseudoMetricSpace ∧
      @Ch12.UniformConventions.Complete (ContinuousMaps X Y) m.toUniformSpace

end Specs.D10Topology.Ch13.UniformLimitsCompleteness
