import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions

/-! The last conclusion of paper.tex, `d10:13:uniform-complete`.
Local compactness is the source's compact-neighborhood condition, with
Hausdorffness explicit in `LCH`. The uniformity is the canonical one generated
by all compact-restriction pseudometrics, not the global uniform metric.
Neither the domain nor the space of continuous maps is assumed nonempty. -/
noncomputable section
open Set Filter
open scoped Topology Uniformity
universe u v
namespace Specs.D10Topology.Ch13.CompactConvergenceCompleteness
open FunctionTopologies

/-- Completeness for the specified compact-convergence uniformity. -/
def compactConvergenceContinuous_completeSpace : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    [CompleteSpace Y],
    Ch11.LocalCompactConventions.LCH X →
    @CompleteSpace (ContinuousMaps X Y) compactConvergenceContinuousUniformity

/-- The source's sequential metric hypothesis and proper-filter conclusion. -/
def compactConvergenceContinuous_complete : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [mY : MetricSpace Y],
    Ch11.LocalCompactConventions.LCH X →
    Ch09.MetricConventions.SequentiallyComplete mY.toPseudoMetricSpace →
    @Ch12.UniformConventions.Complete (ContinuousMaps X Y)
      compactConvergenceContinuousUniformity

/-- Every proper Cauchy filter converges in this very uniformity's topology. -/
def compactConvergence_cauchy_filter_converges : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [mY : MetricSpace Y],
    Ch11.LocalCompactConventions.LCH X →
    Ch09.MetricConventions.SequentiallyComplete mY.toPseudoMetricSpace →
    ∀ F : Filter (ContinuousMaps X Y),
      @Ch12.UniformConventions.CauchyFilter (ContinuousMaps X Y)
        compactConvergenceContinuousUniformity F →
      ∃ f : ContinuousMaps X Y,
        F ≤ @nhds (ContinuousMaps X Y) compactConvergenceContinuousTopology f

end Specs.D10Topology.Ch13.CompactConvergenceCompleteness
