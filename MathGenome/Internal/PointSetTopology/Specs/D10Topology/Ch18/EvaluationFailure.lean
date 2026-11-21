import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.ContinuousMap.Algebra

/-! The exact pointwise failure in paper.tex, d10:18:evaluation-failure.
The topology on the function factor is the chapter 13 compact-open topology;
the rational and real factors have their usual topologies. -/

namespace Specs.D10Topology.Ch18.EvaluationFailure

def evaluation_failure : Prop :=
  letI : TopologicalSpace C(ℚ, ℝ) :=
    D10Topology.Ch13.FunctionTopologies.compactOpenContinuousTopology
  ¬ ContinuousAt (fun p : C(ℚ, ℝ) × ℚ => p.1 p.2)
    ((0 : C(ℚ, ℝ)), (0 : ℚ))

end Specs.D10Topology.Ch18.EvaluationFailure
