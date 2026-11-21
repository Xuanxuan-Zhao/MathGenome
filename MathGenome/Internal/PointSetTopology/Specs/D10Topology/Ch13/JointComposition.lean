import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions

/-!
Independent statement of paper.tex, d10:13:composition (Theorem 13.7).
Each function space carries the source's compact-open topology. Only the
middle space is assumed locally compact Hausdorff; empty spaces are allowed.
-/

universe u v w

namespace Specs.D10Topology.Ch13.JointComposition

open Specs.D10Topology.Ch13.FunctionTopologies
open Specs.D10Topology.Ch11.LocalCompactConventions

def joint_composition : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z],
    LCH Y →
    letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
    letI : TopologicalSpace (ContinuousMaps Y Z) := compactOpenContinuousTopology
    letI : TopologicalSpace (ContinuousMaps X Z) := compactOpenContinuousTopology
    Continuous (fun p : ContinuousMaps X Y × ContinuousMaps Y Z => p.2.comp p.1)

end Specs.D10Topology.Ch13.JointComposition
