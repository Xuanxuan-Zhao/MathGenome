import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.JointComposition
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.CompactShrinking

/-!
Joint composition for the compact-open topology (paper.tex, Theorem 13.7).
The accepted topology bridge identifies the source topology on each function
space with Mathlib's compact-open topology. The source LCH assumption on Y
gives arbitrarily small compact neighborhoods, which is the only condition
needed to apply the library's joint composition theorem.
-/

universe u v w

namespace D10Topology.Ch13

theorem joint_composition {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (hY : Ch11.LCH Y) :
    letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
    letI : TopologicalSpace (ContinuousMaps Y Z) := compactOpenContinuousTopology
    letI : TopologicalSpace (ContinuousMaps X Z) := compactOpenContinuousTopology
    Continuous (fun p : ContinuousMaps X Y × ContinuousMaps Y Z => p.2.comp p.1) := by
  rw [compactOpenContinuousTopology_eq_mathlib (X := X) (Y := Y),
    compactOpenContinuousTopology_eq_mathlib (X := Y) (Y := Z),
    compactOpenContinuousTopology_eq_mathlib (X := X) (Y := Z)]
  let : T2Space Y := hY.2
  let : LocallyCompactSpace Y := (Ch11.locallyCompact_iff_locallyCompactSpace Y).mp hY.1
  exact ContinuousMap.continuous_comp'

end D10Topology.Ch13
