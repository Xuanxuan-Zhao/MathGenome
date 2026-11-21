import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.CompactConvergenceCompleteness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.CompactShrinking
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.MetricFilterCompleteness
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! Completeness in the uniformity of compact convergence, the last assertion
of paper.tex, `d10:13:uniform-complete`.

The library completeness theorem works for compactly coherent domains.
The accepted compact-neighborhood bridge supplies this condition for LCH X.
Before applying it, we identify the actual uniformities (equality of the
compact-open and compact-convergence topologies alone would not suffice).
The library proof uses completeness on compact restrictions and closedness
of the continuous maps in the space of compact-uniform limits. -/
noncomputable section
open Set Filter
open scoped Topology Uniformity
universe u v
namespace D10Topology.Ch13
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]

/-- The two induced structures have exactly the same entourages. Mathlib
replaces only the topology projection with its proved equal compact-open one. -/
theorem compactConvergenceContinuousUniformity_eq_mathlib :
    compactConvergenceContinuousUniformity (X := X) (Y := Y) =
      ContinuousMap.compactConvergenceUniformSpace := by
  apply UniformSpace.ext
  change comap _ (comap _ _) = _
  rw [Filter.comap_comap]
  rfl

theorem compactConvergenceContinuous_completeSpace [CompleteSpace Y]
    (hX : Ch11.LCH X) :
    @CompleteSpace (ContinuousMaps X Y) compactConvergenceContinuousUniformity := by
  let : T2Space X := hX.2
  let : LocallyCompactSpace X :=
    (Ch11.locallyCompact_iff_locallyCompactSpace X).mp hX.1
  rw [compactConvergenceContinuousUniformity_eq_mathlib]
  infer_instance

theorem compactConvergenceContinuous_complete
    (hX : Ch11.LCH X)
    (hY : Ch09.SequentiallyComplete (inferInstance : MetricSpace Y).toPseudoMetricSpace) :
    @Ch12.Complete (ContinuousMaps X Y) compactConvergenceContinuousUniformity := by
  let : CompleteSpace Y := (Ch09.sequentiallyComplete_iff_mathlib _).mp hY
  let : UniformSpace (ContinuousMaps X Y) := compactConvergenceContinuousUniformity
  exact Ch12.complete_iff_mathlib.mpr (compactConvergenceContinuous_completeSpace hX)

theorem compactConvergence_cauchy_filter_converges
    (hX : Ch11.LCH X)
    (hY : Ch09.SequentiallyComplete (inferInstance : MetricSpace Y).toPseudoMetricSpace)
    (F : Filter (ContinuousMaps X Y))
    (hF : @Ch12.CauchyFilter (ContinuousMaps X Y)
      compactConvergenceContinuousUniformity F) :
    ∃ f : ContinuousMaps X Y,
      F ≤ @nhds (ContinuousMaps X Y) compactConvergenceContinuousTopology f := by
  let : UniformSpace (ContinuousMaps X Y) := compactConvergenceContinuousUniformity
  obtain ⟨f, hf⟩ := compactConvergenceContinuous_complete hX hY F hF
  exact ⟨f, (@Ch04.converges_iff_le_nhds (ContinuousMaps X Y)
    compactConvergenceContinuousTopology F f).mp hf⟩

end D10Topology.Ch13
