import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctorialMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies

/-! Fixed evaluation and fixed composition for the compact-open topology.
The identification with Mathlib's topology was established upstream from
the actual subbasic sets. None of these statements needs local compactness. -/

universe u v w z

namespace D10Topology.Ch13

theorem fixed_evaluation_continuous
    {X : Type u} {Y : Type v} [TopologicalSpace X] [tY : TopologicalSpace Y]
    (x : X) :
    @Continuous (ContinuousMaps X Y) Y compactOpenContinuousTopology tY
      (fun f => f x) := by
  rw [compactOpenContinuousTopology_eq_mathlib]
  exact continuous_eval_const x

theorem compactOpen_hausdorff
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] :
    @T2Space (ContinuousMaps X Y) compactOpenContinuousTopology := by
  rw [compactOpenContinuousTopology_eq_mathlib]
  infer_instance

theorem fixed_precomposition_continuous
    {X : Type u} {Y : Type v} {W : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    (a : W → X) (ha : Continuous a) :
    @Continuous (ContinuousMaps X Y) (ContinuousMaps W Y)
      compactOpenContinuousTopology compactOpenContinuousTopology
      (fun f => f.comp (⟨a, ha⟩ : ContinuousMaps W X)) := by
  rw [compactOpenContinuousTopology_eq_mathlib, compactOpenContinuousTopology_eq_mathlib]
  exact ContinuousMap.continuous_precomp (⟨a, ha⟩ : ContinuousMaps W X)

theorem fixed_postcomposition_continuous
    {X : Type u} {Y : Type v} {Z : Type z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (b : Y → Z) (hb : Continuous b) :
    @Continuous (ContinuousMaps X Y) (ContinuousMaps X Z)
      compactOpenContinuousTopology compactOpenContinuousTopology
      (fun f => (⟨b, hb⟩ : ContinuousMaps Y Z).comp f) := by
  rw [compactOpenContinuousTopology_eq_mathlib, compactOpenContinuousTopology_eq_mathlib]
  exact ContinuousMap.continuous_postcomp (⟨b, hb⟩ : ContinuousMaps Y Z)

end D10Topology.Ch13
