import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies

/-! Independent statements of paper.tex, Proposition `d10:13:functorial-maps`.
The topologies on the continuous-map spaces are the previously defined
compact-open topologies, specified explicitly in each statement. -/

universe u v w z

namespace Specs.D10Topology.Ch13.FunctorialMaps

open Specs.D10Topology.Ch13.FunctionTopologies

def fixed_evaluation_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [tY : TopologicalSpace Y]
    (x : X),
    @Continuous (ContinuousMaps X Y) Y compactOpenContinuousTopology tY
      (fun f => f x)

def compactOpen_hausdorff : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y],
    @T2Space (ContinuousMaps X Y) compactOpenContinuousTopology

def fixed_precomposition_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} {W : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    (a : W → X) (ha : Continuous a),
    @Continuous (ContinuousMaps X Y) (ContinuousMaps W Y)
      compactOpenContinuousTopology compactOpenContinuousTopology
      (fun f => f.comp (⟨a, ha⟩ : ContinuousMaps W X))

def fixed_postcomposition_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (b : Y → Z) (hb : Continuous b),
    @Continuous (ContinuousMaps X Y) (ContinuousMaps X Z)
      compactOpenContinuousTopology compactOpenContinuousTopology
      (fun f => (⟨b, hb⟩ : ContinuousMaps Y Z).comp f)

end Specs.D10Topology.Ch13.FunctorialMaps
