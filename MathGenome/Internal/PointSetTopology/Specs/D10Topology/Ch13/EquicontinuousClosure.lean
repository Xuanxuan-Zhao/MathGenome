import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies

/-! Independent statements for paper.tex, d10:13:equicontinuous-closure.
The closure is in the product topology on all maps, including discontinuous
maps. The final equality is between the two induced topologies on the same
subtype of continuous maps. No compactness or completeness is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
universe u v
namespace Specs.D10Topology.Ch13.EquicontinuousClosure
open FunctionTopologies

def pointwise_closure_equicontinuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y)), Equicontinuous A →
    ∀ x : X, ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 x,
      ∀ y ∈ U, ∀ g ∈ @closure (X → Y) pointwiseTopology
        ((fun f : ContinuousMaps X Y => (f : X → Y)) '' A),
        dist (g y) (g x) < ε

def pointwise_closure_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y)), Equicontinuous A →
    ∀ g ∈ @closure (X → Y) pointwiseTopology
      ((fun f : ContinuousMaps X Y => (f : X → Y)) '' A), Continuous g

def equicontinuous_relative_topologies_eq : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (E : Set (ContinuousMaps X Y)), Equicontinuous E →
    TopologicalSpace.induced (fun f : E => f.val) pointwiseContinuousTopology =
    TopologicalSpace.induced (fun f : E => f.val) compactConvergenceContinuousTopology

end Specs.D10Topology.Ch13.EquicontinuousClosure
