import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.SineCurveClosure

/-! Full conclusions for the exact subsets in paper.tex, d10:06:sine-curve.
All path components below are computed in the subspace `curve`, not in the plane. -/
namespace Specs.D10Topology.Ch06.SineCurvePathComponents
open Set
open _root_.D10Topology.Ch06
open SineCurveData

def no_path : Prop :=
  ∀ x ∈ graph, ∀ y ∈ vertical, ¬ JoinedIn curve x y

def graph_component : Prop :=
  ∀ x : curve, x.val ∈ graph →
    ComponentsPathsData.PathComponent x = {y : curve | y.val ∈ graph}

def vertical_component : Prop :=
  ∀ x : curve, x.val ∈ vertical →
    ComponentsPathsData.PathComponent x = {y : curve | y.val ∈ vertical}

def exactly_two_components : Prop :=
  {A : Set curve | ∃ x : curve, ComponentsPathsData.PathComponent x = A} =
    {{y : curve | y.val ∈ graph}, {y : curve | y.val ∈ vertical}} ∧
    ({y : curve | y.val ∈ graph} : Set curve) ≠ {y : curve | y.val ∈ vertical}

def graph_not_closed : Prop :=
  ¬ IsClosed ({y : curve | y.val ∈ graph} : Set curve)

def complete_result : Prop :=
  closure graph = curve ∧ ConnectednessData.ConnectedSubset curve ∧
    exactly_two_components ∧ graph_not_closed

end Specs.D10Topology.Ch06.SineCurvePathComponents
