import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.ComponentsAndPaths
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The exact subsets of the usual real plane in paper.tex, d10:06:sine-curve.
The graph includes t = 1 and excludes t = 0. The added set is the entire
closed vertical segment. All subset topologies are induced from ℝ × ℝ. -/

namespace D10Topology.Ch06.SineCurveData

noncomputable def graph : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ 1 ∧ p.2 = Real.sin (1 / p.1)}

def vertical : Set (ℝ × ℝ) :=
  {p | p.1 = 0 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1}

noncomputable def curve : Set (ℝ × ℝ) := graph ∪ vertical

end D10Topology.Ch06.SineCurveData

namespace Specs.D10Topology.Ch06.SineCurveClosure
open _root_.D10Topology.Ch06

def subsetType := Set (ℝ × ℝ)
noncomputable def graphValue : subsetType := SineCurveData.graph
def verticalValue : subsetType := SineCurveData.vertical
noncomputable def curveValue : subsetType := SineCurveData.curve

def graph_closure : Prop := closure SineCurveData.graph = SineCurveData.curve

def graph_connected : Prop := ConnectednessData.ConnectedSubset SineCurveData.graph

def graph_pathConnected : Prop := ComponentsPathsData.PathConnectedSubset SineCurveData.graph

def vertical_pathConnected : Prop :=
  ComponentsPathsData.PathConnectedSubset SineCurveData.vertical

def curve_connected : Prop := ConnectednessData.ConnectedSubset SineCurveData.curve

end Specs.D10Topology.Ch06.SineCurveClosure
