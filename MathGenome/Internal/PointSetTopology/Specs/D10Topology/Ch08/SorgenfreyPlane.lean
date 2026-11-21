import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.SorgenfreyLine
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.SorgenfreyLindelof
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Real.Cardinality

/-! Independent statements for paper.tex, d10:08:sorgenfrey-plane.
The underlying space is the actual real Cartesian square, with the product
of the two lower-limit topologies. The anti-diagonal has the induced topology.
Normality does not include T₁; the T₃ assertion includes both regularity and T₁.
-/
open Set TopologicalSpace
open scoped Cardinal

namespace Specs.D10Topology.Ch08.SorgenfreyPlane

@[instance_reducible] def topology : TopologicalSpace (ℝ × ℝ) :=
  letI : TopologicalSpace ℝ := Ch01.ElementaryTopologies.lowerLimitTopology
  inferInstance

def antiDiagonal : Set (ℝ × ℝ) := {p | p.1 + p.2 = 0}
def rationalPlane : Set (ℝ × ℝ) :=
  range ((↑) : ℚ → ℝ) ×ˢ range ((↑) : ℚ → ℝ)

def topologyType := TopologicalSpace (ℝ × ℝ)
def setType := Set (ℝ × ℝ)

local instance : TopologicalSpace (ℝ × ℝ) := topology

def antiDiagonal_eq_range : Prop := antiDiagonal = range (fun t : ℝ => (t, -t))
def rationals_countable : Prop := rationalPlane.Countable
def rationals_dense : Prop := Dense rationalPlane
def separable : Prop := SeparableSpace (ℝ × ℝ)
def firstCountable : Prop :=
  Ch04.FirstCountableSequences.FirstCountable topology
def t3 : Prop := RegularSpace (ℝ × ℝ) ∧ T1Space (ℝ × ℝ)
def antiDiagonal_closed : Prop := IsClosed antiDiagonal
def antiDiagonal_discrete : Prop := DiscreteTopology antiDiagonal
def antiDiagonal_cardinality : Prop := Cardinal.mk antiDiagonal = (2 : Cardinal) ^ ℵ₀
def antiDiagonal_not_separable : Prop := ¬ SeparableSpace antiDiagonal
def antiDiagonal_not_lindelof : Prop := ¬ LindelofSpace antiDiagonal
def not_lindelof : Prop := ¬ LindelofSpace (ℝ × ℝ)
def not_normal : Prop := ¬ NormalSpace (ℝ × ℝ)

/-- This particular closed subspace witnesses failure of closed heredity. -/
def closed_subspace_counterexample : Prop :=
  SeparableSpace (ℝ × ℝ) ∧ IsClosed antiDiagonal ∧ ¬ SeparableSpace antiDiagonal

/-- Each factor is both Lindelöf and normal, while their product has neither property. -/
def product_counterexample : Prop :=
  (@LindelofSpace ℝ Ch01.ElementaryTopologies.lowerLimitTopology ∧
    @NormalSpace ℝ Ch01.ElementaryTopologies.lowerLimitTopology) ∧
  ¬ LindelofSpace (ℝ × ℝ) ∧ ¬ NormalSpace (ℝ × ℝ)

end Specs.D10Topology.Ch08.SorgenfreyPlane
