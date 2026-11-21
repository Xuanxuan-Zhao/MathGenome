import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.ActiveRows
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fin.VecNotation

/-! The triangle example following W35, paper.tex 1663–1669.
The coordinates enumerate the unordered edges 01, 12, 20 of the complete
simple graph on three vertices. Degree inequalities use actual incidence. -/
noncomputable section

namespace P205.Matching.Triangle

abbrev Vertex := Fin 3
abbrev Edge := Fin 3
abbrev Coordinate := P205.Polyhedra.Coordinate 3

/-- The finite simple triangle `K₃`. -/
def graph : SimpleGraph Vertex := ⊤

/-- The three distinct unordered graph edges, in coordinate order. -/
def edge : Edge → Sym2 Vertex := ![s(0, 1), s(1, 2), s(2, 0)]

/-- Sum of the coordinates incident to a vertex. -/
def degreeSum (x : Coordinate) (v : Vertex) : ℝ :=
  ∑ e : Edge, if v ∈ edge e then x e else 0

/-- Nonnegative edge weights with degree at most one at every vertex. -/
def degreeRelaxation : Set Coordinate :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ v, degreeSum x v ≤ 1}

/-- The half-integral point of the example. -/
def half : Coordinate := fun _ => 1 / 2

/-- Integral means that every edge coordinate is an integer. -/
def Integral (x : Coordinate) : Prop := ∀ e, ∃ z : ℤ, x e = (z : ℝ)

namespace Expected

def edgeEnumeration : Prop := Function.Injective edge ∧
  ∀ s : Sym2 Vertex, s ∈ graph.edgeSet ↔ ∃ e : Edge, edge e = s

def halfFeasible : Prop := half ∈ degreeRelaxation

def halfVertex : Prop := half ∈ degreeRelaxation.extremePoints ℝ

def halfNotIntegral : Prop := ¬ Integral half

/-- All actual graph matchings, including the empty matching, are covered. -/
def matchingSize : Prop := ∀ M : graph.Subgraph,
  M.IsMatching → M.edgeSet.ncard ≤ 1

end Expected
end P205.Matching.Triangle
