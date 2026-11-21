import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder

/-! Independent statements of the coloring bounds in paper.tex W57 (2113–2132).
The degree and natural chromatic number are the common W35 and W56 objects.
The removal-order equivalence is supplied by the upstream W57 interface.
No nonemptiness or positivity hypotheses are imposed. -/

universe u
namespace Specs.FiniteCombinatorics.Graph.Coloring.Greedy

open Specs.FiniteCombinatorics.Graph

def colorable_of_degenerateType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (d : ℕ),
    DegeneracyOrder.IsDegenerateValue G d → Nonempty (Foundations.KColoringValue G (d + 1))

def chromaticNumber_le_of_degenerateType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (d : ℕ),
    DegeneracyOrder.IsDegenerateValue G d → Foundations.chromaticNumberValue G ≤ d + 1

/-- A version independent of a chosen finite enumeration of the vertices. -/
def chromaticNumber_le_of_degree_leType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (Δ : ℕ),
    (∀ v, Graph.Foundations.degreeValue G v ≤ Δ) →
      Foundations.chromaticNumberValue G ≤ Δ + 1

def chromaticNumber_le_maxDegreeType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Foundations.chromaticNumberValue G ≤ G.maxDegree + 1

/-- Mathlib's maximum degree has the source's value zero on an empty vertex set. -/
def empty_maxDegreeType : Prop :=
  ∀ {V : Type u} [Fintype V] [IsEmpty V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree = 0

end Specs.FiniteCombinatorics.Graph.Coloring.Greedy
