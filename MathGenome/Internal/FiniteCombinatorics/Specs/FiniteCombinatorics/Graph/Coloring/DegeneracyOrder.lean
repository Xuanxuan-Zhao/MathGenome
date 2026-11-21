import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations

/-! Independent specification of the removal-order assertion in paper.tex, W57.
Induced subgraphs range over all vertex subsets. An order is a duplicate-free
list containing every vertex. Its tail at a vertex consists of the later vertices.
The neighbor counts count vertices, rather than occurrences in a list. -/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder

def IsDegenerateType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ → Prop

def IsDegenerateValue : IsDegenerateType := fun {_} _ G d =>
  ∀ S : Set _, S.Nonempty → ∃ v : S, Foundations.degreeValue (G.induce S) v ≤ d

def LaterBoundType := ∀ {V : Type u}, SimpleGraph V → ℕ → List V → Prop

def LaterBoundValue {V : Type u} (G : SimpleGraph V) (d : ℕ) : List V → Prop
  | [] => True
  | v :: l => Nat.card {w : V // w ∈ l ∧ G.Adj v w} ≤ d ∧ LaterBoundValue G d l

def IsRemovalOrderType := ∀ {V : Type u}, SimpleGraph V → ℕ → List V → Prop

def IsRemovalOrderValue : IsRemovalOrderType := fun {_} G d l =>
  l.Nodup ∧ (∀ v, v ∈ l) ∧ LaterBoundValue G d l

def degeneracy_iff_removal_orderType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (d : ℕ),
    IsDegenerateValue G d ↔ ∃ l : List V, IsRemovalOrderValue G d l

/-- When the vertices still present are the current vertex and the tail,
its degree in the remaining induced graph is exactly its later-neighbor count. -/
def degree_removal_correspondenceType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V) (l : List V),
    Foundations.degreeValue (G.induce {w | w = v ∨ w ∈ l}) ⟨v, Or.inl rfl⟩ =
      Nat.card {w : V // w ∈ l ∧ G.Adj v w}

def empty_removal_orderType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] (G : SimpleGraph V) (d : ℕ),
    IsRemovalOrderValue G d [] ∧ IsDegenerateValue G d ∧
      ∀ l : List V, IsRemovalOrderValue G d l → l = []

end Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder
