import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Directed.Foundations

/-! Canonical search objects for paper.tex, Lemma `p204:alternating-reach`.
Arcs retain ordered endpoints and their orientation proof; reachability uses
exactly the shared directed-walk type, including its empty walks. -/
universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Matching.Alternating
open Specs.FiniteCombinatorics.Graph.Matching.Foundations

variable {V : Type u} [Fintype V]

/-- The two parts partition all vertices, and every edge crosses the partition. -/
structure Bipartition (G : SimpleGraph V) (L R : Set V) : Prop where
  disjoint : Disjoint L R
  cover : L ∪ R = Set.univ
  crosses : ∀ ⦃x y⦄, G.Adj x y → (x ∈ L ∧ y ∈ R) ∨ (x ∈ R ∧ y ∈ L)

/-- Nonmatching edges point left to right; matching edges point right to left. -/
def Oriented (G : SimpleGraph V) (L R : Set V) (M : Set (Sym2 V)) (x y : V) : Prop :=
  G.Adj x y ∧ ((x ∈ L ∧ y ∈ R ∧ s(x, y) ∉ M) ∨
    (x ∈ R ∧ y ∈ L ∧ s(x, y) ∈ M))

def SearchArc (G : SimpleGraph V) (L R : Set V) (M : Set (Sym2 V)) :=
  {xy : V × V // Oriented G L R M xy.1 xy.2}

noncomputable instance (G : SimpleGraph V) (L R : Set V) (M : Set (Sym2 V)) :
    Fintype (SearchArc G L R M) := by
  classical
  unfold SearchArc
  infer_instance

def searchDigraph (G : SimpleGraph V) (L R : Set V) (M : Set (Sym2 V)) :
    Directed.Digraph V (SearchArc G L R M) where
  tail a := a.val.1
  head a := a.val.2

def roots (L : Set V) (M : Set (Sym2 V)) : Set V :=
  {x | x ∈ L ∧ ¬ SaturatedValue M x}

def reached (G : SimpleGraph V) (L R : Set V) (M : Set (Sym2 V)) : Set V :=
  {y | ∃ x ∈ roots L M, Directed.Spec.reachable (searchDigraph G L R M) x y}

def leftReach (G : SimpleGraph V) (L R : Set V) (M : Set (Sym2 V)) : Set V :=
  L ∩ reached G L R M

def rightReach (G : SimpleGraph V) (L R : Set V) (M : Set (Sym2 V)) : Set V :=
  R ∩ reached G L R M

def neighbors (G : SimpleGraph V) (R S : Set V) : Set V :=
  {y | y ∈ R ∧ ∃ x ∈ S, G.Adj x y}

end FiniteCombinatorics.Graph.Matching.Alternating

namespace Specs.FiniteCombinatorics.Graph.Matching.AlternatingReach
open FiniteCombinatorics.Graph.Matching.Alternating
open Specs.FiniteCombinatorics.Graph.Matching.Foundations

/-- The equivalence is explicitly required to send each vertex to its matching
partner, rather than merely assert equality of the two cardinalities. -/
def alternating_reachabilityType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (L R : Set V)
    (M : Set (Sym2 V)), Bipartition G L R → IsMatchingValue G M →
    (∀ N : Set (Sym2 V), IsMatchingValue G N → Nat.card N ≤ Nat.card M) →
    rightReach G L R M = neighbors G R (leftReach G L R M) ∧
    (∀ y ∈ rightReach G L R M, SaturatedValue M y) ∧
    ∃ e : ↥(rightReach G L R M) ≃ ↥(leftReach G L R M \ roots L M),
      ∀ y, s(y.val, (e y).val) ∈ M

end Specs.FiniteCombinatorics.Graph.Matching.AlternatingReach
