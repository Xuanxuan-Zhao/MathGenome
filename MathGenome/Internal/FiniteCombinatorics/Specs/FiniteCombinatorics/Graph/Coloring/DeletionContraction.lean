import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Independent specification of paper.tex W60, lines 2236–2273.
The vertex quotient has the single potentially nonsingleton class `{u,v}`.
`SimpleGraph.map` discards loops and uses a proposition for adjacency, so parallel
images of edges impose only one constraint. -/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction

/-- Identify precisely the two endpoints. -/
def contractionSetoid {V : Type u} (u v : V) : Setoid V where
  r a b := a = b ∨ (a = u ∨ a = v) ∧ (b = u ∨ b = v)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro a b h
      rcases h with h | ⟨ha, hb⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hb, ha⟩
    trans := by
      intro a b c hab hbc
      rcases hab with rfl | ⟨ha, hb⟩
      · exact hbc
      rcases hbc with rfl | ⟨_, hc⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hc⟩ }

def ContractedVertex {V : Type u} (u v : V) := Quotient (contractionSetoid u v)

instance {V : Type u} [Finite V] (u v : V) : Finite (ContractedVertex u v) :=
  inferInstanceAs (Finite (Quotient (contractionSetoid u v)))

def contractVertex {V : Type u} (u v : V) (a : V) : ContractedVertex u v :=
  Quotient.mk _ a

def deleteEdge {V : Type u} (G : SimpleGraph V) (u v : V) : SimpleGraph V :=
  G.deleteEdges {s(u,v)}

/-- Push adjacency through the endpoint quotient after removing the edge. -/
def contractEdge {V : Type u} (G : SimpleGraph V) (u v : V) :
    SimpleGraph (ContractedVertex u v) :=
  (deleteEdge G u v).map (contractVertex u v)

def contractionSetoidType := ∀ {V : Type u}, V → V → Setoid V
abbrev contractionSetoidValue : contractionSetoidType := @contractionSetoid

def ContractedVertexType := ∀ {V : Type u}, V → V → Type u
abbrev ContractedVertexValue : ContractedVertexType := @ContractedVertex

def contractVertexType := ∀ {V : Type u} (u v : V), V → ContractedVertex u v
abbrev contractVertexValue : contractVertexType := @contractVertex

def deleteEdgeType := ∀ {V : Type u}, SimpleGraph V → V → V → SimpleGraph V
abbrev deleteEdgeValue : deleteEdgeType := @deleteEdge

def contractEdgeType := ∀ {V : Type u} (_G : SimpleGraph V) (u v : V),
  SimpleGraph (ContractedVertex u v)
abbrev contractEdgeValue : contractEdgeType := @contractEdge

def quotientIdentification : Prop := ∀ {V : Type u} (u v a b : V),
  contractVertex u v a = contractVertex u v b ↔
    a = b ∨ (a = u ∨ a = v) ∧ (b = u ∨ b = v)

def contractedAdjacency : Prop := ∀ {V : Type u} (G : SimpleGraph V) (u v : V)
  (a b : ContractedVertex u v),
  (contractEdge G u v).Adj a b ↔ a ≠ b ∧ ∃ x y : V,
    G.Adj x y ∧ s(x,y) ≠ s(u,v) ∧
      contractVertex u v x = a ∧ contractVertex u v y = b

def deletionContraction : Prop := ∀ {V : Type u} [Finite V]
  (G : SimpleGraph V) (u v : V), G.Adj u v →
  ChromaticPolynomial.chromaticPolynomial G =
    ChromaticPolynomial.chromaticPolynomial (deleteEdge G u v) -
      ChromaticPolynomial.chromaticPolynomial (contractEdge G u v)

end Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction
