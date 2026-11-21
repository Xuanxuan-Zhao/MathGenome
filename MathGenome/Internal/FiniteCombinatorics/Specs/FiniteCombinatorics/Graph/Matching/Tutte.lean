import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Foundations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Independent statement of paper.tex, W53 (and the notation immediately before it).
Deleting `S` means taking the induced graph on the surviving vertices `univ \ S`.
Component orders count their vertex supports; the empty graph has no components.
-/

universe u
noncomputable section

namespace Specs.FiniteCombinatorics.Graph.Matching.Tutte

def deletedGraphType := ∀ {V : Type u} [Finite V],
  SimpleGraph V → (S : Set V) → SimpleGraph ↥((Set.univ : Set V) \ S)

def deletedGraphValue : deletedGraphType := fun {_} _ G S =>
  G.induce (Set.univ \ S)

def oddComponentCountType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ

def oddComponentCountValue : oddComponentCountType := fun {_} _ G =>
  Nat.card {c : G.ConnectedComponent // Odd (Nat.card c.supp)}

def tutteType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    (∃ M : Set (Sym2 V),
      Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsPerfectMatchingValue G M) ↔
    ∀ S : Set V, oddComponentCountValue (deletedGraphValue G S) ≤ Nat.card S

end Specs.FiniteCombinatorics.Graph.Matching.Tutte
