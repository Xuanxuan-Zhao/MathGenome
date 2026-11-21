import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.AlternatingReach

/-! Hall's theorem (paper.tex, W51), with the designated left part.
The matching and neighbor set are the shared edge-set and bipartite-search
objects. Neither part is required to be inhabited or to have the other's size. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Matching.Hall

open FiniteCombinatorics.Graph.Matching.Alternating
open Specs.FiniteCombinatorics.Graph.Matching.Foundations

/-- A matching saturates precisely the specified left part; the condition ranges
 over every subset of that part, including the empty subset. -/
def hallType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (L R : Set V),
    Bipartition G L R →
    ((∃ M : Set (Sym2 V), IsMatchingValue G M ∧
        ∀ x ∈ L, SaturatedValue M x) ↔
      ∀ X : Set V, X ⊆ L → Nat.card X ≤ Nat.card (neighbors G R X))

end Specs.FiniteCombinatorics.Graph.Matching.Hall
