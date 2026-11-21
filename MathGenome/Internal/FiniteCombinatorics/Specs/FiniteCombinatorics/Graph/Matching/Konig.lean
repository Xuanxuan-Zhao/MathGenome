import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.AlternatingReach

/-! Independent statement of paper.tex, W52. The cover is a subset of the full
vertex type, which is partitioned by L and R. No nonemptiness is assumed. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Matching.Konig
open Specs.FiniteCombinatorics.Graph.Matching.Foundations
open FiniteCombinatorics.Graph.Matching.Alternating

/-- An attained maximum matching and an attained minimum vertex cover have the
same cardinality. The two universal inequalities specify the extrema. -/
def konig_matching_coverType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (L R : Set V),
    Bipartition G L R →
    ∃ (M : Set (Sym2 V)) (C : Set V),
      IsMatchingValue G M ∧ IsVertexCoverValue G C ∧ Nat.card M = Nat.card C ∧
      (∀ N : Set (Sym2 V), IsMatchingValue G N → Nat.card N ≤ Nat.card M) ∧
      (∀ D : Set V, IsVertexCoverValue G D → Nat.card C ≤ Nat.card D)

end Specs.FiniteCombinatorics.Graph.Matching.Konig
