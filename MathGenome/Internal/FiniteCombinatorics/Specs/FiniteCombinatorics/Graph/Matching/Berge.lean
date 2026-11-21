import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Foundations

/-! Independent statements for paper.tex, W50, including both constructions
in its proof. All graphs are finite and simple; no bipartition is assumed. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Matching.Berge
open Specs.FiniteCombinatorics.Graph.Matching.Foundations

def flipAlongType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V},
  Set (Sym2 V) → ∀ {a b : V}, G.Walk a b → Set (Sym2 V)

/-- Remove the matching edges on the path and insert its other edges. -/
def flipAlongValue : flipAlongType := fun {_} _ {_} M {_ _} p =>
  (M \ {e | e ∈ p.edges}) ∪ ({e | e ∈ p.edges} \ M)

def flip_augmentingType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (M : Set (Sym2 V))
    {a b : V} (p : G.Walk a b),
    IsAugmentingPathValue G M p →
      IsMatchingValue G (flipAlongValue M p) ∧
      Nat.card (flipAlongValue M p) = Nat.card M + 1

def larger_matching_augmentingType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (M N : Set (Sym2 V)),
    IsMatchingValue G M → IsMatchingValue G N → Nat.card M < Nat.card N →
      ∃ (a b : V) (p : G.Walk a b), IsAugmentingPathValue G M p

def maximum_has_no_augmenting_pathType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (M : Set (Sym2 V)),
    IsMatchingValue G M →
    (∀ N : Set (Sym2 V), IsMatchingValue G N → Nat.card N ≤ Nat.card M) →
      ¬ ∃ (a b : V) (p : G.Walk a b), IsAugmentingPathValue G M p

def berge_criterionType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (M : Set (Sym2 V)),
    IsMatchingValue G M →
      ((∀ N : Set (Sym2 V), IsMatchingValue G N → Nat.card N ≤ Nat.card M) ↔
        ¬ ∃ (a b : V) (p : G.Walk a b), IsAugmentingPathValue G M p)

end Specs.FiniteCombinatorics.Graph.Matching.Berge
