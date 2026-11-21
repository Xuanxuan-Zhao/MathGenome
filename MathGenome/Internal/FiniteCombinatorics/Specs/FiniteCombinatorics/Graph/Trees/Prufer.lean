import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import Mathlib.Data.List.OfFn

/-! Independent statements for W41. The labelled trees have exactly the supplied
vertex type, not a quotient by graph isomorphism. Codes use ordered positions.
The relation records successive deletion of the least degree-one vertex. -/

universe u

namespace Specs.FiniteCombinatorics.Graph.Trees.Prufer

open Specs.FiniteCombinatorics.Graph.Foundations

abbrev LabelledTree (V : Type u) := {G : SimpleGraph V // G.IsTree}

abbrev Sequence (V : Type u) := Fin (Nat.card V - 2) → V

/-- The usual smallest-leaf code. At a recursive stage, all labels and all
edges are restricted to the complement of the deleted label. -/
inductive IsPruferCode : {V : Type u} → [Finite V] → [LinearOrder V] →
    SimpleGraph V → List V → Prop
  | pair {V : Type u} [Finite V] [LinearOrder V] (G : SimpleGraph V)
      (hG : G.IsTree) (hcard : Nat.card V = 2) : IsPruferCode G []
  | step {V : Type u} [Finite V] [LinearOrder V] (G : SimpleGraph V)
      (hG : G.IsTree) (hcard : 3 ≤ Nat.card V) (b a : V)
      (hb : degreeValue G b = 1)
      (hmin : ∀ v, degreeValue G v = 1 → b ≤ v)
      (ha : G.Adj b a) (tail : List ({b}ᶜ : Set V))
      (htail : IsPruferCode (G.induce {b}ᶜ) tail) :
      IsPruferCode G (a :: tail.map Subtype.val)

def prufer_bijectionType : Prop :=
  ∀ (V : Type u) [Finite V] [LinearOrder V], 2 ≤ Nat.card V →
    ∃ e : LabelledTree V ≃ Sequence V, ∀ T : LabelledTree V,
      IsPruferCode T.val (List.ofFn (e T)) ∧
        ∀ v : V, (List.ofFn (e T)).count v = degreeValue T.val v - 1

def cayleyType : Prop :=
  ∀ (V : Type u) [Finite V] [LinearOrder V], 2 ≤ Nat.card V →
    Nat.card (LabelledTree V) = (Nat.card V) ^ (Nat.card V - 2)

def singleton_tree_countType : Prop :=
  ∀ (V : Type u) [Finite V], Nat.card V = 1 → Nat.card (LabelledTree V) = 1

/-- Useful separately checkable forward direction of the construction. -/
def encoding_existsType : Prop :=
  ∀ (V : Type u) [Finite V] [LinearOrder V] (G : SimpleGraph V),
    G.IsTree → 2 ≤ Nat.card V → ∃ c : List V, IsPruferCode G c

def encoding_statisticsType : Prop :=
  ∀ (V : Type u) [Finite V] [LinearOrder V] (G : SimpleGraph V) (c : List V),
    IsPruferCode G c → c.length = Nat.card V - 2 ∧
      ∀ v : V, c.count v = degreeValue G v - 1

end Specs.FiniteCombinatorics.Graph.Trees.Prufer
