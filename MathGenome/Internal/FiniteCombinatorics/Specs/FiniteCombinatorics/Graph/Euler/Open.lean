import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Euler.Foundations

/-! W39: open Euler trails, with isolated vertices allowed. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Euler.Open
open Specs.FiniteCombinatorics.Graph.Euler.Foundations
open Specs.FiniteCombinatorics.Graph.Foundations

def open_eulerTrail_odd_degreeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) {a b : V} (p : G.Walk a b),
    IsEulerTrailValue G p → IsOpenValue G p →
      ∀ w, Odd (degreeValue G w) ↔ w = a ∨ w = b

def exists_eulerTrail_of_odd_endpointsType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), G.edgeSet.Nonempty →
    (edgeSupportValue G).Connected → ∀ (a b : V), a ≠ b →
      (∀ w, Odd (degreeValue G w) ↔ w = a ∨ w = b) →
        ∃ p : G.Walk a b, IsEulerTrailValue G p ∧ IsOpenValue G p

def open_eulerTrail_iff_two_odd_degreeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), G.edgeSet.Nonempty →
    (edgeSupportValue G).Connected →
      ((∃ (a b : V) (p : G.Walk a b), IsEulerTrailValue G p ∧ IsOpenValue G p) ↔
        ∃ a b : V, a ≠ b ∧ ∀ w, Odd (degreeValue G w) ↔ w = a ∨ w = b)

def open_eulerTrail_iff_card_odd_degreeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), G.edgeSet.Nonempty →
    (edgeSupportValue G).Connected →
      ((∃ (a b : V) (p : G.Walk a b), IsEulerTrailValue G p ∧ IsOpenValue G p) ↔
        Nat.card {w : V // Odd (degreeValue G w)} = 2)

end Specs.FiniteCombinatorics.Graph.Euler.Open
