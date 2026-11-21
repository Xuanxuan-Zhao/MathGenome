import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Euler.Foundations

/-! Ore and Dirac conditions, paper.tex W40. Cardinality and degree are natural
numbers, so the integral form of the minimum degree condition is `n ≤ 2 * d`.
No connectivity hypothesis is imposed. -/
universe u
namespace Specs.FiniteCombinatorics.Graph.Hamilton.OreDirac

open Specs.FiniteCombinatorics.Graph.Foundations
open Specs.FiniteCombinatorics.Graph.Euler.Foundations

def oreType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), 3 ≤ Nat.card V →
    (∀ a b : V, a ≠ b → ¬ G.Adj a b →
      Nat.card V ≤ degreeValue G a + degreeValue G b) →
    ∃ (a : V) (p : G.Walk a a), IsHamiltonCycleValue G p

def diracType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), 3 ≤ Nat.card V →
    (∀ a : V, Nat.card V ≤ 2 * degreeValue G a) →
    ∃ (a : V) (p : G.Walk a a), IsHamiltonCycleValue G p

end Specs.FiniteCombinatorics.Graph.Hamilton.OreDirac
