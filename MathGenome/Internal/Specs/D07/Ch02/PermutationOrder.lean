import MathGenome.Internal.Specs.D07.Ch02.CycleDecomposition
import MathGenome.Internal.Specs.D07.Ch02.OrderDivisibility

/-!
Independent specification of `K07.02.permutation_order`
(paper.tex:518–524, chapters/M07.02.tex:96–102).

The cycles are the actual lists of distinct entries in the upstream
`Decomposition` predicate. Their lengths, rather than the cardinality of
the ambient set, determine the order. `foldr Nat.lcm 1` is the ordinary
least common multiple, including value one for the empty list. The carrier
may be empty, and the permutation may be the identity.
-/

namespace Specs.D07.Ch02.PermutationOrder

universe u

/-- The formula holds for every written disjoint-cycle decomposition. -/
def OrderFromCycleLengths : Prop :=
  ∀ (X : Type u) [Finite X] (σ : Equiv.Perm X) (L : List (List X)),
    CycleDecomposition.Decomposition σ L →
      orderOf σ = (L.map List.length).foldr Nat.lcm 1

/-- Every finite permutation admits the decomposition used in the formula. -/
def ExistsDecompositionWithOrder : Prop :=
  ∀ (X : Type u) [Finite X] (σ : Equiv.Perm X),
    ∃ L : List (List X), CycleDecomposition.Decomposition σ L ∧
      orderOf σ = (L.map List.length).foldr Nat.lcm 1

/-- The empty least common multiple and the identity's order are both one,
including on the empty carrier. -/
def EmptyCycleLengths : Prop :=
  ∀ (X : Type u) [Finite X],
    CycleDecomposition.Decomposition (1 : Equiv.Perm X) [] ∧
      (([] : List (List X)).map List.length).foldr Nat.lcm 1 = 1 ∧
      orderOf (1 : Equiv.Perm X) = 1

end Specs.D07.Ch02.PermutationOrder
