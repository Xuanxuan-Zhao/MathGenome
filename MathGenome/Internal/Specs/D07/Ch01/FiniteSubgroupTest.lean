import MathGenome.Internal.Specs.D07.Ch01.SubgroupDefinitionTest
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Group.Int

/-!
Independent specification of `K07.01.finite_subgroup_test`
(paper.tex:264–270, chapters/M07.01.tex:49–55).

Only the subset is assumed finite; the ambient group may be infinite,
noncommutative, or trivial. The boundary example uses the actual additive
group of integers and its strictly positive subset.
-/

namespace Specs.D07.Ch01.FiniteSubgroupTest

universe u

/-- Every finite nonempty multiplicatively closed subset is a subgroup
carrier, with all operations inherited from the ambient group. -/
def FiniteClosedSubsetIsSubgroup : Prop :=
  ∀ (G : Type u) [Group G] (s : Set G),
    s.Finite → s.Nonempty →
      (∀ x ∈ s, ∀ y ∈ s, x * y ∈ s) →
        ∃ H : Subgroup G, (H : Set G) = s

/-- Dropping finiteness fails: the strictly positive integers are nonempty
and additively closed but are not the carrier of an additive subgroup. -/
def PositiveIntegersCounterexample : Prop :=
  ({z : ℤ | 0 < z} : Set ℤ).Nonempty ∧
    (∀ x ∈ ({z : ℤ | 0 < z} : Set ℤ),
      ∀ y ∈ ({z : ℤ | 0 < z} : Set ℤ),
        x + y ∈ ({z : ℤ | 0 < z} : Set ℤ)) ∧
    ¬ (∃ H : AddSubgroup ℤ, (H : Set ℤ) = {z : ℤ | 0 < z})

end Specs.D07.Ch01.FiniteSubgroupTest
