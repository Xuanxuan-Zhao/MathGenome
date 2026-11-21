import MathGenome.Internal.Specs.D07.Ch02.CyclicDefinition
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Basic.Finite.Defs

/-!
Independent statements for `K07.02.cyclic_abelian_and_subgroups`
(paper.tex:461–467; chapters/M07.02.tex:39–45).

All groups carry their given multiplication. Cyclicity is the same integer-power
predicate used in the upstream cyclic-group definition. Neither commutativity
nor finiteness is assumed. Images are the actual homomorphism ranges, and the
surjective formulation also covers arbitrary presentations of an image group.
The final statement uses actual infinitude, and excludes only the bottom
subgroup. It records both infinite cyclicity and the integer-group model.
-/

namespace Specs.D07.Ch02.CyclicAbelianAndSubgroups

universe u v

/-- Any two elements of a cyclic group commute, including in the trivial case. -/
def CyclicAbelian : Prop :=
  ∀ (G : Type u) [Group G] [IsCyclic G], ∀ x y : G, x * y = y * x

/-- Every subgroup, with its inherited operations, is cyclic. -/
def SubgroupCyclic : Prop :=
  ∀ (G : Type u) [Group G] [IsCyclic G] (H : Subgroup G), IsCyclic H

/-- The range of every homomorphism from a cyclic group is cyclic. -/
def HomomorphicImageCyclic : Prop :=
  ∀ (G : Type u) (K : Type v) [Group G] [Group K] [IsCyclic G]
    (f : G →* K), IsCyclic f.range

/-- Equivalently, every group that is a surjective image is cyclic. -/
def SurjectiveImageCyclic : Prop :=
  ∀ (G : Type u) (K : Type v) [Group G] [Group K] [IsCyclic G]
    (f : G →* K), Function.Surjective f → IsCyclic K

/-- A nontrivial subgroup of an infinite cyclic group is infinite cyclic.
The equivalence changes only notation on the additive integer model. -/
def NontrivialSubgroupInfiniteCyclic : Prop :=
  ∀ (G : Type u) [Group G] [IsCyclic G] [Infinite G]
    (H : Subgroup G), H ≠ ⊥ →
      Infinite H ∧ IsCyclic H ∧ Nonempty (Multiplicative ℤ ≃* H)

end Specs.D07.Ch02.CyclicAbelianAndSubgroups
