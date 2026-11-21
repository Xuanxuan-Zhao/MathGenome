import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
Independent specification of `K07.05.conjugacy_counting`, paper.tex:891–898.
Both formulas assume only that the group is finite. The second counts distinct
subgroups, rather than conjugating elements with multiplicities. Its predicate
spells out equality with the conjugate set gHg⁻¹, with the source's order.
-/

namespace Specs.D07.Ch05.ConjugacyCounting

universe u

/-- The cardinality of the conjugacy class of an element. -/
def ConjugacyClassCardEqIndex : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (x : G),
    Nat.card ↥(ConjClasses.mk x).carrier = (Subgroup.centralizer {x}).index

/-- The number of distinct conjugate subgroups of H. -/
def ConjugateSubgroupsCardEqIndex : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G),
    Nat.card {K : Subgroup G //
      ∃ g : G, (fun h : G => g * h * g⁻¹) '' (H : Set G) = (K : Set G)} =
        (Subgroup.normalizer (H : Set G)).index

end Specs.D07.Ch05.ConjugacyCounting
