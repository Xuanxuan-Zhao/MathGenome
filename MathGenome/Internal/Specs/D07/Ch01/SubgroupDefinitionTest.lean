import MathGenome.Internal.Specs.D07.Ch01.GroupDefinition
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
Independent specification of `K07.01.subgroup_definition_test`
(paper.tex:253–262, chapters/M07.01.tex:38–47).

A subset is a subgroup exactly when it is the carrier of a canonical
`Subgroup G`. The closure characterization relates that bundled object to
the source definition. Both tests concern arbitrary subsets of arbitrary
groups; no finiteness, commutativity, or nontriviality is required.
-/

namespace Specs.D07.Ch01.SubgroupDefinitionTest

universe u

/-- The source's three closure conditions characterize subgroup carriers. -/
def SubgroupIffClosed : Prop :=
  ∀ (G : Type u) [Group G] (s : Set G),
    (∃ H : Subgroup G, (H : Set G) = s) ↔
      (1 : G) ∈ s ∧
      (∀ x ∈ s, ∀ y ∈ s, x * y ∈ s) ∧
      (∀ x ∈ s, x⁻¹ ∈ s)

/-- The subgroup is a group with exactly the ambient operations, including
the ambient identity, rather than an independently chosen identity. -/
def InheritedGroupOperations : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    GroupDefinition.groupAxiomsValue H (· * ·) 1 Inv.inv ∧
      ((1 : H) : G) = 1 ∧
      (∀ x y : H, ((x * y : H) : G) = (x : G) * (y : G)) ∧
      (∀ x : H, ((x⁻¹ : H) : G) = (x : G)⁻¹)

/-- First subgroup test, with nonemptiness stated separately from closure. -/
def MulInvTest : Prop :=
  ∀ (G : Type u) [Group G] (s : Set G),
    (∃ H : Subgroup G, (H : Set G) = s) ↔
      s.Nonempty ∧ (∀ x ∈ s, ∀ y ∈ s, x * y⁻¹ ∈ s)

/-- Second subgroup test, with the order of multiplication preserved. -/
def InvMulTest : Prop :=
  ∀ (G : Type u) [Group G] (s : Set G),
    (∃ H : Subgroup G, (H : Set G) = s) ↔
      s.Nonempty ∧ (∀ x ∈ s, ∀ y ∈ s, x⁻¹ * y ∈ s)

end Specs.D07.Ch01.SubgroupDefinitionTest
