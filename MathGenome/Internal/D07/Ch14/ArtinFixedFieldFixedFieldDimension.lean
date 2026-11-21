import MathGenome.Internal.D07.Ch14.FixedField
import MathGenome.Internal.Specs.D07.Ch14.ArtinFixedFieldFixedFieldDimension

/-!
The finite dimension and degree parts of Artin's fixed-field theorem.
Mathlib's fixed-point dimension theorem uses no finite-degree assumption.
Its upper bound proves finite dimension from finiteness of the acting group;
Dedekind independence gives the opposite inequality for a faithful action.
-/

universe u v

namespace D07.Ch14.ArtinFixedFieldFixedFieldDimension

open Specs.D07.Ch14.ArtinFixedFieldFixedFieldDimension

/-- A faithful finite group of field automorphisms has degree equal to its
order over its fixed field, including a group of order one. -/
theorem faithful_action_dimension : FaithfulActionDimension.{u, v} := by
  intro H L _ _ _ _ _
  let _ : Fintype H := Fintype.ofFinite H
  exact ⟨inferInstance, (FixedPoints.finrank_eq_card H L).trans
    (Nat.card_eq_fintype_card.symm)⟩

/-- Specialization to the upstream intermediate fixed field, with the
canonical evaluation action of the subgroup. -/
theorem subgroup_fixed_field_dimension : SubgroupFixedFieldDimension.{u, v} := by
  intro K L _ _ _ H _
  exact faithful_action_dimension H L

end D07.Ch14.ArtinFixedFieldFixedFieldDimension
