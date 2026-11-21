import MathGenome.Internal.D07.Ch12.AdjoinDefinition
import MathGenome.Internal.D07.Ch14.AutomorphismGroup
import MathGenome.Internal.Specs.D07.Ch14.FixedField

/-! Fixed fields and fixing subgroups for arbitrary field extensions.
The two constructions are Mathlib's canonical intermediate field and subgroup.
The scalar-change equivalence changes only the record of which base is fixed.
-/

universe u v

namespace D07.Ch14.FixedField

open Specs.D07.Ch14.FixedField

/-- The intermediate field of elements fixed by every member of H. -/
abbrev fixedField (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (H : Subgroup (AutomorphismGroup.Aut K L)) : IntermediateField K L :=
  IntermediateField.fixedField H

/-- The subgroup of K-automorphisms fixing E pointwise. -/
abbrev fixingSubgroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) : Subgroup (AutomorphismGroup.Aut K L) :=
  E.fixingSubgroup

/-- Keeping the same maps identifies the fixing subgroup with Aut_E(L). -/
def fixingSubgroupEquiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) : fixingSubgroup K L E ≃* (L ≃ₐ[E] L) :=
  E.fixingSubgroupEquiv

theorem fixed_field_carrier : FixedFieldCarrier.{u, v} := by
  intro K L _ _ _ H
  ext x
  exact IntermediateField.mem_fixedField_iff H x

theorem fixed_field_operations : FixedFieldOperations.{u, v} := by
  intro K L _ _ _ H
  let F := fixedField K L H
  refine ⟨F.algebraMap_mem, F.zero_mem, F.one_mem, ?_⟩
  intro a ha b hb
  exact ⟨F.sub_mem ha hb, F.mul_mem ha hb, F.inv_mem ha⟩

theorem fixing_subgroup_carrier : FixingSubgroupCarrier.{u, v} := by
  intro K L _ _ _ E
  ext σ
  exact IntermediateField.mem_fixingSubgroup_iff E σ

theorem fixing_subgroup_operations : FixingSubgroupOperations.{u, v} := by
  intro K L _ _ _ E
  let G := fixingSubgroup K L E
  refine ⟨G.one_mem, ?_⟩
  intro σ hσ τ hτ
  exact ⟨G.mul_mem hσ hτ, G.inv_mem hσ⟩

theorem fixing_subgroup_equiv_maps : FixingSubgroupEquivMaps.{u, v} := by
  intro K L _ _ _ E
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end D07.Ch14.FixedField
