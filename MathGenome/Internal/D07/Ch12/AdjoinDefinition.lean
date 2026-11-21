import MathGenome.Internal.Specs.D07.Ch12.AdjoinDefinition

/-! Generated fields, simple adjunctions, and composita in a specified extension.
Mathlib's subfield closure is defined as an intersection, so the canonical
intermediate-field construction has exactly the source's defining carrier. -/

universe u v

namespace D07.Ch12.AdjoinDefinition

open Specs.D07.Ch12.AdjoinDefinition

abbrev generatedField (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (S : Set L) : IntermediateField K L :=
  IntermediateField.adjoin K S

abbrev simpleField (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (α : L) : IntermediateField K L :=
  generatedField K L {α}

abbrev compositum (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E F : IntermediateField K L) : IntermediateField K L :=
  generatedField K L ((E : Set L) ∪ (F : Set L))

theorem adjoin_intersection : AdjoinIntersection.{u, v} := by
  intro K L _ _ _ S
  rfl

theorem defining_family_nonempty : DefiningFamilyNonempty.{u, v} := by
  intro K L _ _ _ S
  exact ⟨⊤, Set.subset_univ _⟩

theorem adjoin_contains : AdjoinContains.{u, v} := by
  intro K L _ _ _ S
  exact ⟨IntermediateField.set_range_subset _, IntermediateField.subset_adjoin K S⟩

theorem adjoin_least : AdjoinLeast.{u, v} := by
  intro K L _ _ _ S E
  exact IntermediateField.adjoin_le_iff

theorem adjoin_field_operations : AdjoinFieldOperations.{u, v} := by
  intro K L _ _ _ S
  refine ⟨(IntermediateField.adjoin K S).zero_mem,
    (IntermediateField.adjoin K S).one_mem, ?_⟩
  intro x hx y hy
  exact ⟨sub_mem hx hy, mul_mem hx hy, inv_mem hx⟩

theorem simple_field_least : SimpleFieldLeast.{u, v} := by
  intro K L _ _ _ α E
  exact IntermediateField.adjoin_simple_le_iff

theorem compositum_sup : CompositumSup.{u, v} := by
  intro K L _ _ _ E F
  exact (IntermediateField.sup_def E F).symm

theorem compositum_least : CompositumLeast.{u, v} := by
  intro K L _ _ _ E F
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact IntermediateField.subset_adjoin K _ (Or.inl hx)
  · intro x hx
    exact IntermediateField.subset_adjoin K _ (Or.inr hx)
  · intro T hE hF
    apply IntermediateField.adjoin_le_subfield
    · exact (IntermediateField.set_range_subset E).trans hE
    · exact Set.union_subset hE hF

theorem infimum_intersection : InfimumIntersection.{u, v} := by
  intro K L _ _ _ E F
  exact ⟨IntermediateField.coe_inf E F, fun _ => le_inf_iff⟩

theorem empty_adjoin : EmptyAdjoin.{u, v} := by
  intro K L _ _ _
  rw [IntermediateField.adjoin_empty]
  exact IntermediateField.coe_bot

end D07.Ch12.AdjoinDefinition
