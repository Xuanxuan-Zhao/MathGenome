import MathGenome.Internal.D07.Ch14.FixedField
import MathGenome.Internal.Specs.D07.Ch14.InclusionReversal

/-! The antitone fixed-field/fixing-subgroup connection for arbitrary extensions.
These statements use the same canonical objects as D07.Ch14.FixedField.
-/

universe u v

namespace D07.Ch14.InclusionReversal

open Specs.D07.Ch14.InclusionReversal

theorem fixing_subgroup_inclusion_reversal : FixingSubgroupInclusionReversal.{u, v} := by
  intro K L _ _ _ E₁ E₂ h
  exact IntermediateField.fixingSubgroup_le h

theorem fixed_field_inclusion_reversal : FixedFieldInclusionReversal.{u, v} := by
  intro K L _ _ _ H₁ H₂ h
  exact IntermediateField.fixedField_le h

theorem le_fixed_field_iff_le_fixing_subgroup : LeFixedFieldIffLeFixingSubgroup.{u, v} := by
  intro K L _ _ _ E H
  exact IntermediateField.le_iff_le H E

end D07.Ch14.InclusionReversal
