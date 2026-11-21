import MathGenome.Internal.Specs.D07.Ch14.FundamentalCorrespondence
import MathGenome.Internal.D07.Ch14.InclusionReversal

/-!
The finite Galois correspondence, K07.14.fundamental_correspondence.

Mathlib's two inverse lemmas implement the source's argument: Artin's
fixed-field theorem identifies the fixing subgroup of a fixed field;
normality and separability over each intermediate base give the reverse
identity by the automorphism count and equality of extension degrees.
We assemble the specified maps into an order isomorphism with the dual
subgroup lattice, using the upstream inclusion-reversal theorem.
-/

universe u v

namespace D07.Ch14.FundamentalCorrespondence

open Specs.D07.Ch14.FundamentalCorrespondence

theorem fixed_field_fixing_subgroup : FixedFieldFixingSubgroup.{u, v} := by
  intro K L _ _ _ _ _ E
  exact IsGalois.fixedField_fixingSubgroup E

theorem fixing_subgroup_fixed_field : FixingSubgroupFixedField.{u, v} := by
  intro K L _ _ _ _ _ H
  exact IntermediateField.fixingSubgroup_fixedField H

theorem antitone_bijections : AntitoneBijections.{u, v} := by
  intro K L _ _ _ _ _
  let e : IntermediateField K L ≃ Subgroup (L ≃ₐ[K] L) :=
    { toFun := FixedField.fixingSubgroup K L
      invFun := FixedField.fixedField K L
      left_inv := fixed_field_fixing_subgroup K L
      right_inv := fixing_subgroup_fixed_field K L }
  exact ⟨e.bijective, e.symm.bijective,
    fun _ _ h => InclusionReversal.fixing_subgroup_inclusion_reversal K L _ _ h,
    fun _ _ h => InclusionReversal.fixed_field_inclusion_reversal K L _ _ h⟩

theorem fundamental_correspondence : OrderCorrespondence.{u, v} := by
  intro K L _ _ _ _ _
  let e : IntermediateField K L ≃o (Subgroup (L ≃ₐ[K] L))ᵒᵈ :=
    { toFun := fun E => OrderDual.toDual (FixedField.fixingSubgroup K L E)
      invFun := fun H => FixedField.fixedField K L (OrderDual.ofDual H)
      left_inv := fixed_field_fixing_subgroup K L
      right_inv := fixing_subgroup_fixed_field K L
      map_rel_iff' := by
        intro E₁ E₂
        change FixedField.fixingSubgroup K L E₂ ≤
          FixedField.fixingSubgroup K L E₁ ↔ E₁ ≤ E₂
        constructor
        · intro h
          have h' := InclusionReversal.fixed_field_inclusion_reversal K L _ _ h
          calc
            E₁ = FixedField.fixedField K L (FixedField.fixingSubgroup K L E₁) :=
              (fixed_field_fixing_subgroup K L E₁).symm
            _ ≤ FixedField.fixedField K L (FixedField.fixingSubgroup K L E₂) := h'
            _ = E₂ := fixed_field_fixing_subgroup K L E₂
        · exact InclusionReversal.fixing_subgroup_inclusion_reversal K L E₁ E₂ }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

end D07.Ch14.FundamentalCorrespondence
