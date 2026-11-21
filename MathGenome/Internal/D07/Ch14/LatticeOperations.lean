import MathGenome.Internal.D07.Ch14.FundamentalCorrespondence
import MathGenome.Internal.D07.Ch12.AdjoinDefinition
import MathGenome.Internal.Specs.D07.Ch14.LatticeOperations

/-!
Intersections and composita in a finite Galois extension.

The upstream order isomorphism has the canonical pointwise fixing maps
in both directions. An order isomorphism preserves suprema and infima;
the order dual exchanges these operations on the subgroup side. The
upstream compositum theorem and the subgroup closure theorem then identify
the suprema with the generated objects in the source.
-/

universe u v

namespace D07.Ch14.LatticeOperations

open Specs.D07.Ch14.LatticeOperations
open D07.Ch12

theorem fixing_subgroup_compositum : FixingSubgroupCompositum.{u, v} := by
  intro K L _ _ _ _ _ E₁ E₂
  obtain ⟨e, he, _⟩ := FundamentalCorrespondence.fundamental_correspondence K L
  change (AdjoinDefinition.compositum K L E₁ E₂).fixingSubgroup =
    E₁.fixingSubgroup ⊓ E₂.fixingSubgroup
  dsimp only [AdjoinDefinition.compositum, AdjoinDefinition.generatedField]
  rw [AdjoinDefinition.compositum_sup K L E₁ E₂]
  have h := congrArg OrderDual.ofDual (e.map_sup E₁ E₂)
  change OrderDual.ofDual (e (E₁ ⊔ E₂)) =
    OrderDual.ofDual (e E₁) ⊓ OrderDual.ofDual (e E₂) at h
  simpa only [he, Specs.D07.Ch14.FixedField.fixingSubgroupValue] using h

theorem fixing_subgroup_intersection : FixingSubgroupIntersection.{u, v} := by
  intro K L _ _ _ _ _ E₁ E₂
  rw [← Subgroup.sup_eq_closure]
  obtain ⟨e, he, _⟩ := FundamentalCorrespondence.fundamental_correspondence K L
  have h := congrArg OrderDual.ofDual (e.map_inf E₁ E₂)
  change OrderDual.ofDual (e (E₁ ⊓ E₂)) =
    OrderDual.ofDual (e E₁) ⊔ OrderDual.ofDual (e E₂) at h
  simpa only [he] using h

theorem fixed_field_generated : FixedFieldGenerated.{u, v} := by
  intro K L _ _ _ _ _ H₁ H₂
  rw [← Subgroup.sup_eq_closure]
  obtain ⟨e, _, hE⟩ := FundamentalCorrespondence.fundamental_correspondence K L
  have h := e.symm.map_inf (OrderDual.toDual H₁) (OrderDual.toDual H₂)
  change e.symm (OrderDual.toDual (H₁ ⊔ H₂)) =
    e.symm (OrderDual.toDual H₁) ⊓ e.symm (OrderDual.toDual H₂) at h
  simpa only [hE] using h

theorem fixed_field_intersection : FixedFieldIntersection.{u, v} := by
  intro K L _ _ _ _ _ H₁ H₂
  change IntermediateField.fixedField (H₁ ⊓ H₂) =
    AdjoinDefinition.compositum K L
      (IntermediateField.fixedField H₁) (IntermediateField.fixedField H₂)
  dsimp only [AdjoinDefinition.compositum, AdjoinDefinition.generatedField]
  rw [AdjoinDefinition.compositum_sup K L]
  obtain ⟨e, _, hE⟩ := FundamentalCorrespondence.fundamental_correspondence K L
  have h := e.symm.map_sup (OrderDual.toDual H₁) (OrderDual.toDual H₂)
  change e.symm (OrderDual.toDual (H₁ ⊓ H₂)) =
    e.symm (OrderDual.toDual H₁) ⊔ e.symm (OrderDual.toDual H₂) at h
  simpa only [hE, Specs.D07.Ch14.FixedField.fixedFieldValue] using h

end D07.Ch14.LatticeOperations
