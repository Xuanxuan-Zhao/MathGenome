import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.RestrictionSystem

/-!
Independent statements for C03, notes/003/advanced-field-theory.tex:686–707.
The inverse image under E.val represents the intersection as a field inside E;
its image under E.val is the literal intersection inside L. No topology or
closedness condition on the subgroup is imposed.
-/

universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory

/-- Fixed elements agree before and after restricting the group to E. -/
def fixedField_comap_restriction_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)) (E : IntermediateField K L) [IsGalois K E],
    (IntermediateField.fixedField H).comap E.val =
      IntermediateField.fixedField (H.map (restriction_value E))

/-- The first equality of C03, with both fields embedded in the specified L. -/
def fixedField_inf_finiteLayer_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)) (E : IntermediateField K L) [IsGalois K E],
    IntermediateField.fixedField H ⊓ E =
      (IntermediateField.fixedField (H.map (restriction_value E))).map E.val

/-- The second equality of C03: the image is the full pointwise stabilizer
of the intersection, regarded as an intermediate field of E/K. -/
def restriction_image_eq_fixingSubgroup_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) (E : IntermediateField K L)
    [FiniteDimensional K E] [IsGalois K E],
    H.map (restriction_value E) =
      ((IntermediateField.fixedField H).comap E.val).fixingSubgroup

end Specs.AdvancedFieldTheory
