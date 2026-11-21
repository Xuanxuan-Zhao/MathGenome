import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteIngredients.GaloisCorrespondence

/-!
# Finite Galois correspondence

Proposition F01 (finite correspondence) in the field-theory source.
The upstream `fixedField` and `fixingSubgroup` are definitionally the
canonical Mathlib constructions used in the independent statements.
No intermediate field is required to be Galois over the base, and no
subgroup is required to be normal or nontrivial.
-/

universe u v

namespace AdvancedFieldTheory.FiniteIngredients

variable {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]

/-- Taking the pointwise stabilizer and then its fixed field recovers M. -/
theorem finite_fixedField_fixingSubgroup [FiniteDimensional K E] [IsGalois K E]
    (M : IntermediateField K E) :
    fixedField (fixingSubgroup M) = M :=
  IsGalois.fixedField_fixingSubgroup M

/-- Taking the fixed field and then its pointwise stabilizer recovers H. -/
theorem finite_fixingSubgroup_fixedField [FiniteDimensional K E] [IsGalois K E]
    (H : Subgroup (GaloisGroup K E)) :
    fixingSubgroup (fixedField H) = H :=
  IntermediateField.fixingSubgroup_fixedField H

/-- The field-to-subgroup map reverses inclusion. -/
theorem fixingSubgroup_antitone :
    Antitone (fixingSubgroup : IntermediateField K E → Subgroup (GaloisGroup K E)) :=
  IntermediateField.fixingSubgroup_antitone

/-- The subgroup-to-field map reverses inclusion. -/
theorem fixedField_antitone :
    Antitone (fixedField : Subgroup (GaloisGroup K E) → IntermediateField K E) :=
  IntermediateField.fixedField_antitone

/-- In particular, the full finite Galois group has fixed field K. -/
theorem finite_fixedField_top [FiniteDimensional K E] [IsGalois K E] :
    fixedField (⊤ : Subgroup (GaloisGroup K E)) = (⊥ : IntermediateField K E) :=
  IsGalois.fixedField_top

/-- The trivial subgroup fixes E. -/
theorem fixedField_bot :
    fixedField (⊥ : Subgroup (GaloisGroup K E)) = (⊤ : IntermediateField K E) :=
  IntermediateField.fixedField_bot

/-- Every K-automorphism fixes the specified image of K. -/
theorem fixingSubgroup_bot :
    fixingSubgroup (⊥ : IntermediateField K E) = (⊤ : Subgroup (GaloisGroup K E)) :=
  IntermediateField.fixingSubgroup_bot

/-- Only the identity automorphism fixes E pointwise. -/
theorem fixingSubgroup_top :
    fixingSubgroup (⊤ : IntermediateField K E) = (⊥ : Subgroup (GaloisGroup K E)) :=
  IntermediateField.fixingSubgroup_top

end AdvancedFieldTheory.FiniteIngredients
