import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
Independent statements for the finite Galois correspondence in
notes/003/advanced-field-theory.tex, Proposition F01, lines 141–149.
The bottom intermediate field is the specified image of the base field;
the top intermediate field is the whole extension. All subgroups and all
intermediate fields are allowed, including for a degree-one extension.
-/

universe u v

namespace Specs.AdvancedFieldTheory.FiniteIngredients

/-- Recovery of every intermediate field. -/
def finite_fixedField_fixingSubgroup_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E], ∀ M : IntermediateField K E,
    IntermediateField.fixedField M.fixingSubgroup = M

/-- Recovery of every subgroup, without a normality condition. -/
def finite_fixingSubgroup_fixedField_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E], ∀ H : Subgroup (E ≃ₐ[K] E),
    (IntermediateField.fixedField H).fixingSubgroup = H

/-- Enlarging the field shrinks its pointwise stabilizer. -/
def fixingSubgroup_antitone_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E], 
    Antitone (IntermediateField.fixingSubgroup : IntermediateField K E → Subgroup (E ≃ₐ[K] E))

/-- Enlarging the subgroup shrinks its fixed field. -/
def fixedField_antitone_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E], 
    Antitone (IntermediateField.fixedField : Subgroup (E ≃ₐ[K] E) → IntermediateField K E)

/-- The full Galois group fixes precisely the base field. -/
def finite_fixedField_top_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E], 
    IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[K] E)) =
      (⊥ : IntermediateField K E)

/-- The trivial subgroup fixes the whole extension. -/
def fixedField_bot_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E], 
    IntermediateField.fixedField (⊥ : Subgroup (E ≃ₐ[K] E)) =
      (⊤ : IntermediateField K E)

/-- The base field is fixed by the full automorphism group. -/
def fixingSubgroup_bot_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E], 
    (⊥ : IntermediateField K E).fixingSubgroup = (⊤ : Subgroup (E ≃ₐ[K] E))

/-- Only the identity fixes the whole extension pointwise. -/
def fixingSubgroup_top_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E], 
    (⊤ : IntermediateField K E).fixingSubgroup = (⊥ : Subgroup (E ≃ₐ[K] E))

end Specs.AdvancedFieldTheory.FiniteIngredients
