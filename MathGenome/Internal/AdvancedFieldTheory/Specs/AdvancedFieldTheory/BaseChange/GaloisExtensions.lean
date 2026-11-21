import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
The Galoisness assertions of C10, notes/003/advanced-field-theory.tex:903–933.
The common overfield is unrestricted. The scalar maps between the literal
supremum/infimum fields are inclusions; M/K need not be algebraic.
-/

universe u v

namespace Specs.AdvancedFieldTheory

def galois_compositum_over_right_type : Prop :=
  ∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (E M : IntermediateField K Ω) [IsGalois K E],
    letI : Algebra M (E ⊔ M : IntermediateField K Ω) :=
      (IntermediateField.inclusion le_sup_right).toAlgebra
    IsGalois M (E ⊔ M : IntermediateField K Ω)

def galois_over_intersection_type : Prop :=
  ∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (E M : IntermediateField K Ω) [IsGalois K E],
    letI : Algebra (E ⊓ M : IntermediateField K Ω) E :=
      (IntermediateField.inclusion inf_le_left).toAlgebra
    IsGalois (E ⊓ M : IntermediateField K Ω) E

end Specs.AdvancedFieldTheory
