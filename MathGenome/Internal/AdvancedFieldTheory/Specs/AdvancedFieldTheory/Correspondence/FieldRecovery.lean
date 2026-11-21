import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations
import Mathlib.FieldTheory.KrullTopology

/-!
Independent statements for FT-C02, Proposition C02 in
`notes/003/advanced-field-theory.tex:670–685`.
The ambient extension is Galois, and its automorphism group carries the
Krull topology. The intermediate field is arbitrary: it need not be finite
or normal over the base field.
-/

universe u v

namespace Specs.AdvancedFieldTheory

/-- The pointwise fixing subgroup of any intermediate field is closed. -/
def fixingSubgroup_isClosed_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L),
    IsClosed (M.fixingSubgroup : Set (L ≃ₐ[K] L))

/-- Taking the fixed field of that subgroup recovers the original field. -/
def fixedField_fixingSubgroup_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L),
    IntermediateField.fixedField M.fixingSubgroup = M

end Specs.AdvancedFieldTheory
