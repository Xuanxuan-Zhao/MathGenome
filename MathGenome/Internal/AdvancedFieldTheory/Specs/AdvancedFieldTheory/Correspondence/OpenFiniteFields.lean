import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations
import Mathlib.FieldTheory.KrullTopology

/-!
Independent specification of FT-C06A, the field finiteness criterion in
`notes/003/advanced-field-theory.tex:780–797`.
Finiteness means finite dimension over the base field. The intermediate
field need not be normal, and trivial extensions are included.
-/

universe u v

namespace Specs.AdvancedFieldTheory

/-- A pointwise fixing subgroup is Krull open exactly for finite extensions. -/
def fixingSubgroup_isOpen_iff_finiteDimensional_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L),
    IsOpen (M.fixingSubgroup : Set (L ≃ₐ[K] L)) ↔ FiniteDimensional K M

end Specs.AdvancedFieldTheory
