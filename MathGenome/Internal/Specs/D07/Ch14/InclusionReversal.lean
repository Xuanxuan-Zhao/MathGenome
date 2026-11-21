import MathGenome.Internal.Specs.D07.Ch14.FixedField

/-!
Independent specification for K07.14.inclusion_reversal,
paper.tex:4108–4114 (chapters/M07.14.tex:26–32).

The chosen Algebra K L records the base embedding. The fields and subgroups
are the canonical objects from the upstream fixed-field specification.
No finiteness, algebraicity, normality, or separability assumption is imposed.
The order relations below are inclusion of their carriers.
-/

universe u v

namespace Specs.D07.Ch14.InclusionReversal

/-- Enlarging an intermediate field shrinks its pointwise fixing subgroup. -/
def FixingSubgroupInclusionReversal : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E₁ E₂ : IntermediateField K L),
    E₁ ≤ E₂ →
      FixedField.fixingSubgroupValue K L E₂ ≤ FixedField.fixingSubgroupValue K L E₁

/-- Enlarging a subgroup shrinks its fixed field. -/
def FixedFieldInclusionReversal : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (H₁ H₂ : Subgroup (L ≃ₐ[K] L)),
    H₁ ≤ H₂ →
      FixedField.fixedFieldValue K L H₂ ≤ FixedField.fixedFieldValue K L H₁

/-- Both sides say that every member of H fixes every element of E. -/
def LeFixedFieldIffLeFixingSubgroup : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (H : Subgroup (L ≃ₐ[K] L)),
    E ≤ FixedField.fixedFieldValue K L H ↔ H ≤ FixedField.fixingSubgroupValue K L E

end Specs.D07.Ch14.InclusionReversal
