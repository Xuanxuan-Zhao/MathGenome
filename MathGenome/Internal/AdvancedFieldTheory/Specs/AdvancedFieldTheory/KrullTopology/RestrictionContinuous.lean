import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.InitialDescriptions

/-! Independent specification for the general restriction assertion of FT-T03,
notes/003/advanced-field-theory.tex:433–441, 460–471.
Both automorphism groups carry their intrinsic Krull topology. In particular,
the intermediate extension need not be finite. -/

universe u v

namespace Specs.AdvancedFieldTheory.KrullTopology

def restriction_continuous_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) [IsGalois K M],
    @Continuous (L ≃ₐ[K] L) (M ≃ₐ[K] M) (krullTopology K L) (krullTopology K M)
      (Specs.AdvancedFieldTheory.restriction_value M)

end Specs.AdvancedFieldTheory.KrullTopology
