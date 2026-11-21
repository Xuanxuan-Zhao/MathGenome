import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
# Specification for extension of an intermediate-field embedding

Source: `notes/003/advanced-field-theory.tex`, Theorem 1.5 (`res:F05`).
The intermediate field is unrestricted, and the embedding need not map it into itself.
An algebra equivalence of the whole ambient field expresses the required bijective
K-automorphism. No finite-dimensional hypothesis is imposed.
-/

universe u v

namespace Specs.AdvancedFieldTheory

/-- Every K-embedding of an intermediate field into a Galois extension extends
    to a K-automorphism of that extension. -/
def exists_automorphism_extending_embedding_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) (ι : M →ₐ[K] L),
    ∃ σ : L ≃ₐ[K] L, ∀ m : M, σ (m : L) = ι m

end Specs.AdvancedFieldTheory
