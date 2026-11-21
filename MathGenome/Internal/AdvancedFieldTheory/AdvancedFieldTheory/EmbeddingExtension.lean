import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.EmbeddingExtension

/-!
# Extension of an intermediate-field embedding

Theorem 1.5 (`res:F05`) of `notes/003/advanced-field-theory.tex`.
-/

universe u v

namespace AdvancedFieldTheory

/-- An embedding of any intermediate field into a Galois extension extends to
an automorphism of the ambient extension, even when its image leaves the
intermediate field. -/
theorem exists_automorphism_extending_embedding
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) (ι : M →ₐ[K] L) :
    ∃ σ : GaloisGroup K L, ∀ m : M, σ (m : L) = ι m := by
  -- The towers K ⊆ M ⊆ L and K ⊆ L ⊆ L use the canonical inclusion maps.
  -- Normality extends the homomorphism; algebraicity makes the extension bijective.
  let f : L →ₐ[K] L := ι.liftNormal L
  refine ⟨AlgEquiv.ofBijective f (AlgHom.normal_bijective K L L f), ?_⟩
  intro m
  exact ι.liftNormal_commutes L m

end AdvancedFieldTheory
