import MathGenome.Internal.Specs.D07.Ch12.ExtensionDefinition
import MathGenome.Internal.D07.Ch08.FieldEmbedding

/-! Field extensions with a chosen structure map, their induced vector spaces,
and embeddings preserving the chosen base. -/

universe u v w

namespace D07.Ch12.ExtensionDefinition

open Specs.D07.Ch12.ExtensionDefinition

abbrev FieldExtension (K : Type u) (L : Type v) [Field K] [Field L] :=
  K →+* L

abbrev extensionAlgebra (K : Type u) (L : Type v) [Field K] [Field L]
    (ι : K →+* L) : Algebra K L :=
  ι.toAlgebra

abbrev extensionModule (K : Type u) (L : Type v) [Field K] [Field L]
    (ι : K →+* L) : Module K L :=
  letI := ι.toAlgebra
  Algebra.toModule

abbrev FieldEmbedding (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] :=
  E →ₐ[K] L

theorem structure_map_injective : StructureMapInjective.{u, v} := by
  intro K L _ _ ι
  exact D07.Ch08.FieldEmbedding.unital_injective K L ι

theorem induced_scalars : InducedScalars.{u, v} := by
  intro K L _ _ ι
  exact ⟨rfl, fun _ _ => rfl⟩

theorem recover_algebra : RecoverAlgebra.{u, v} := by
  intro K L _ _ A
  let := A
  exact toAlgebra_algebraMap

theorem identify_with_image : IdentifyWithImage.{u, v} := by
  intro K L _ _ ι
  exact ⟨ι.rangeRestrictFieldEquiv, fun a => rfl⟩

theorem embedding_iff : EmbeddingIff.{u, v, w} := by
  intro K E L _ _ _ _ _ f
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨structure_map_injective E L σ.toRingHom, σ.commutes⟩
  · rintro ⟨_, h⟩
    exact ⟨{ f with commutes' := h }, rfl⟩

theorem embedding_laws : EmbeddingLaws.{u, v, w} := by
  intro K E L _ _ _ _ _ σ
  refine ⟨structure_map_injective E L σ.toRingHom, σ.commutes, ?_⟩
  intro a x
  simp only [Algebra.smul_def, map_mul, σ.commutes]

theorem embeddings_determine_scalars : EmbeddingsDetermineScalars.{u, v} := by
  intro K L _ _ ι κ
  constructor
  · constructor
    · rintro rfl
      rfl
    · intro h
      exact congrArg (fun A : Algebra K L => A.algebraMap) h
  · constructor
    · rintro rfl
      exact fun _ _ => rfl
    · intro h
      apply RingHom.ext
      intro a
      simpa only [mul_one] using h a 1

theorem different_extensions : DifferentExtensions := by
  let ι : ℂ →+* ℂ := RingHom.id ℂ
  let κ : ℂ →+* ℂ := starRingEnd ℂ
  have hne : ι ≠ κ := by
    intro h
    have hI := congrArg (fun f : ℂ →+* ℂ => (f Complex.I).im) h
    norm_num [ι, κ] at hI
  refine ⟨ι, κ, hne, ?_⟩
  intro h
  exact hne ((embeddings_determine_scalars ℂ ℂ ι κ).1.mpr h)

end D07.Ch12.ExtensionDefinition
