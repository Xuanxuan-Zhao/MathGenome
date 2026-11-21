import MathGenome.Internal.Specs.D07.Ch12.EmbeddingExtension

/-!
Extension of algebraic embeddings (K07.12.embedding_extension).

Give Ω the E-algebra structure induced by the specified σ. Mathlib's
`IntermediateField.nonempty_algHom_of_splits` then applies: every element
of L is integral over the field E, and its minimal polynomial splits after
mapping coefficients by precisely σ. This theorem uses the one-element
extension and Zorn argument in `Mathlib.FieldTheory.Extension`, and places
no finiteness or separability assumption on L/E. An E-algebra homomorphism
is injective between fields, and its scalar compatibility says exactly
that it restricts to σ. Algebraic closedness implies the splitting premise.
-/

universe u v w

namespace D07.Ch12.EmbeddingExtension

open Specs.D07.Ch12.EmbeddingExtension

theorem extensionOfSplitting : ExtensionOfSplitting.{u, v, w} := by
  intro E L Ω _ _ _ _ _ σ hs
  letI : Algebra E Ω := σ.toAlgebra
  obtain ⟨τ⟩ := IntermediateField.nonempty_algHom_of_splits
    (F := E) (E := L) (K := Ω)
    (fun a => ⟨(Algebra.IsAlgebraic.isAlgebraic a).isIntegral, hs a⟩)
  exact ⟨τ.toRingHom, τ.injective, fun x => τ.commutes x⟩

theorem extensionIntoAlgebraicallyClosed :
    ExtensionIntoAlgebraicallyClosed.{u, v, w} := by
  intro E L Ω _ _ _ _ _ _ σ
  exact extensionOfSplitting E L Ω σ (fun a => IsAlgClosed.splits _)

end D07.Ch12.EmbeddingExtension
