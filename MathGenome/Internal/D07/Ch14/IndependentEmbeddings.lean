import MathGenome.Internal.Specs.D07.Ch14.IndependentEmbeddings
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! Dedekind independence for the field embeddings in
`lem:independent-embeddings` of the source manuscript. -/

universe u v w

namespace D07.Ch14.IndependentEmbeddings

open Specs.D07.Ch14.IndependentEmbeddings

/-- Distinct field embeddings are linearly independent over their target field
as functions, without any assumption on extension degrees or separability. -/
theorem embeddings_linearIndependent : EmbeddingsLinearIndependent.{u, v, w} := by
  intro A B _ _ ι σ hσ
  exact (linearIndependent_monoidHom A B).comp
    (fun i => (σ i).toMonoidHom)
    (fun i j h => hσ (RingHom.ext fun x => DFunLike.congr_fun h x))

/-- The source's finite relation formulation, with coefficients in B and the
relation required to vanish at every element of A. -/
theorem finite_relation_trivial : FiniteRelationTrivial.{u, v} := by
  intro A B _ _ s σ hσ c hc
  have hlin := embeddings_linearIndependent A B (Fin s) σ hσ
  apply (Fintype.linearIndependent_iff.mp hlin) c
  ext x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hc x

end D07.Ch14.IndependentEmbeddings
