import MathGenome.Internal.Specs.D07.Ch12.EmbeddingCount
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
Counting embeddings, K07.12.embedding_count (paper.tex:3778–3791).

The finite separable degree counts embeddings into any algebraically closed
K-field, by `Field.finSepDegree_eq_of_isAlgClosed`. The library supplies its
upper bound by the finite vector-space dimension and the full equivalence
between equality and separability. The latter's converse uses an arbitrary
simple intermediate field and the strict loss in its number of distinct
conjugates for an inseparable element, together with both tower formulas.
Thus the converse does not assume separability or a primitive element.

We separately prove finiteness of the embedding type and transfer the result
to cardinal degree, so neither natural cardinality nor finrank is used with
an infinite object. The target need not be algebraic over K or be a chosen
algebraic closure, and all three fields can have different universes.
-/

universe u v w

namespace D07.Ch12.EmbeddingCount

open Specs.D07.Ch12.EmbeddingCount

theorem finite_embeddings : FiniteEmbeddings.{u, v, w} := by
  intro K E Ω _ _ _ _ _ _ _
  infer_instance

theorem embedding_bound : EmbeddingBound.{u, v, w} := by
  intro K E Ω _ _ _ _ _ _ _
  rw [← Field.finSepDegree_eq_of_isAlgClosed K E Ω]
  exact Field.finSepDegree_le_finrank K E

theorem equality_iff_separable : EqualityIffSeparable.{u, v, w} := by
  intro K E Ω _ _ _ _ _ _ _
  rw [← Field.finSepDegree_eq_of_isAlgClosed K E Ω]
  exact Field.finSepDegree_eq_finrank_iff K E

theorem cardinal_embedding_count : CardinalEmbeddingCount.{u, v, w} := by
  intro K E Ω _ _ _ _ _ _ _
  have hfinite := finite_embeddings K E Ω
  rw [Specs.D07.Ch12.DegreeDefinition.degreeValue,
    ← Module.finrank_eq_rank K E,
    ← Nat.cast_card (α := E →ₐ[K] Ω)]
  simpa only [Cardinal.lift_natCast, Nat.cast_le, Nat.cast_inj] using
    And.intro (embedding_bound K E Ω) (equality_iff_separable K E Ω)

end D07.Ch12.EmbeddingCount
