import MathGenome.Internal.Specs.D07.Ch12.DegreeDefinition
import MathGenome.Internal.Specs.D07.Ch12.SeparableDefinition
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Independent specification of K07.12.embedding_count (paper.tex:3778–3791).
The two algebra structures retain the specified embeddings of K into E and Ω.
As in the upstream extension specification, K-embeddings are algebra
homomorphisms: their underlying field maps are automatically injective.
FiniteDimensional means finite vector-space degree, not a finite field.
The finiteness assertion makes Nat.card an actual finite count. The final
formulation compares cardinalities with the source's cardinal-valued degree;
the natural-number formulations use precisely the finite-degree hypothesis.
No separability hypothesis is imposed on the bound or on the equivalence.
-/

universe u v w

namespace Specs.D07.Ch12.EmbeddingCount

/-- Finiteness is part of interpreting the natural-number count. -/
def FiniteEmbeddings : Prop :=
  ∀ (K : Type u) (E : Type v) (Ω : Type w)
    [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]
    [FiniteDimensional K E] [IsAlgClosed Ω],
    Finite (E →ₐ[K] Ω)

/-- The number of embeddings is at most the finite extension degree. -/
def EmbeddingBound : Prop :=
  ∀ (K : Type u) (E : Type v) (Ω : Type w)
    [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]
    [FiniteDimensional K E] [IsAlgClosed Ω],
    Nat.card (E →ₐ[K] Ω) ≤ Module.finrank K E

/-- Both directions of the equality criterion, for an arbitrary closed target. -/
def EqualityIffSeparable : Prop :=
  ∀ (K : Type u) (E : Type v) (Ω : Type w)
    [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]
    [FiniteDimensional K E] [IsAlgClosed Ω],
    Nat.card (E →ₐ[K] Ω) = Module.finrank K E ↔
      SeparableDefinition.extensionSeparableValue K E

/-- The same theorem in the cardinal-dimension convention of the source.
Lifts compare the possibly different universes of E and Ω. -/
def CardinalEmbeddingCount : Prop :=
  ∀ (K : Type u) (E : Type v) (Ω : Type w)
    [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]
    [FiniteDimensional K E] [IsAlgClosed Ω],
    Cardinal.lift.{v} (Cardinal.mk (E →ₐ[K] Ω)) ≤
        Cardinal.lift.{w} (DegreeDefinition.degreeValue K E) ∧
      (Cardinal.lift.{v} (Cardinal.mk (E →ₐ[K] Ω)) =
        Cardinal.lift.{w} (DegreeDefinition.degreeValue K E) ↔
          SeparableDefinition.extensionSeparableValue K E)

end Specs.D07.Ch12.EmbeddingCount
