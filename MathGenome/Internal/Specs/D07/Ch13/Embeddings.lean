import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent specification for K07.13.embeddings (paper.tex:3958–3965).

The finite base K and the two Algebra structures retain the specified base
embeddings. A K-embedding is an algebra homomorphism between fields, whose
underlying field map is automatically injective. FiniteDimensional expresses
finite extension degree; it does not replace the finite-base hypothesis.
The fields may lie in different universes and need not already be subfields
of a common closure. The natural-number count is accompanied by finiteness.
No normality, separability, inclusion or preexisting embedding is assumed
in the existence criterion. Degrees one and equal degrees are included.
-/

universe u v w

namespace Specs.D07.Ch13.Embeddings

/-- The type of base-preserving embeddings has an actual finite cardinality. -/
def FiniteEmbeddings : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    [Finite K] [FiniteDimensional K E] [FiniteDimensional K L],
    Finite (E →ₐ[K] L)

/-- For the specified degrees a and b, existence is equivalent to divisibility. -/
def EmbeddingExistsIff : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    [Finite K] [FiniteDimensional K E] [FiniteDimensional K L]
    (a b : ℕ), Module.finrank K E = a → Module.finrank K L = b →
    (Nonempty (E →ₐ[K] L) ↔ a ∣ b)

/-- Whenever an embedding exists, there are exactly a such embeddings. -/
def EmbeddingCount : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    [Finite K] [FiniteDimensional K E] [FiniteDimensional K L]
    (a b : ℕ), Module.finrank K E = a → Module.finrank K L = b →
    Nonempty (E →ₐ[K] L) → Nat.card (E →ₐ[K] L) = a

end Specs.D07.Ch13.Embeddings
