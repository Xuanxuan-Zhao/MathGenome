import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
Independent specification for `lem:independent-embeddings`, paper.tex:4116–4123.
The embeddings are arbitrary unital field homomorphisms. In particular no
finite-degree, normality, separability, or common base-field assumption is
imposed. The vector space is the space of all B-valued functions on A, with
pointwise B-scalars. The family formulation includes the empty family; the
finite-sum formulation states explicitly that every relation is trivial.
-/

universe u v w

namespace Specs.D07.Ch14.IndependentEmbeddings

def EmbeddingsLinearIndependent : Prop :=
  ∀ (A : Type u) (B : Type v) [Field A] [Field B]
    (ι : Type w) (σ : ι → A →+* B),
    Function.Injective σ → LinearIndependent B (fun i => (σ i : A → B))

def FiniteRelationTrivial : Prop :=
  ∀ (A : Type u) (B : Type v) [Field A] [Field B]
    (s : ℕ) (σ : Fin s → A →+* B),
    Function.Injective σ → ∀ (c : Fin s → B),
      (∀ x : A, ∑ i : Fin s, c i * σ i x = 0) → ∀ i, c i = 0

end Specs.D07.Ch14.IndependentEmbeddings
