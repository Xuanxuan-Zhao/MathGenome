import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteIngredients.SimpleEmbeddings
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations

/-!
# Simple extensions and embeddings

FT-F01: evaluation at `a` identifies embeddings of `K(a)` with roots of its
minimal polynomial in an arbitrary extension. For finite separable domains,
splitting in the target gives exactly the degree many embeddings.
-/

universe u v w

noncomputable section

open IntermediateField Polynomial

namespace AdvancedFieldTheory

/-- Evaluation at the generator gives the root parametrization of embeddings. -/
def simpleEmbeddingsEquiv (K : Type u) (L : Type v) (T : Type w)
    [Field K] [Field L] [Field T] [Algebra K L] [Algebra K T]
    (a : L) (ha : IsAlgebraic K a) :
    (K⟮a⟯ →ₐ[K] T) ≃ {b : T // aeval b (minpoly K a) = 0} :=
  (adjoin.powerBasis ha.isIntegral).liftEquiv.trans
    ((Equiv.refl T).subtypeEquiv fun b => by
      simp only [Equiv.refl_apply, adjoin.powerBasis_gen, minpoly_gen])

@[simp]
theorem simpleEmbeddingsEquiv_apply (K : Type u) (L : Type v) (T : Type w)
    [Field K] [Field L] [Field T] [Algebra K L] [Algebra K T]
    (a : L) (ha : IsAlgebraic K a) (f : K⟮a⟯ →ₐ[K] T) :
    (simpleEmbeddingsEquiv K L T a ha f).val = f (AdjoinSimple.gen K a) := rfl

@[simp]
theorem simpleEmbeddingsEquiv_symm_apply_gen (K : Type u) (L : Type v) (T : Type w)
    [Field K] [Field L] [Field T] [Algebra K L] [Algebra K T]
    (a : L) (ha : IsAlgebraic K a)
    (b : {b : T // aeval b (minpoly K a) = 0}) :
    (simpleEmbeddingsEquiv K L T a ha).symm b (AdjoinSimple.gen K a) = b.val := by
  have h := congrArg Subtype.val ((simpleEmbeddingsEquiv K L T a ha).apply_symm_apply b)
  exact h

/-- Each root determines exactly one embedding, even in the inseparable case. -/
theorem existsUnique_embedding_of_root (K : Type u) (L : Type v) (T : Type w)
    [Field K] [Field L] [Field T] [Algebra K L] [Algebra K T]
    (a : L) (ha : IsAlgebraic K a) (b : T) (hb : aeval b (minpoly K a) = 0) :
    ∃! f : K⟮a⟯ →ₐ[K] T, f (AdjoinSimple.gen K a) = b := by
  let e := simpleEmbeddingsEquiv K L T a ha
  refine ⟨e.symm ⟨b, hb⟩, simpleEmbeddingsEquiv_symm_apply_gen K L T a ha _, ?_⟩
  intro f hf
  apply e.injective
  apply Subtype.ext
  simpa only [e, simpleEmbeddingsEquiv_apply,
    simpleEmbeddingsEquiv_symm_apply_gen] using hf

/-- The primitive-element counting formula, with no normality assumption. -/
theorem card_embeddings_of_splits (K : Type u) (M : Type v) (T : Type w)
    [Field K] [Field M] [Field T] [Algebra K M] [Algebra K T]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (hT : ∀ x : M, ((minpoly K x).map (algebraMap K T)).Splits) :
    Nat.card (M →ₐ[K] T) = Module.finrank K M :=
  AlgHom.natCard_of_splits K M T hT

end AdvancedFieldTheory
