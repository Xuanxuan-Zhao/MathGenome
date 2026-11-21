import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
Independent specification for `fa2:p2:prehilbert-completion`, paper.tex 7682–7688.
The original inner product and scalar action on E are fixed. `RCLike` covers
both real and complex fields, with the inner product conjugate linear in its
first argument. No completeness, dimension, or nonzero assumption is made on E.

A unitary between Hilbert spaces is represented by a scalar-linear isometric
equivalence, with preservation of the actual scalar-valued inner product also
stated explicitly. Uniqueness is relative to the given dense embeddings.
-/

universe u v w z

namespace ExpandedFA.Hilbert.PreHilbertCompletion.Spec

/-- The canonical completion has its extended inner product and is complete;
the same canonical linear embedding preserves the inner product and is dense
and injective. -/
def CanonicalCompletionProperties : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E],
    let i : E →ₗᵢ[𝕜] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
    CompleteSpace (UniformSpace.Completion E) ∧
      (∀ x y, inner 𝕜 (i x) (i y) = inner 𝕜 x y) ∧
      Function.Injective i ∧ DenseRange i

/-- Existence of a Hilbert completion of the given inner-product space.
The embedding is linear over the original field and preserves the full inner
product, rather than only its real part or the induced norm. -/
def CompletionExists : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E],
    ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace 𝕜 H)
      (_ : CompleteSpace H) (i : E →ₗ[𝕜] H),
      (∀ x y, inner 𝕜 (i x) (i y) = inner 𝕜 x y) ∧
      Function.Injective i ∧ DenseRange i

/-- Any two Hilbert completions admit exactly one intertwining unitary.
The input embeddings are merely linear maps preserving inner products with
dense range; no independent isometry assumption is imposed on them.
The unitary is surjective by its bundled equivalence type. -/
def CompletionUniqueness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (H : Type w) (G : Type z)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (i : E →ₗ[𝕜] H) (j : E →ₗ[𝕜] G),
    (∀ x y, inner 𝕜 (i x) (i y) = inner 𝕜 x y) → DenseRange i →
    (∀ x y, inner 𝕜 (j x) (j y) = inner 𝕜 x y) → DenseRange j →
    ∃! U : H ≃ₗᵢ[𝕜] G,
      (∀ x y, inner 𝕜 (U x) (U y) = inner 𝕜 x y) ∧
      ∀ x, U (i x) = j x

end ExpandedFA.Hilbert.PreHilbertCompletion.Spec
