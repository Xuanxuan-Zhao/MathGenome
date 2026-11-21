import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
Independent specification of paper.tex, Lemma `d13:19:hilbert-projection`.
The scalar field is real or complex, represented by `RCLike`. A Hilbert
space is a complete inner product space. No dimension restriction is imposed.
-/

namespace Specs.D13Unified.Ch19.HilbertProjection

universe u v

/-- Every closed linear subspace of a Hilbert space is complementary to its
orthogonal complement, and every vector has a unique ordered pair of components.
The equality in the predicate records the original vector as their sum. -/
def closed_subspace_projection_type : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : Submodule 𝕜 H),
    IsClosed (M : Set H) →
      IsCompl M Mᗮ ∧
      ∀ x : H, ∃! p : H × H, p.1 ∈ M ∧ p.2 ∈ Mᗮ ∧ x = p.1 + p.2

end Specs.D13Unified.Ch19.HilbertProjection
