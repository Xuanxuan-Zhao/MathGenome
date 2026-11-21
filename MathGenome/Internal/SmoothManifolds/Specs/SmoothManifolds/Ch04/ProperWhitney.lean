import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.FiniteProperEmbedding

/-! Proper weak Whitney embedding, paper.tex, Theorem M04.02.
The derivative is the full derivative of local ambient extensions, including
normal vectors at boundary points. The homeomorphism uses the subspace topology.
There is no nonemptiness, compactness, connectedness or positive-dimension
hypothesis. -/
namespace Specs.SmoothManifolds.Ch04.ProperWhitney
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.GoodProjectionData
  _root_.SmoothManifolds.MapClassData
universe u

def exists_proper_embeddingType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M),
    ∃ e : M → Euclidean (2 * n + 1),
      IsEuclideanImmersion S e ∧ Function.Injective e ∧ IsProper e ∧
        ∃ h : M ≃ₜ Set.range e, ∀ p, (h p).val = e p

end Specs.SmoothManifolds.Ch04.ProperWhitney
