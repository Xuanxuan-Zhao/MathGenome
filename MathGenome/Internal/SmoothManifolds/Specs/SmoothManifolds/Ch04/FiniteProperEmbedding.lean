import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.GoodProjections
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.ProperEmbedding
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.SmoothExhaustion

/-! The independent finite-dimensional existence stage of M04.02.
No target dimension is imposed. Smoothness and derivative injectivity use the
shared ambient-extension convention, in every chart, including full normal
vectors at boundary points. The range carries its actual subspace topology. -/
namespace Specs.SmoothManifolds.Ch04.FiniteProperEmbedding
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.GoodProjectionData
  _root_.SmoothManifolds.MapClassData
universe u

/-- Empty, disconnected, noncompact, boundary and zero-dimensional manifolds
are all included, with no extra hypotheses. -/
def exists_finite_proper_embeddingType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M),
    ∃ (q : ℕ) (e : M → Euclidean q),
      IsEuclideanImmersion S e ∧ Function.Injective e ∧ IsProper e ∧
        ∃ h : M ≃ₜ Set.range e, ∀ p, (h p).val = e p

end Specs.SmoothManifolds.Ch04.FiniteProperEmbedding
