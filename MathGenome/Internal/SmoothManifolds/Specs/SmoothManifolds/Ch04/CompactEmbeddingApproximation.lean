import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.GoodProjections

/-! Uniform approximation in the fixed target of M04.03 (paper.tex:1199–1204).
A Euclidean smooth embedding is expressed by smoothness, injectivity of every
full coordinate derivative, and a homeomorphism onto the subspace image. -/
namespace Specs.SmoothManifolds.Ch04.CompactEmbeddingApproximation
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.GoodProjectionData
universe u

def compact_embedding_approximationType : Prop :=
  ∀ {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold n a M), 2 * n + 1 ≤ q →
    ∀ f : M → Euclidean q, IsSmoothEuclidean S f →
    ∀ ε : ℝ, 0 < ε → ∃ g : M → Euclidean q,
      IsEuclideanImmersion S g ∧ Function.Injective g ∧
      (∃ h : M ≃ₜ Set.range g, ∀ p, (h p).val = g p) ∧
      ∀ p, ‖g p - f p‖ < ε

end Specs.SmoothManifolds.Ch04.CompactEmbeddingApproximation
