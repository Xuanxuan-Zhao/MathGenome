import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Partitions

/-! Independent full statement of M01.07(b). Both models, every natural
 dimension, and arbitrary (including empty) manifold types are quantified. -/
namespace Specs.SmoothManifolds.Localization.SmoothExhaustion
open _root_.SmoothManifolds _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.PartitionData
universe u

def exists_smooth_exhaustionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M),
    ∃ ρ : M → ℝ, ScalarSmooth S.smoothStructure.val ρ ∧
      (∀ x, 0 ≤ ρ x) ∧ ∀ c : ℝ, IsCompact {x | ρ x ≤ c}

end Specs.SmoothManifolds.Localization.SmoothExhaustion
