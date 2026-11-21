import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Partitions

/-! M01.07(a): extension from an arbitrary closed subset, using the shared
local-extension convention and support closed in the manifold. -/
namespace Specs.SmoothManifolds.Localization.Extension
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData
open Set
universe u

def exists_supported_smooth_extensionType : Prop :=
  ∀ {n k : ℕ} {a : _root_.SmoothManifolds.ModelKind}
    {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (A U : Set M),
    IsClosed A → IsOpen U → A ⊆ U →
    ∀ f : A → Euclidean k,
      LocallySmoothOnSubset S.smoothStructure.val A f →
      ∃ F : M → Euclidean k,
        (∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val F x) ∧
        (∀ x : A, F x.val = f x) ∧ sectionSupport F ⊆ U

end Specs.SmoothManifolds.Localization.Extension
