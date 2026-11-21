import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Extension
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.SmoothExhaustion

/-! Independent statements of M01.07(c) and the complete M01.07 theorem.
All smoothness uses local ambient extensions, including at boundary points. -/
namespace Specs.SmoothManifolds.Localization.ClosedZeroSets
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.PartitionData
open Set
universe u

def exists_smooth_nonnegative_zero_setType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (A : Set M), IsClosed A →
    ∃ g : M → ℝ, ScalarSmooth S.smoothStructure.val g ∧
      (∀ x, 0 ≤ g x) ∧ g ⁻¹' {0} = A

/-- The three conclusions hold together for every locally smooth vector-valued
map on the closed set, with extension supported in the prescribed open set. -/
def extension_exhaustion_zero_setsType : Prop :=
  ∀ {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (A U : Set M),
    IsClosed A → IsOpen U → A ⊆ U →
    ∀ f : A → Euclidean k,
      LocallySmoothOnSubset S.smoothStructure.val A f →
      ∃ (F : M → Euclidean k) (ρ g : M → ℝ),
        ((∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val F x) ∧
          (∀ x : A, F x.val = f x) ∧ sectionSupport F ⊆ U) ∧
        (ScalarSmooth S.smoothStructure.val ρ ∧ (∀ x, 0 ≤ ρ x) ∧
          ∀ c : ℝ, IsCompact {x | ρ x ≤ c}) ∧
        (ScalarSmooth S.smoothStructure.val g ∧ (∀ x, 0 ≤ g x) ∧ g ⁻¹' {0} = A)

end Specs.SmoothManifolds.Localization.ClosedZeroSets
