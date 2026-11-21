import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.SmoothMaps
import Mathlib.Analysis.Normed.Lp.PiLp

/-! Independent statement of the Euclidean-target clause of M04.05.
The coordinate space is the shared `ModelData.Euclidean q`; `WithLp.toLp 2`
expresses the standard Euclidean norm, rather than the Pi type's maximum norm.
Smoothness and the hypothesis on the closed subset use the shared ambient
extension convention, including at ordinary boundary points.
-/
namespace Specs.SmoothManifolds.Ch04.RelativeEuclideanApproximation
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
open Set
universe u

def relative_euclidean_approximationType : Prop :=
  ∀ {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (A : Set M) (F : M → Euclidean q)
    (ε : M → ℝ),
    IsClosed A → Continuous F → Continuous ε → (∀ x, 0 < ε x) →
    LocallySmoothOnSubset S.smoothStructure.val A (fun x => F x.val) →
    ∃ G : M → Euclidean q,
      (∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val G x) ∧
      EqOn G F A ∧
      (∀ x, ‖WithLp.toLp 2 (G x - F x)‖ < ε x) ∧
      ∃ H : Icc (0 : ℝ) 1 × M → Euclidean q,
        Continuous H ∧
        (∀ x, H (⟨0, by simp⟩, x) = F x) ∧
        (∀ x, H (⟨1, by simp⟩, x) = G x) ∧
        ∀ (t : Icc (0 : ℝ) 1) (x : M), x ∈ A → H (t, x) = F x

end Specs.SmoothManifolds.Ch04.RelativeEuclideanApproximation
