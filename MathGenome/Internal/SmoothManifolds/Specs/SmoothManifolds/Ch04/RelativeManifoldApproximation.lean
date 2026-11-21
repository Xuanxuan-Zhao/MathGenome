import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.SmoothMaps

/-! The boundaryless-target clause of relative Whitney approximation,
paper.tex, M04.05 (including its last proof sentence).

The source may have ordinary boundary. The cylinder need not be an ordinary
manifold: at a source boundary point and a time endpoint it has a corner.
Its smoothness is therefore tested by ambient extensions in the time variable
and the original source charts. Both endpoints belong to the cylinder.
-/
namespace SmoothManifolds.RelativeManifoldApproximationData
open ModelData AtlasData MapData Set
universe u v

abbrev Time := Icc (0 : ℝ) 1

/-- Ambient local extension in time and source coordinates, in every pair of
source and target charts. This includes the corner points of the cylinder. -/
def CylinderSmoothAt {n m : ℕ} {a : ModelKind} {N : Type u} {M : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m .euclidean N)
    (H : Time × M → N) (z : Time × M) : Prop :=
  ContinuousAt H z ∧
    ∀ e ∈ S.smoothStructure.val, ∀ d ∈ T.smoothStructure.val,
      z.2 ∈ e.source → H z ∈ d.source →
      LocalCoordinateExtension (⊤ : ℕ∞)
        (fun w : Time × M => Fin.cons w.1.val (e w.2).val)
        (fun w => (d (H w)).val) z

/-- A neighborhood of the entire closed time interval times the given set.
Smoothness is the ambient local-extension convention, not a derivative within
the closed cylinder. -/
def HomotopySmoothNear {n m : ℕ} {a : ModelKind} {N : Type u} {M : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m .euclidean N)
    (A : Set M) (H : Time × M → N) : Prop :=
  ∃ U : Set M, IsOpen U ∧ A ⊆ U ∧
    ∀ z : Time × M, z.2 ∈ U → CylinderSmoothAt S T H z

end SmoothManifolds.RelativeManifoldApproximationData

namespace Specs.SmoothManifolds.Ch04.RelativeManifoldApproximation
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.RelativeManifoldApproximationData Set
universe u v

def relative_manifold_approximationType : Prop :=
  ∀ {n m : ℕ} {a : ModelKind} {N : Type u} {M : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m .euclidean N)
    (A : Set M) (F : M → N) (O : Set (M × N)),
    IsClosed A → Continuous F →
    LocallySmoothOnSubsetToManifold S.smoothStructure.val T.smoothStructure.val
      A (fun x => F x.val) →
    IsOpen O → (∀ x, (x, F x) ∈ O) →
    ∃ G : M → N, IsSmoothMap S T G ∧ EqOn G F A ∧
      ∃ H : Time × M → N, Continuous H ∧
        (∀ x, H (⟨0, by simp⟩, x) = F x) ∧
        (∀ x, H (⟨1, by simp⟩, x) = G x) ∧
        (∀ (t : Time) (x : M), x ∈ A → H (t, x) = F x) ∧
        (∀ (t : Time) (x : M), (x, H (t, x)) ∈ O) ∧
        ((∃ U : Set M, IsOpen U ∧ A ⊆ U ∧
          ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val F U) →
          HomotopySmoothNear S T A H)

end Specs.SmoothManifolds.Ch04.RelativeManifoldApproximation
