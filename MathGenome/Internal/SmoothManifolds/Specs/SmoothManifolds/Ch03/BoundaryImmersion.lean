import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.InteriorInverse

/-! Boundary immersion into the interior of the target. The coordinates on the
source are an original smooth half-space chart. The target coordinates are an
actual open partial homeomorphism, obtained from an original target chart by a
Euclidean C^r change of coordinates with C^r inverse. The product coordinates
have exactly n entries, including when n = m. -/
namespace Specs.SmoothManifolds.Ch03.BoundaryImmersion
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.FiniteRegularityData
open Set
universe u v

def boundary_immersionType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (r : ℕ∞), 1 ≤ r →
    ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    ManifoldContDiff r S.smoothStructure.val T.smoothStructure.val f →
    ∀ p : M, p ∈ intrinsicBoundary S → f p ∈ manifoldInterior T →
    ∀ (F : FiberModel S.smoothStructure.val p)
      (G : FiberModel T.smoothStructure.val (f p)),
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∀ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p),
    IsCoordinateDifferential f p F G L → Function.Injective L →
    m ≤ n ∧ 0 < m ∧ a = .halfSpace ∧
    ∃ e : ModelChart m a M, e ∈ S.smoothStructure.val ∧ p ∈ e.source ∧
      (e p).val ∈ modelFace m a ∧
    ∃ c : OpenPartialHomeomorph N (Euclidean m × Euclidean (n - m)),
      f p ∈ c.source ∧ c.source ⊆ manifoldInterior T ∧
    ∃ d : ModelChart n b N, d ∈ T.smoothStructure.val ∧ c.source ⊆ d.source ∧
    ∃ h : OpenPartialHomeomorph (Euclidean n) (Euclidean m × Euclidean (n - m)),
      ContDiffOn ℝ r h h.source ∧ ContDiffOn ℝ r h.symm h.target ∧
      (∀ y ∈ c.source, (d y).val ∈ h.source ∧ c y = h (d y).val) ∧
      (∀ z ∈ c.target, h.symm z = (d (c.symm z)).val) ∧
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ e.source ∧
      ∀ x ∈ V, f x ∈ c.source ∧ c (f x) = ((e x).val, 0)

end Specs.SmoothManifolds.Ch03.BoundaryImmersion
