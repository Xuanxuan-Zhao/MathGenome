import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Frames
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! Independent interface for the metric-existence clause of M05.05
(paper.tex 1306--1310). No metric on the given bundle is assumed. -/
namespace SmoothManifolds.BundleMetricData
open ModelData AtlasData BundleData Bundle Set
universe u v w

/-- A smooth real fiber metric. Smoothness means that every Gram coefficient in
any of the given smooth linear trivializations has local smooth ambient
extensions in every base chart. This is the coordinate definition of a smooth
bilinear form on a vector bundle, also for bases with ordinary boundary. -/
structure SmoothFiberMetric {n r : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v}
    {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) where
  form : (p : M) → LinearMap.BilinForm ℝ (E p)
  symmetric : ∀ p x y, form p x y = form p y x
  positive : ∀ p (x : E p), x ≠ 0 → 0 < form p x x
  smooth : ∀ (i : ι) (j k : Fin r), SmoothOnBase S
    (fun p => form p ((B.trivialization i).symm p (Pi.single j 1))
      ((B.trivialization i).symm p (Pi.single k 1))) (B.baseSet i)

end SmoothManifolds.BundleMetricData

namespace Specs.SmoothManifolds.Ch05.BundleMetrics
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.BundleData _root_.SmoothManifolds.BundleMetricData Bundle
universe u v w

/-- Every finite rank smooth bundle over a Hausdorff second countable smooth
manifold has a smooth symmetric positive definite metric. There is no
nonemptiness, compactness, connectedness, positive-rank, or interior assumption. -/
def exists_smoothFiberMetricType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E), Nonempty (SmoothFiberMetric B)

end Specs.SmoothManifolds.Ch05.BundleMetrics
