import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Independent statements for paper.tex:827–857 (D12.04.01).
The closed triangle is the real convex hull, with no nondegeneracy condition.
Boundary integrals are sums of the canonical contour integrals along their
directed sides. The theorem holds for either vertex ordering, hence in
particular for the positive orientation. -/

noncomputable section
open Set

namespace Specs.D12Complex.Ch04.WeakGoursat
open _root_.D12Complex

def segmentPath_type := ℂ → ℂ → PiecewiseC1Path
def segmentPath_value : segmentPath_type := fun a b =>
  ⟨⟨0, 1, zero_le_one, fun t => a + t • (b - a),
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn⟩,
    ⟨C1Partition.single _
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn⟩⟩
def closedTriangle_type := ℂ → ℂ → ℂ → Set ℂ
def closedTriangle_value : closedTriangle_type := fun a b c => convexHull ℝ {a, b, c}
def triangleBoundaryIntegral_type := ℂ → ℂ → ℂ → (ℂ → ℂ) → ℂ
def triangleBoundaryIntegral_value : triangleBoundaryIntegral_type := fun a b c f =>
  (segmentPath_value a b).integral f + (segmentPath_value b c).integral f +
    (segmentPath_value c a).integral f
def closedParallelogram_type := ℂ → ℂ → ℂ → Set ℂ
def closedParallelogram_value : closedParallelogram_type :=
  fun a u v => convexHull ℝ {a, a + u, a + u + v, a + v}
def parallelogramBoundaryIntegral_type := ℂ → ℂ → ℂ → (ℂ → ℂ) → ℂ
def parallelogramBoundaryIntegral_value : parallelogramBoundaryIntegral_type := fun a u v f =>
  (segmentPath_value a (a + u)).integral f +
    (segmentPath_value (a + u) (a + u + v)).integral f +
    (segmentPath_value (a + u + v) (a + v)).integral f +
    (segmentPath_value (a + v) a).integral f

def goursat_triangle_type : Prop :=
  ∀ (a b c : ℂ) (Ω : Set ℂ) (f : ℂ → ℂ),
    HolomorphicOn Ω f → closedTriangle_value a b c ⊆ Ω →
    triangleBoundaryIntegral_value a b c f = 0

def goursat_parallelogram_type : Prop :=
  ∀ (a u v : ℂ) (Ω : Set ℂ) (f : ℂ → ℂ),
    HolomorphicOn Ω f → closedParallelogram_value a u v ⊆ Ω →
    parallelogramBoundaryIntegral_value a u v f = 0

/-- Every (possibly rotated or degenerate) rectangle is covered: e gives its
direction and w,h its real side lengths. Multiplication by I turns the
second side through a right angle. Positive w,h and e ≠ 0 give the positive
boundary orientation. No such restriction is needed for the zero integral. -/
def goursat_rectangle_type : Prop :=
  ∀ (a e : ℂ) (w h : ℝ) (Ω : Set ℂ) (f : ℂ → ℂ),
    HolomorphicOn Ω f →
    closedParallelogram_value a ((w : ℂ) * e) ((h : ℂ) * Complex.I * e) ⊆ Ω →
    parallelogramBoundaryIntegral_value a ((w : ℂ) * e) ((h : ℂ) * Complex.I * e) f = 0

end Specs.D12Complex.Ch04.WeakGoursat
