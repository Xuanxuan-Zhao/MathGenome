import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathOperations
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The triangle criterion, paper.tex:671–686. Closed triangles are real convex
hulls, including collinear and repeated vertices. Their oriented boundary
integral is the sum of the three directed segment integrals. -/
noncomputable section
open Set MeasureTheory
open scoped Topology

namespace D12Complex

/-- The directed segment, with its genuine smooth traversal on [0,1]. -/
def segmentPath (a b : ℂ) : PiecewiseC1Path :=
  let γ : ComplexPath := ⟨0, 1, zero_le_one, AffineMap.lineMap a b,
    AffineMap.lineMap_continuous.continuousOn⟩
  ⟨γ, ⟨C1Partition.single γ (by
    change ContDiffOn ℝ 1 (AffineMap.lineMap a b) (Icc 0 1)
    have heq : (AffineMap.lineMap a b : ℝ → ℂ) =
        (fun t : ℝ => t • (b - a) + a) := by
      funext t; exact AffineMap.lineMap_apply_module' a b t
    rw [heq]
    exact ((contDiff_id.smul contDiff_const).add contDiff_const).contDiffOn)⟩⟩

def segmentIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ := (segmentPath a b).integral f

def triangleBoundaryIntegral (f : ℂ → ℂ) (a b c : ℂ) : ℂ :=
  segmentIntegral f a b + segmentIntegral f b c + segmentIntegral f c a

/-- The geometric hypothesis, with no differentiability assumption on f. -/
def ZeroTriangleIntegrals (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ a b c : ℂ, convexHull ℝ {a, b, c} ⊆ Ω → triangleBoundaryIntegral f a b c = 0

def radialPrimitive (f : ℂ → ℂ) (a : ℂ) : ℂ → ℂ := segmentIntegral f a

end D12Complex

namespace Specs.D12Complex.Ch03.TrianglePrimitiveCriterion
open _root_.D12Complex

def segmentPath_type := ℂ → ℂ → PiecewiseC1Path
def segmentPath_value : segmentPath_type := segmentPath

def segmentIntegral_type := (ℂ → ℂ) → ℂ → ℂ → ℂ
def segmentIntegral_value : segmentIntegral_type := segmentIntegral

def triangleBoundaryIntegral_type := (ℂ → ℂ) → ℂ → ℂ → ℂ → ℂ
def triangleBoundaryIntegral_value : triangleBoundaryIntegral_type := triangleBoundaryIntegral

def ZeroTriangleIntegrals_type := Set ℂ → (ℂ → ℂ) → Prop
def ZeroTriangleIntegrals_value : ZeroTriangleIntegrals_type := ZeroTriangleIntegrals

def radialPrimitive_type := (ℂ → ℂ) → ℂ → ℂ → ℂ
def radialPrimitive_value : radialPrimitive_type := radialPrimitive

def segmentPath_trace_type : Prop := ∀ a b : ℂ,
  (segmentPath a b).trace = segment ℝ a b

def segmentIntegral_formula_type : Prop := ∀ (f : ℂ → ℂ) (a b : ℂ),
  ContinuousOn f (segment ℝ a b) →
  segmentIntegral f a b = ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap a b t) * (b - a)

def segmentIntegral_reverse_type : Prop := ∀ (f : ℂ → ℂ) (a b : ℂ),
  ContinuousOn f (segment ℝ a b) → segmentIntegral f b a = -segmentIntegral f a b

def segmentIntegral_subsegment_add_type : Prop := ∀ (f : ℂ → ℂ) (a b c : ℂ),
  c ∈ segment ℝ a b → ContinuousOn f (segment ℝ a b) →
  segmentIntegral f a c + segmentIntegral f c b = segmentIntegral f a b

/-- A collinear triangle, with its middle vertex c; cyclic reordering and
reversal give every ordering of the same degenerate triangle. -/
def triangleBoundaryIntegral_degenerate_type : Prop := ∀ (f : ℂ → ℂ) (a b c : ℂ),
  c ∈ segment ℝ a b → ContinuousOn f (segment ℝ a b) →
  triangleBoundaryIntegral f a c b = 0

def triangleBoundaryIntegral_collinear_type : Prop := ∀ (f : ℂ → ℂ) (a b c : ℂ),
  Collinear ℝ ({a, b, c} : Set ℂ) → ContinuousOn f (convexHull ℝ {a, b, c}) →
  triangleBoundaryIntegral f a b c = 0

/-- The degenerate cases need not be separately assumed. -/
def zeroTriangleIntegrals_iff_noncollinear_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), ContinuousOn f Ω →
  (ZeroTriangleIntegrals Ω f ↔ ∀ a b c : ℂ,
    ¬ Collinear ℝ ({a, b, c} : Set ℂ) → convexHull ℝ {a, b, c} ⊆ Ω →
    triangleBoundaryIntegral f a b c = 0)

def triangle_primitive_criterion_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ) (f : ℂ → ℂ), IsOpen Ω → a ∈ Ω →
  StarConvex ℝ a Ω → ContinuousOn f Ω → ZeroTriangleIntegrals Ω f →
  HolomorphicOn Ω (radialPrimitive f a) ∧
  ∀ z ∈ Ω, HasDerivAt (radialPrimitive f a) (f z) z

def convex_triangle_primitive_criterion_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ) (f : ℂ → ℂ), IsOpen Ω → a ∈ Ω →
  Convex ℝ Ω → ContinuousOn f Ω → ZeroTriangleIntegrals Ω f →
  HolomorphicOn Ω (radialPrimitive f a) ∧
  ∀ z ∈ Ω, HasDerivAt (radialPrimitive f a) (f z) z

end Specs.D12Complex.Ch03.TrianglePrimitiveCriterion
