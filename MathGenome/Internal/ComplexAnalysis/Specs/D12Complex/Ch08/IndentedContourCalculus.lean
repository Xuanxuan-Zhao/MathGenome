import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.OrderedIndentedDiameter
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.IndexComputations
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathOperations

/-! Finite indented contours for paper.tex:2147–2162.  All paths and indices
are the canonical Ch03/Ch04 objects.  The witness precedes the integrand. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Specs.D12Complex.Ch08.IndentedContourCalculus
open _root_.D12Complex
namespace Diameter
export Specs.D12Complex.Ch08.OrderedIndentedDiameter
  (Admissible Gaps Traversal Retained TraceSet)
end Diameter

def Geometry (s : Finset ℝ) (r : ℝ) (ε : s → ℝ) : Prop :=
  0 < r ∧ (∀ x, 0 < ε x ∧ |x.val| + 2 * ε x < r) ∧
    ∀ x y, x ≠ y → 2 * ε x + 2 * ε y < |x.val - y.val|

def TraceSet (s : Finset ℝ) (r : ℝ) (ε : s → ℝ) : Set ℂ :=
  Complex.ofReal '' Diameter.Retained s (-r) r ε ∪
    circleMap 0 r '' Icc 0 Real.pi ∪
    ⋃ x : s, circleMap (x.val : ℂ) (ε x) '' Icc 0 Real.pi

def ArcIntegrand (c : ℂ) (r : ℝ) (f : ℂ → ℂ) (t : ℝ) : ℂ :=
  f (circleMap c r t) * (circleMap 0 r t * Complex.I)

def BoundaryIntegral (s : Finset ℝ) (r : ℝ) (ε : s → ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x in Diameter.Retained s (-r) r ε, f (x : ℂ)) +
    (∫ t in (0:ℝ)..Real.pi, ArcIntegrand 0 r f t) -
    ∑ x : s, ∫ t in (0:ℝ)..Real.pi, ArcIntegrand (x.val : ℂ) (ε x) f t

def IntegrableBoundary (s : Finset ℝ) (r : ℝ) (ε : s → ℝ) (f : ℂ → ℂ) : Prop :=
  IntegrableOn (fun x : ℝ => f (x : ℂ)) (Diameter.Retained s (-r) r ε) ∧
    IntervalIntegrable (ArcIntegrand 0 r f) volume 0 Real.pi ∧
    ∀ x : s, IntervalIntegrable (ArcIntegrand (x.val : ℂ) (ε x) f) volume 0 Real.pi

/-- The ordered diameter is followed by the positive outer upper semicircle.
This fixes the directed concatenation independently of any integrand. -/
def ClosingTraversal (γ δ : PiecewiseC1Path) : Prop :=
  δ.path.a = 0 ∧ δ.path.b = 2 ∧
    EqOn δ (fun t => γ (γ.path.a + (γ.path.b - γ.path.a) * t)) (Icc 0 1)

/-- Full constructive geometric witness, including the empty indentation set. -/
def contour_exists_type : Prop :=
  ∀ (s : Finset ℝ) (r : ℝ) (ε : s → ℝ), Geometry s r ε →
    ∃ (n : ℕ) (e : Fin n ≃ s) (start stop : Fin (n+1) → ℝ)
      (γ δ : PiecewiseC1Path),
      Diameter.Gaps (-r) r ε e start stop ∧ Diameter.Traversal ε e start stop γ ∧
      γ.path.source = (-r : ℂ) ∧ γ.path.target = (r : ℂ) ∧
      ClosingTraversal γ δ ∧
      EqOn δ (fun t => circleMap 0 r (Real.pi * (t-1))) (Icc 1 2) ∧
      δ.IsClosed ∧ δ.trace = TraceSet s r ε

def contour_calculus_type : Prop :=
  ∀ (s : Finset ℝ) (r : ℝ) (ε : s → ℝ), Geometry s r ε →
    ∃ (n : ℕ) (e : Fin n ≃ s) (start stop : Fin (n+1) → ℝ)
      (γ δ : PiecewiseC1Path),
      Diameter.Gaps (-r) r ε e start stop ∧ Diameter.Traversal ε e start stop γ ∧
      γ.path.source = (-r : ℂ) ∧ γ.path.target = (r : ℂ) ∧
      ClosingTraversal γ δ ∧
      EqOn δ (fun t => circleMap 0 r (Real.pi * (t-1))) (Icc 1 2) ∧
      δ.IsClosed ∧ δ.trace = TraceSet s r ε ∧
      (∀ f : ℂ → ℂ, ContinuousOn f (TraceSet s r ε) →
        IntegrableBoundary s r ε f ∧
        IntervalIntegrable (fun t => f (δ t) * deriv δ t) volume δ.path.a δ.path.b ∧
        δ.integral f = BoundaryIntegral s r ε f) ∧
      (∀ a : ℂ, ‖a‖ < r → 0 < a.im → (∀ x : s, ε x < ‖a - (x.val : ℂ)‖) →
        a ∉ δ.trace ∧ δ.index a = 1) ∧
      (∀ a : ℂ, a.im ≤ 0 → a ∉ TraceSet s r ε → δ.index a = 0)
end Specs.D12Complex.Ch08.IndentedContourCalculus
