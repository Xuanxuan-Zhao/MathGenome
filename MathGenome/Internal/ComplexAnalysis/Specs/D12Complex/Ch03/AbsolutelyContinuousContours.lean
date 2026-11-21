import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.RectifiableStieltjes
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathOperations
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! The AC bridge in paper.tex:689–727. The AC hypothesis is the usual
finite-disjoint-interval condition, not an integral representation certificate.
`deriv` is the total ordinary real derivative; its values at the null exceptional
set do not affect the Lebesgue integral. All hypotheses concern the closed
parameter interval, and singleton intervals are included. -/
noncomputable section
open Set MeasureTheory

namespace Specs.D12Complex.Ch03.AbsolutelyContinuousContours
open _root_.D12Complex _root_.D12Complex.Stieltjes

def ac_derivative_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ γ : ℝ → ℂ,
    AbsolutelyContinuousOnInterval γ a b →
    IntervalIntegrable (deriv γ) volume a b ∧
    (∀ᵐ t ∂volume, t ∈ Ioo a b → HasDerivAt γ (deriv γ t) t) ∧
    ∀ x ∈ Icc a b, γ x = γ a + ∫ t in a..x, deriv γ t

def ac_finite_variation_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ γ : ℝ → ℂ,
    AbsolutelyContinuousOnInterval γ a b → totalVariation γ a b < ⊤

def hasIntegral_ac_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ u γ : ℝ → ℂ,
    ContinuousOn u (Icc a b) → AbsolutelyContinuousOnInterval γ a b →
    HasIntegral a b u γ (∫ t in a..b, u t * deriv γ t)

def integral_ac_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ u γ : ℝ → ℂ,
    ContinuousOn u (Icc a b) → AbsolutelyContinuousOnInterval γ a b →
    IntervalIntegrable (fun t => u t * deriv γ t) volume a b ∧
    integral a b u γ = ∫ t in a..b, u t * deriv γ t

def piecewiseC1_ac_type : Prop :=
  ∀ γ : ComplexPath, IsPiecewiseC1 γ → AbsolutelyContinuousOnInterval γ γ.a γ.b

def contourIntegral_ac_type : Prop :=
  ∀ γ : ComplexPath, AbsolutelyContinuousOnInterval γ γ.a γ.b →
    ∀ f : ℂ → ℂ, ContinuousOn f γ.trace →
    Rectifiable γ ∧ contourIntegral γ f = ∫ t in γ.a..γ.b, f (γ t) * deriv γ t

def contourIntegral_piecewiseC1_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (f : ℂ → ℂ), ContinuousOn f γ.trace →
    Rectifiable γ.path ∧ contourIntegral γ.path f = γ.integral f

end Specs.D12Complex.Ch03.AbsolutelyContinuousContours
