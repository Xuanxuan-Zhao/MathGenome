import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The L¹ clause of `fa2:p4:constrained-support`. All scalars are real.
The subspace is arbitrary; it need not be closed. The dual-functional
statement does not require a measure-size assumption. -/
open MeasureTheory
open scoped ENNReal

universe u
noncomputable section
namespace ExpandedFA.PartIV.ConstrainedL1

/-- The support function of the pointwise interval [a,b]. -/
def upperIntegral {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (a b : Lp ℝ ∞ μ) (v : Lp ℝ 1 μ) : ℝ :=
  ∫ x, max (a x * v x) (b x * v x) ∂μ

/-- The manuscript's signed positive/negative-part test. -/
def lowerIntegral {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (a b : Lp ℝ ∞ μ) (v : Lp ℝ 1 μ) : ℝ :=
  ∫ x, a x * max (v x) 0 - b x * max (-v x) 0 ∂μ

namespace Spec

def DominatedDual : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (M : Submodule ℝ (Lp ℝ 1 μ)) (a b : Lp ℝ ∞ μ),
    (∀ᵐ x ∂μ, a x ≤ b x) →
    ((∃ L : Lp ℝ 1 μ →L[ℝ] ℝ,
      (∀ v : M, L v = 0) ∧
      (∀ v, lowerIntegral μ a b v ≤ L v ∧ L v ≤ upperIntegral μ a b v)) ↔
    ∀ v : M, lowerIntegral μ a b v ≤ 0)

/-- Finite-measure integral tests force the ordinary a.e. interval bounds. -/
def FiniteMeasureTests : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (a b h : Lp ℝ ∞ μ),
    (∀ s, MeasurableSet s → μ s < ∞ →
      (∫ x in s, a x ∂μ) ≤ (∫ x in s, h x ∂μ) ∧
      (∫ x in s, h x ∂μ) ≤ (∫ x in s, b x ∂μ)) →
    ∀ᵐ x ∂μ, a x ≤ h x ∧ h x ≤ b x

def ConstrainedExistence : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (M : Submodule ℝ (Lp ℝ 1 μ)) (a b : Lp ℝ ∞ μ),
    (∀ᵐ x ∂μ, a x ≤ b x) →
    ((∃ h : Lp ℝ ∞ μ,
      (∀ᵐ x ∂μ, a x ≤ h x ∧ h x ≤ b x) ∧
      ∀ v : M, (∫ x, h x * (v : Lp ℝ 1 μ) x ∂μ) = 0) ↔
    ∀ v : M, lowerIntegral μ a b v ≤ 0)

end Spec
end ExpandedFA.PartIV.ConstrainedL1
