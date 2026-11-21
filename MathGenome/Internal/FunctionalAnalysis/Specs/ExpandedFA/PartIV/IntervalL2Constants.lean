import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.IntervalL1Constants
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Independent L² clauses of paper.tex:19933–19979,
`fa2:p4:sharp-interval-poincare`. H¹ means the actual distributional
W¹,² graph, and H¹₀ means its closure-defined zero-boundary subspace.
Scalar coefficients are in R or C. Equality concerns the unique continuous
representative on [0,1], with the zero function included. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace ExpandedFA.PartIV.IntervalL2
open ExpandedFA.Sobolev.OneDimensional
open ExpandedFA.PartIV.IntervalL1 (unitInterval mean)

abbrev H1 (𝕜 : Type) [RCLike 𝕜] := W1p 𝕜 unitInterval 2

def ZeroTrace {𝕜 : Type} [RCLike 𝕜] (u : H1 𝕜) : Prop :=
  u ∈ Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.ZeroSpaceValue
    𝕜 1 (lineDomain unitInterval) 1 2 (by norm_num)

/-- Ordinary unnormalized Lebesgue L² norm on the unit interval. -/
def l2Norm {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) : ℝ :=
  (eLpNorm f 2 (volume.restrict (Ioo (0 : ℝ) 1))).toReal

def CosineOptimizer {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) : Prop :=
  ∃ a b : 𝕜, EqOn f (fun x => a + b * (Real.cos (Real.pi * x) : 𝕜)) (Icc 0 1)

def SineOptimizer {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) : Prop :=
  ∃ b : 𝕜, EqOn f (fun x => b * (Real.sin (Real.pi * x) : 𝕜)) (Icc 0 1)

end ExpandedFA.PartIV.IntervalL2

namespace Specs.ExpandedFA.PartIV.IntervalL2Constants
open _root_.ExpandedFA.PartIV.IntervalL2
open _root_.ExpandedFA.PartIV.IntervalL1 (mean)
open _root_.ExpandedFA.Sobolev.OneDimensional

def NormIdentification : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f →
    l2Norm f = ‖baseLp u‖ ∧
    l2Norm (lineFunction (derivativeLp u)) = ‖derivativeLp u‖ ∧
    (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) = l2Norm f ^ 2

def ZeroTraceIdentification : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f →
    (ZeroTrace u ↔ f 0 = 0 ∧ f 1 = 0)

def MeanBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f →
    l2Norm (fun x => f x - mean f) ≤ Real.pi⁻¹ * ‖derivativeLp u‖

def ZeroBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f → ZeroTrace u →
    l2Norm f ≤ Real.pi⁻¹ * ‖derivativeLp u‖

def MeanEquality : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f →
    (l2Norm (fun x => f x - mean f) = Real.pi⁻¹ * ‖derivativeLp u‖ ↔
      CosineOptimizer f)

def ZeroEquality : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f → ZeroTrace u →
    (l2Norm f = Real.pi⁻¹ * ‖derivativeLp u‖ ↔ SineOptimizer f)

/-- Sufficiency halves of the full equality classifications above. -/
def MeanOptimizerSufficiency : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f → CosineOptimizer f →
    l2Norm (fun x => f x - mean f) = Real.pi⁻¹ * ‖derivativeLp u‖

def ZeroOptimizerSufficiency : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f → SineOptimizer f →
    ZeroTrace u ∧ l2Norm f = Real.pi⁻¹ * ‖derivativeLp u‖

def MeanSharp : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (C : ℝ), C < Real.pi⁻¹ →
    ∃ (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f ∧
      0 < ‖derivativeLp u‖ ∧
      C * ‖derivativeLp u‖ < l2Norm (fun x => f x - mean f)

def ZeroSharp : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (C : ℝ), C < Real.pi⁻¹ →
    ∃ (u : H1 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f ∧ ZeroTrace u ∧
      0 < ‖derivativeLp u‖ ∧ C * ‖derivativeLp u‖ < l2Norm f

end Specs.ExpandedFA.PartIV.IntervalL2Constants
