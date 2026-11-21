import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Absolute
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The damped part of K03.18.dirichlet_integral, paper.tex:4258–4276.
The measure-integral representative J is accompanied by an explicit equality
with the cofinal limit of proper Darboux integrals, as well as absolute
improper convergence. Thus its total definition supplies no existence premise.
The derivative tails are uniform on every half-line a ≥ α > 0, which includes
all compact positive parameter intervals used in the source. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral
open Set MeasureTheory
open Ch10.OneEndpoint Ch10.Absolute Ch14.UniformImproper

abbrev integrandType := ℝ → ℝ → ℝ
def integrandValue : integrandType := fun a x => Real.exp (-a * x) * Real.sinc x
abbrev integralType := ℝ → ℝ
def integralValue : integralType := fun a => ∫ x in Ioi (0 : ℝ), integrandValue a x

def continuousExtension : Prop :=
  (∀ a, Continuous (integrandValue a)) ∧ (∀ a, integrandValue a 0 = 1) ∧
  ∀ a x, x ≠ 0 → integrandValue a x = Real.exp (-a*x) * (Real.sin x / x)

def absoluteConvergence : Prop := ∀ a : ℝ, 0 < a →
  rightHasIntegralValue .real (integrandValue a) 0 ⊤ (integralValue a) ∧
  rightAbsoluteValue .real (integrandValue a) 0 ⊤

def exponentialSineIntegral : Prop := ∀ a : ℝ, 0 < a →
  rightHasIntegralValue .real (fun x => Real.exp (-a*x) * Real.sin x) 0 ⊤
    (1 / (1+a^2))

def uniformDerivativeTails : Prop := ∀ α : ℝ, 0 < α →
  rightUniformHasIntegralValue .real (Ici α)
    (fun x a => -Real.exp (-a.val*x) * Real.sin x) 0 ⊤
    (fun a => -1 / (1+a.val^2))

def derivativeFormula : Prop := ∀ a : ℝ, 0 < a →
  HasDerivAt integralValue (-1 / (1+a^2)) a

def integralBound : Prop := ∀ a : ℝ, 0 < a → |integralValue a| ≤ 1/a

def evaluation : Prop := ∀ a : ℝ, 0 < a → integralValue a = Real.arctan (1/a)

end Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral
