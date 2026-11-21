import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDerivativeBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! K03.18.gamma_regular, paper.tex:4098–4123.
All orders include zero and all parameters are strictly positive. Integral
values are split at 1, and the endpoint assertions use independent limits of
proper Darboux integrals. The canonical real Gamma agrees with the previously
defined Gamma integral only on this positive domain. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.GammaRegular
open Set MeasureTheory
open scoped ContDiff
namespace B
export GammaDerivativeBounds (kernelValue absoluteConvergence uniformConvergence uniformlySmallTails)
end B
namespace E
export Ch10.OneEndpoint (leftHasIntegralValue rightHasIntegralValue)
end E

abbrev derivativeIntegralType := ℕ → ℝ → ℝ
def derivativeIntegralValue : derivativeIntegralType := fun k s =>
  (∫ t in (0 : ℝ)..1, B.kernelValue k s t) +
    ∫ t in Ioi (1 : ℝ), B.kernelValue k s t

def orderZero : Prop := ∀ (s : ℝ) (hs : 0 < s),
  derivativeIntegralValue 0 s = GammaDefinition.gammaIntegralValue s hs

def independentLimits : Prop := ∀ (k : ℕ) (s : ℝ), 0 < s →
  E.leftHasIntegralValue .real (B.kernelValue k s) (0 : WithBot ℝ) 1
    (show ℝ from ∫ t in (0 : ℝ)..1, B.kernelValue k s t) ∧
  E.rightHasIntegralValue .real (B.kernelValue k s) 1 ⊤
    (show ℝ from ∫ t in Ioi (1 : ℝ), B.kernelValue k s t)

def integralDerivative : Prop := ∀ (k : ℕ) (s : ℝ), 0 < s →
  HasDerivAt (derivativeIntegralValue k) (derivativeIntegralValue (k + 1) s) s

def integralContinuous : Prop := ∀ k : ℕ,
  ContinuousOn (derivativeIntegralValue k) (Ioi 0)

def iteratedDerivativeFormula : Prop := ∀ (k : ℕ) (s : ℝ), 0 < s →
  iteratedDeriv k Real.Gamma s = derivativeIntegralValue k s

def derivativeHasIntegral : Prop := ∀ (k : ℕ) (s : ℝ), 0 < s →
  Ch10.SeveralEndpoints.hasIntegralValue .real (B.kernelValue k s)
    (0 : WithBot ℝ) ⊤ (show ℝ from iteratedDeriv k Real.Gamma s)

def smooth : Prop := ContDiffOn ℝ ∞ Real.Gamma (Ioi 0)

/-- The source's absolute endpoint convergence and locally uniform tails. -/
def absoluteConvergence : Prop := B.absoluteConvergence
def uniformConvergence : Prop := B.uniformConvergence
def uniformlySmallTails : Prop := B.uniformlySmallTails

end Specs.SingleVariableAnalysis.Ch18.GammaRegular
