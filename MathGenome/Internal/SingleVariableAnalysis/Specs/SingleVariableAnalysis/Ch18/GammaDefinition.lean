import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! K03.18.gamma_definition, paper.tex:4031–4046.
The parameter of Gamma is restricted to s > 0. Its value is the sum of
two separately specified endpoint limits of proper Darboux integrals.
The measure integrals in the value formula are identified with those limits
by `independentLimits`; they are not used as a definition of convergence.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.GammaDefinition
open Set MeasureTheory
namespace I
export Specs.SingleVariableAnalysis.Ch08.Integral (realIntegrableValue realIntegralValue)
end I
namespace E
export Specs.SingleVariableAnalysis.Ch10.OneEndpoint
  (leftHasIntegralValue rightHasIntegralValue leftConvergesValue rightConvergesValue)
end E

abbrev gammaKernelType := ℝ → ℝ → ℝ
def gammaKernelValue : gammaKernelType := fun s t => t ^ (s - 1) * Real.exp (-t)

abbrev gammaIntegralType := (s : ℝ) → 0 < s → ℝ
def gammaIntegralValue : gammaIntegralType := fun s _ =>
  (∫ t in (0 : ℝ)..1, gammaKernelValue s t) +
    ∫ t in Ioi (1 : ℝ), gammaKernelValue s t

def properTruncations : Prop := ∀ (s u v : ℝ), 0 < u → u ≤ v →
  ∃ h : I.realIntegrableValue (gammaKernelValue s) u v,
    I.realIntegralValue _ h = ∫ t in u..v, gammaKernelValue s t

def independentLimits : Prop := ∀ (s : ℝ), 0 < s →
  E.leftHasIntegralValue .real (gammaKernelValue s) (0 : WithBot ℝ) 1
    (show ℝ from ∫ t in (0 : ℝ)..1, gammaKernelValue s t) ∧
  E.rightHasIntegralValue .real (gammaKernelValue s) 1 ⊤
    (show ℝ from ∫ t in Ioi (1 : ℝ), gammaKernelValue s t)

def absoluteConvergence : Prop := ∀ (s : ℝ), 0 < s →
  E.leftConvergesValue .real ((fun t : ℝ => |gammaKernelValue s t|) : ℝ → ℝ) (0 : WithBot ℝ) 1 ∧
  E.rightConvergesValue .real ((fun t : ℝ => |gammaKernelValue s t|) : ℝ → ℝ) 1 ⊤

def hasIntegral : Prop := ∀ (s : ℝ) (hs : 0 < s),
  Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints.hasIntegralValue
    .real (gammaKernelValue s) (0 : WithBot ℝ) ⊤ (gammaIntegralValue s hs)

def positive : Prop := ∀ (s : ℝ) (hs : 0 < s), 0 < gammaIntegralValue s hs

/-- Canonical identification is asserted only together with the separate
Riemann-limit obligations above, and only for positive parameters. -/
def eqRealGamma : Prop := ∀ (s : ℝ) (hs : 0 < s), gammaIntegralValue s hs = Real.Gamma s

end Specs.SingleVariableAnalysis.Ch18.GammaDefinition
