import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDefinition

/-! K03.18.gaussian, paper.tex:4233–4252.
The half-line and whole-line claims use independent limits of proper Darboux
integrals. In particular the whole-line assertion is not a principal value.
The square substitution is asserted on every regular positive truncation.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.Gaussian
open MeasureTheory Set
namespace I
export Ch08.Integral (realIntegrableValue realIntegralValue)
end I
namespace E
export Ch10.OneEndpoint (rightHasIntegralValue leftHasIntegralValue)
end E
namespace M
export Ch10.SeveralEndpoints (hasIntegralValue)
end M

abbrev gaussianKernelType := ℝ → ℝ
def gaussianKernelValue : gaussianKernelType := fun x => Real.exp (-(x ^ 2))

def gammaHalf : Prop :=
  GammaDefinition.gammaIntegralValue (1 / 2) (by norm_num) = Real.sqrt Real.pi

def properTruncations : Prop := ∀ a b : ℝ, a ≤ b →
  ∃ h : I.realIntegrableValue gaussianKernelValue a b,
    I.realIntegralValue _ h = ∫ x in a..b, gaussianKernelValue x

def squareSubstitution : Prop := ∀ a b : ℝ, 0 < a → a ≤ b →
  ∃ (hg : I.realIntegrableValue (GammaDefinition.gammaKernelValue (1 / 2))
      (a ^ 2) (b ^ 2))
    (hf : I.realIntegrableValue gaussianKernelValue a b),
    I.realIntegralValue _ hg = 2 * I.realIntegralValue _ hf

def positiveHalf : Prop := E.rightHasIntegralValue .real gaussianKernelValue 0 ⊤
  (Real.sqrt Real.pi / 2)

def negativeHalf : Prop := E.leftHasIntegralValue .real gaussianKernelValue ⊥ 0
  (Real.sqrt Real.pi / 2)

def wholeLine : Prop := M.hasIntegralValue .real gaussianKernelValue ⊥ ⊤
  (Real.sqrt Real.pi)

def absoluteConvergence : Prop := M.hasIntegralValue .real
  ((fun x : ℝ => |gaussianKernelValue x|) : ℝ → ℝ) ⊥ ⊤ (Real.sqrt Real.pi)

/-- The value of the Gamma integral is twice the independently convergent
positive Gaussian integral. Quantification over its value avoids choosing a
total integral as a substitute for convergence. -/
def gammaGaussianRelation : Prop := ∀ L : ℝ,
  E.rightHasIntegralValue .real gaussianKernelValue 0 ⊤ L →
  GammaDefinition.gammaIntegralValue (1 / 2) (by norm_num) = 2 * L

end Specs.SingleVariableAnalysis.Ch18.Gaussian
