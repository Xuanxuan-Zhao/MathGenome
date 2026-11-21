import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.LineIntegrals
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge

/-! Independent statements for paper.tex, d04:09:gradient-integral.
The scalar C¹ condition is the shared recursive open-domain condition.
The path data allow tangent jumps, stationary pieces, and a degenerate interval.
All integrals are the shared proper Riemann line integrals. -/
noncomputable section
open Set
namespace Specs.D04.C09.GradientIntegral
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model

/-- The differential and gradient are the already shared derivative objects. -/
def differential_gradientType : Prop := ∀ {n} (f : E n → ℝ) (x v : E n),
  totalDerivative f x v = inner ℝ (scalarGradient f x) v

/-- C¹ data supply both integrability assertions; these are not extra hypotheses. -/
def gradient_integrableType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (U : Set (E n)) (f : E n → ℝ),
  IsOpen U → CrOn 1 U f → trace γ ⊆ U →
  CovectorIntegrable d (totalDerivative f) ∧ WorkIntegrable d (scalarGradient f)

/-- The full endpoint theorem, including existence of both proper integrals. -/
def gradient_integralType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (U : Set (E n)) (f : E n → ℝ),
  IsOpen U → CrOn 1 U f → trace γ ⊆ U →
  ∃ hc : CovectorIntegrable d (totalDerivative f),
    ∃ hw : WorkIntegrable d (scalarGradient f),
      covectorLineIntegral d (totalDerivative f) hc =
        workLineIntegral d (scalarGradient f) hw ∧
      workLineIntegral d (scalarGradient f) hw = f (γ b) - f (γ a)

/-- At a=b even arbitrary field selectors have zero integral. -/
def gradient_integral_degenerateType : Prop := ∀ {n a} {γ : IntervalPath n a a}
  (d : PiecewiseC1Data γ) (f : E n → ℝ),
  ∃ hc : CovectorIntegrable d (totalDerivative f),
    ∃ hw : WorkIntegrable d (scalarGradient f),
      covectorLineIntegral d (totalDerivative f) hc = 0 ∧
      workLineIntegral d (scalarGradient f) hw = 0 ∧ f (γ a) - f (γ a) = 0

end Specs.D04.C09.GradientIntegral
