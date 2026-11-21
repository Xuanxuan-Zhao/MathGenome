import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
K03.14.boundary_terms, paper.tex:3551–3559.
The integrand is literally one and the endpoints are zero and the real parameter.
All integral expressions use the shared oriented proper Darboux integral, with
an explicit integrability proof, including for negative and zero parameters.
The final statement evaluates the upper, lower and interior Leibniz terms
separately, and identifies their sum as the derivative of the integral family.
-/
namespace Specs.SingleVariableAnalysis.Ch14.BoundaryTerms
open Specs.SingleVariableAnalysis.Ch08

/-- The spatial and parameter variables of the source integrand. -/
def integrand (_x _t : ℝ) : ℝ := 1

def integrable : Prop :=
  ∀ t : ℝ, Oriented.realIntegrableValue (fun x => integrand x t) 0 t

def integralValue : Prop :=
  ∀ (t : ℝ) (h : Oriented.realIntegrableValue (fun x => integrand x t) 0 t),
    Oriented.realIntegralValue (fun x => integrand x t) h = t

def integralDerivative : Prop :=
  ∀ h : ∀ t : ℝ, Oriented.realIntegrableValue (fun x => integrand x t) 0 t,
    ∀ t : ℝ, HasDerivAt
      (fun s => Oriented.realIntegralValue (fun x => integrand x s) (h s)) 1 t

def partialDerivative : Prop :=
  ∀ x t : ℝ, HasDerivAt (integrand x) 0 t ∧ deriv (integrand x) t = 0

def leibnizContributions : Prop :=
  ∀ t : ℝ,
    ∃ h₀ : Oriented.realIntegrableValue (fun x => deriv (integrand x) t) 0 t,
      integrand t t * deriv (fun s : ℝ => s) t = 1 ∧
      integrand 0 t * deriv (fun _ : ℝ => (0 : ℝ)) t = 0 ∧
      Oriented.realIntegralValue (fun x => deriv (integrand x) t) h₀ = 0 ∧
      ∀ h : ∀ s : ℝ, Oriented.realIntegrableValue (fun x => integrand x s) 0 s,
        HasDerivAt
          (fun s => Oriented.realIntegralValue (fun x => integrand x s) (h s))
          (integrand t t * deriv (fun s : ℝ => s) t -
            integrand 0 t * deriv (fun _ : ℝ => (0 : ℝ)) t +
            Oriented.realIntegralValue (fun x => deriv (integrand x) t) h₀) t

end Specs.SingleVariableAnalysis.Ch14.BoundaryTerms
