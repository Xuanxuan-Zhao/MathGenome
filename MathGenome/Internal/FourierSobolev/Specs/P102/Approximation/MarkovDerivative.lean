import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.BernsteinDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-! Independent specification of Theorem 1.14, including both estimates.
The interval is closed; the derivative is the ordinary formal polynomial
derivative, whose evaluation agrees with the derivative of the polynomial
function. Complex polynomials are evaluated at real arguments. -/
noncomputable section
open scoped Polynomial

namespace P102.Approximation.Expected

/-- The polynomial function on the whole closed real interval. -/
def polynomialOnInterval {𝕜 : Type*} [RCLike 𝕜] (a b : ℝ) (p : 𝕜[X]) :
    C(Set.Icc a b, 𝕜) :=
  ⟨fun x => p.eval (algebraMap ℝ 𝕜 x),
    p.continuous.comp ((RCLike.continuous_ofReal).comp continuous_subtype_val)⟩

def markovRealStatement : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (n : ℕ) (p : ℝ[X]), p.natDegree ≤ n →
    ‖polynomialOnInterval a b p.derivative‖ ≤
      (2 * (n : ℝ) ^ 2 / (b - a)) * ‖polynomialOnInterval a b p‖

def markovComplexStatement : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (n : ℕ) (p : ℂ[X]), p.natDegree ≤ n →
    ‖polynomialOnInterval a b p.derivative‖ ≤
      (2 * (n : ℝ) ^ 2 / (b - a)) * ‖polynomialOnInterval a b p‖

/-- Full original theorem, retaining the arbitrary-period Bernstein estimates. -/
def bernsteinMarkovStatement : Prop :=
  bernsteinRealStatement ∧ bernsteinComplexStatement ∧
    markovRealStatement ∧ markovComplexStatement

end P102.Approximation.Expected
