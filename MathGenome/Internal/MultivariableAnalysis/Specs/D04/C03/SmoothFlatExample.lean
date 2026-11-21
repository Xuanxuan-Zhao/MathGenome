import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-! Independent specification for chapters/03.tex, d04:03:flat-example. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C03.SmoothFlatExample
namespace Model
/-- The source's function, including its separately prescribed value at zero. -/
def flatFunction (x : ℝ) : ℝ := if x = 0 then 0 else Real.exp (-1 / x^2)
end Model
abbrev flatFunctionType := ℝ → ℝ
def flatFunctionValue : flatFunctionType := Model.flatFunction

def flatFunction_smoothType : Prop :=
  Specs.D04.C02.DerivativeInterfaces.Model.SmoothOn Set.univ Model.flatFunction

def flatFunction_derivatives_zeroType : Prop :=
  ∀ j : ℕ, iteratedDeriv j Model.flatFunction 0 = 0

def flatFunction_posType : Prop :=
  ∀ x : ℝ, x ≠ 0 → 0 < Model.flatFunction x

def flatFunction_integer_decayType : Prop :=
  ∀ N : ℤ, Tendsto (fun x : ℝ => |x| ^ (-N) * Real.exp (-1 / x^2))
    (𝓝[≠] 0) (𝓝 0)

def flatFunction_derivative_polynomialType : Prop :=
  ∀ j : ℕ, ∃ p : Polynomial ℝ, ∀ x : ℝ, x ≠ 0 →
    iteratedDeriv j Model.flatFunction x = p.eval x⁻¹ * Real.exp (-1 / x^2)

def flatFunction_taylor_zeroType : Prop :=
  ∀ (k : ℕ) (h : ℝ),
    Specs.D04.C03.HigherInterfaces.Model.taylorPolynomial k Model.flatFunction 0 h = 0

def flatFunction_taylor_seriesType : Prop :=
  ∀ x : ℝ, HasSum (fun j : ℕ =>
    iteratedDeriv j Model.flatFunction 0 / (j.factorial : ℝ) * x^j) 0

def flatFunction_no_taylor_neighborhoodType : Prop :=
  ¬ ∃ U : Set ℝ, U ∈ 𝓝 0 ∧ ∀ x ∈ U,
    HasSum (fun j : ℕ => iteratedDeriv j Model.flatFunction 0 /
      (j.factorial : ℝ) * x^j) (Model.flatFunction x)

def flatFunction_not_analyticType : Prop := ¬ AnalyticAt ℝ Model.flatFunction 0

end Specs.D04.C03.SmoothFlatExample
