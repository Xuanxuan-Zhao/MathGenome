import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The scalar example `d04:08:exponential-tail` (Chapter 8).
`proper` is the ordinary scalar Darboux integral on an ordered finite interval.
The implementation proves agreement with interval integrals for continuous
functions before transferring any measure-integral formula. All orders include
zero. Uniform tails are quantified only on sets a ≥ a₀ > 0, and a single
threshold works for every order up to any prescribed finite order. -/
noncomputable section
open scoped Classical
open Set Filter MeasureTheory Topology
namespace Specs.D04.C08.ExponentialTails.Model

def moment (j : ℕ) (a x : ℝ) : ℝ := x ^ j * Real.exp (-a * x)
def kernel (j : ℕ) (a x : ℝ) : ℝ := (-x) ^ j * Real.exp (-a * x)

def proper (f : ℝ → ℝ) (u v : ℝ) : ℝ :=
  if h : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue f u v then
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue f h else 0

end Specs.D04.C08.ExponentialTails.Model
namespace Specs.D04.C08.ExponentialTails
open Model

def parameter_derivativeType : Prop := ∀ (j : ℕ) (x a : ℝ),
  iteratedDeriv j (fun b => Real.exp (-b * x)) a = kernel j a x

def polynomial_boundType : Prop := ∀ (j : ℕ) {a₀ x : ℝ}, 0 < a₀ → 0 ≤ x →
  x ^ j ≤ (j.factorial : ℝ) * (2 / a₀) ^ j * Real.exp (a₀ * x / 2)

def dominationType : Prop := ∀ (j : ℕ) {a₀ a x : ℝ}, 0 < a₀ → a₀ ≤ a → 0 ≤ x →
  ‖kernel j a x‖ ≤ moment j a₀ x

/-- Absolute convergence is stated both as integrability on the half-line and
as convergence of ordinary proper Darboux integrals. -/
def absolute_convergenceType : Prop := ∀ (j : ℕ) {a : ℝ}, 0 < a →
  IntegrableOn (moment j a) (Ioi 0) ∧
  (∀ u v : ℝ, u ≤ v →
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue (moment j a) u v) ∧
  ∃ I : ℝ, Tendsto (fun R => proper (fun x => ‖kernel j a x‖) 0 R) atTop (𝓝 I)

def uniform_absolute_tailsType : Prop := ∀ {a₀ : ℝ}, 0 < a₀ → ∀ s : ℕ,
  ∀ ε > (0 : ℝ), ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R ≥ R₀, ∀ T ≥ R,
    ∀ a ≥ a₀, ∀ j ≤ s,
      proper (fun x => ‖kernel j a x‖) R T < ε

/-- Actual differentiation under the improper integral, at each finite order;
the same integral is also the limit of the ordinary Darboux truncations. -/
def improper_differentiationType : Prop := ∀ (j : ℕ) {a : ℝ}, 0 < a →
  HasDerivAt (fun b => ∫ x in Ioi (0 : ℝ), kernel j b x)
    (∫ x in Ioi (0 : ℝ), kernel (j + 1) a x) a ∧
  iteratedDeriv j (fun b => ∫ x in Ioi (0 : ℝ), Real.exp (-b * x)) a =
    ∫ x in Ioi (0 : ℝ), kernel j a x ∧
  Tendsto (fun R => proper (kernel j a) 0 R) atTop
    (𝓝 (∫ x in Ioi (0 : ℝ), kernel j a x)) ∧
  iteratedDeriv j (fun b : ℝ => 1 / b) a = ∫ x in Ioi (0 : ℝ), kernel j a x

def moment_formulaType : Prop := ∀ (j : ℕ) {a : ℝ}, 0 < a →
  (∫ x in Ioi (0 : ℝ), moment j a x) = (j.factorial : ℝ) / a ^ (j + 1) ∧
  Tendsto (fun R => proper (moment j a) 0 R) atTop
    (𝓝 ((j.factorial : ℝ) / a ^ (j + 1)))

/-- The finite endpoint may be included, and cutting away a vanishing initial
interval has zero effect. -/
def endpoint_conventionType : Prop := ∀ (j : ℕ) {a : ℝ}, 0 < a →
  (∫ x in Ici (0 : ℝ), moment j a x) = ∫ x in Ioi (0 : ℝ), moment j a x ∧
  Tendsto (fun δ => proper (moment j a) 0 δ) (𝓝[≥] 0) (𝓝 0)
end Specs.D04.C08.ExponentialTails
