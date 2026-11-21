import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.Indicial

/-! Independent statement of paper.tex, Theorem d13:09:frobenius.
All coefficients below are the canonical Taylor coefficients from Indicial.
The analytic and independence conclusions use the original radius and branch.
This module assumes neither convergence nor a solution certificate. -/

noncomputable section

namespace Specs.D13Unified.Ch09.Frobenius

open Specs.D13Unified.Ch09.Indicial
open scoped BigOperators

def Nonresonant (E : Equation) (r : ℂ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → indicialValue E (r + (n : ℂ)) ≠ 0

/-- Exactly the normalized recurrence, with the source's index `1 ≤ k ≤ n`.
The subtraction in the coefficient factor takes place in ℂ; that in the
sequence index takes place in ℕ, where `k ≤ n` holds. -/
def IsCoefficientSequence (E : Equation) (r : ℂ) (a : ℕ → ℂ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ, 1 ≤ n →
    indicialValue E (r + (n : ℂ)) * a n =
      -∑ k ∈ Finset.Icc 1 n,
        ((r + (n : ℂ) - (k : ℂ)) * taylorCoefficientValue E.p k +
          taylorCoefficientValue E.q k) * a (n - k)

def series (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, a n * z ^ n

def firstTerm (a : ℕ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) * a (n + 1) * z ^ n

def secondTerm (a : ℕ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  (n + 2 : ℂ) * (n + 1 : ℂ) * a (n + 2) * z ^ n

/-- Absolute convergence of the original and differentiated series, with their
actual sums equal to the actual complex derivatives. Holomorphy is asserted on
the entire disc, including zero. -/
def AnalyticSeries (E : Equation) (a : ℕ → ℂ) : Prop :=
  DifferentiableOn ℂ (series a) (Metric.ball 0 E.radius) ∧
  DifferentiableOn ℂ (deriv (series a)) (Metric.ball 0 E.radius) ∧
  series a 0 = 1 ∧
  ∀ z ∈ Metric.ball (0 : ℂ) E.radius,
    Summable (fun n : ℕ => ‖a n * z ^ n‖) ∧
    HasSum (fun n : ℕ => a n * z ^ n) (series a z) ∧
    Summable (fun n : ℕ => ‖firstTerm a z n‖) ∧
    HasSum (firstTerm a z) (deriv (series a) z) ∧
    Summable (fun n : ℕ => ‖secondTerm a z n‖) ∧
    HasSum (secondTerm a z) (deriv (deriv (series a)) z)

def frobeniusFunction (E : Equation) (b : LogBranch E.radius)
    (r : ℂ) (a : ℕ → ℂ) : ℂ → ℂ :=
  fun z => powerValue b r z * series a z

def coefficientUniquenessType : Prop :=
  ∀ (E : Equation) (r : ℂ), Nonresonant E r →
    ∃! a : ℕ → ℂ, IsCoefficientSequence E r a

/-- Full existence, uniqueness, convergence and classical solution assertion. -/
def frobeniusType : Prop :=
  ∀ (E : Equation) (b : LogBranch E.radius) (r : ℂ),
    indicialValue E r = 0 → Nonresonant E r →
    ∃! a : ℕ → ℂ,
      IsCoefficientSequence E r a ∧ AnalyticSeries E a ∧
      solutionValue E b (frobeniusFunction E b r a)

/-- The hypothesis means not equal to *any* complex integer, of either sign. -/
def independentSolutionsType : Prop :=
  ∀ (E : Equation) (b : LogBranch E.radius) (r₁ r₂ : ℂ),
    indicialValue E r₁ = 0 → indicialValue E r₂ = 0 →
    (∀ m : ℤ, r₁ - r₂ ≠ (m : ℂ)) →
    ∀ a₁ a₂ : ℕ → ℂ,
      IsCoefficientSequence E r₁ a₁ → IsCoefficientSequence E r₂ a₂ →
      independentValue b (frobeniusFunction E b r₁ a₁)
        (frobeniusFunction E b r₂ a₂)

/-- The noninteger hypothesis supplies both nonresonance hypotheses needed
to apply the single-root existence theorem. -/
def rootSeparationType : Prop :=
  ∀ (E : Equation) (r₁ r₂ : ℂ),
    indicialValue E r₁ = 0 → indicialValue E r₂ = 0 →
    (∀ m : ℤ, r₁ - r₂ ≠ (m : ℂ)) →
    r₁ ≠ r₂ ∧ Nonresonant E r₁ ∧ Nonresonant E r₂

/-- The ordinary analytic multiplier satisfies the equation obtained by
substituting `y = exp(r log z) f`. Unlike the original singular equation,
this identity also makes sense at zero. -/
def MultiplierEquation (E : Equation) (r : ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ Metric.ball (0 : ℂ) E.radius,
    z ^ 2 * deriv (deriv f) z + z * (2 * r + E.p z) * deriv f z +
      (r * (r - 1) + r * E.p z + E.q z) * f z = 0

def powerSolutionBridgeType : Prop :=
  ∀ (E : Equation) (b : LogBranch E.radius) (r : ℂ) (f : ℂ → ℂ),
    DifferentiableOn ℂ f (Metric.ball 0 E.radius) →
    MultiplierEquation E r f →
    solutionValue E b (fun z => powerValue b r z * f z)

def independentMultipliersType : Prop :=
  ∀ (E : Equation) (b : LogBranch E.radius) (r₁ r₂ : ℂ), r₁ ≠ r₂ →
    ∀ f₁ f₂ : ℂ → ℂ,
      DifferentiableOn ℂ f₁ (Metric.ball 0 E.radius) →
      DifferentiableOn ℂ f₂ (Metric.ball 0 E.radius) →
      f₁ 0 = 1 → f₂ 0 = 1 →
      independentValue b (fun z => powerValue b r₁ z * f₁ z)
        (fun z => powerValue b r₂ z * f₂ z)

end Specs.D13Unified.Ch09.Frobenius
