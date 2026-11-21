import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.HolomorphicDiscLinearIVP
import Mathlib.Analysis.Complex.TaylorSeries

/-! Independent statements for `paper.tex`, d13:09:ordinary-series.
All derivatives are complex derivatives and all domains are the full given disc.
The radius is extended nonnegative real, allowing the entire plane. -/
open scoped ENNReal BigOperators

namespace D13Unified.Ch09.OrdinarySeries

open HolomorphicDiscLinearIVP

/-- The coefficient of the Taylor series at the ordinary point zero. -/
noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- An actual convergent series on the prescribed open disc. -/
def HasSeriesOnDisc (R : ℝ≥0∞) (f : ℂ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ z ∈ disc R, HasSum (fun n => a n * z ^ n) (f z)

/-- A classical complex second-order solution, including the initial data. -/
def IsOrdinarySolution (R : ℝ≥0∞) (p q : ℂ → ℂ) (a₀ a₁ : ℂ)
    (y : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ y (disc R) ∧ DifferentiableOn ℂ (deriv y) (disc R) ∧
  y 0 = a₀ ∧ deriv y 0 = a₁ ∧
  ∀ z ∈ disc R, deriv (deriv y) z + p z * deriv y z + q z * y z = 0

/-- The ordinary-point coefficient recurrence, with exactly the source indexing. -/
def OrdinaryRecurrence (p q a : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, ((n : ℂ) + 2) * ((n : ℂ) + 1) * a (n+2) =
    -(∑ k ∈ Finset.range (n+1),
      ((((n-k : ℕ) : ℂ) + 1) * p k * a (n-k+1) + q k * a (n-k)))

end D13Unified.Ch09.OrdinarySeries

namespace Specs.D13Unified.Ch09.OrdinarySeries

open _root_.D13Unified.Ch09.HolomorphicDiscLinearIVP
open _root_.D13Unified.Ch09.OrdinarySeries

/-- The second-order IVP exists uniquely on the full disc. -/
def ordinary_ivp_type : Prop :=
  ∀ (R : ℝ≥0∞), 0 < R → ∀ p q : ℂ → ℂ,
    DifferentiableOn ℂ p (disc R) → DifferentiableOn ℂ q (disc R) →
    ∀ a₀ a₁ : ℂ, ∃ y : ℂ → ℂ,
      IsOrdinarySolution R p q a₀ a₁ y ∧
      ∀ v, IsOrdinarySolution R p q a₀ a₁ v → Set.EqOn v y (disc R)

/-- Every solution has a convergent Taylor expansion on the entire disc and
its coefficients obey the stated recurrence for the given coefficient series. -/
def ordinary_series_type : Prop :=
  ∀ (R : ℝ≥0∞), 0 < R → ∀ (p q : ℂ → ℂ) (pₖ qₖ : ℕ → ℂ),
    DifferentiableOn ℂ p (disc R) → DifferentiableOn ℂ q (disc R) →
    HasSeriesOnDisc R p pₖ → HasSeriesOnDisc R q qₖ →
    ∀ (a₀ a₁ : ℂ) (y : ℂ → ℂ), IsOrdinarySolution R p q a₀ a₁ y →
      taylorCoeff y 0 = a₀ ∧ taylorCoeff y 1 = a₁ ∧
      HasSeriesOnDisc R y (taylorCoeff y) ∧
      OrdinaryRecurrence pₖ qₖ (taylorCoeff y)

/-- Conversely every recursively specified sequence converges on the full disc
and sums to its unique holomorphic IVP solution. No convergence is a premise. -/
def recursive_series_type : Prop :=
  ∀ (R : ℝ≥0∞), 0 < R → ∀ (p q : ℂ → ℂ) (pₖ qₖ : ℕ → ℂ),
    DifferentiableOn ℂ p (disc R) → DifferentiableOn ℂ q (disc R) →
    HasSeriesOnDisc R p pₖ → HasSeriesOnDisc R q qₖ →
    ∀ (a₀ a₁ : ℂ) (a : ℕ → ℂ), a 0 = a₀ → a 1 = a₁ →
    OrdinaryRecurrence pₖ qₖ a → ∃ y : ℂ → ℂ,
      IsOrdinarySolution R p q a₀ a₁ y ∧ a = taylorCoeff y ∧
      HasSeriesOnDisc R y a ∧
      ∀ v, IsOrdinarySolution R p q a₀ a₁ v → Set.EqOn v y (disc R)

end Specs.D13Unified.Ch09.OrdinarySeries
