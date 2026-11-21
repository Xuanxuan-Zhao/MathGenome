import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent statements for paper.tex, Proposition d13:09:legendre.
The normalization below is m! times the usual Legendre polynomial; the
source permits arbitrary nonzero normalization. The differential equation
is an identity in ℝ[X], with its original endpoint-degenerate coefficient. -/
namespace D13Unified.Ch09.Legendre

open Polynomial

/-- The spectral parameter in the source equation, including m = 0. -/
def eigenvalue (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) + 1)

/-- Polynomial solutions of the divergence-form Legendre equation. -/
def IsLegendreSolution (m : ℕ) (p : ℝ[X]) : Prop :=
  derivative ((1 - X ^ 2) * derivative p) + C (eigenvalue m) * p = 0

/-- A normalization-free raising construction of the required polynomials. -/
noncomputable def legendre : ℕ → ℝ[X]
  | 0 => 1
  | m + 1 => (X ^ 2 - 1) * derivative (legendre m) +
      C ((m : ℝ) + 1) * X * legendre m

end D13Unified.Ch09.Legendre

namespace Specs.D13Unified.Ch09.Legendre
open Polynomial _root_.D13Unified.Ch09.Legendre

/-- Existence, exact degree, nonvanishing, and the polynomial equation. -/
def legendre_polynomial_type : Prop :=
  ∀ m : ℕ, legendre m ≠ 0 ∧ (legendre m).natDegree = m ∧
    IsLegendreSolution m (legendre m)

/-- Every polynomial solution, including zero, lies in the constructed line. -/
def polynomial_solution_unique_type : Prop :=
  ∀ (m : ℕ) (p : ℝ[X]), IsLegendreSolution m p →
    ∃ c : ℝ, p = C c * legendre m

/-- Nonzero solutions differ by a nonzero scalar. -/
def nonzero_solutions_proportional_type : Prop :=
  ∀ (m : ℕ) (p q : ℝ[X]), p ≠ 0 → q ≠ 0 →
    IsLegendreSolution m p → IsLegendreSolution m q →
    ∃ c : ℝ, c ≠ 0 ∧ p = C c * q

/-- Orthogonality on the source interval for every pair of distinct degrees. -/
def legendre_orthogonal_type : Prop :=
  ∀ m l : ℕ, m ≠ l →
    (∫ x : ℝ in (-1)..1, (legendre m).eval x * (legendre l).eval x) = 0

/-- The same assertion for arbitrary polynomial solutions at those parameters. -/
def polynomial_solutions_orthogonal_type : Prop :=
  ∀ (m l : ℕ) (p q : ℝ[X]), m ≠ l →
    IsLegendreSolution m p → IsLegendreSolution l q →
    (∫ x : ℝ in (-1)..1, p.eval x * q.eval x) = 0

end Specs.D13Unified.Ch09.Legendre
