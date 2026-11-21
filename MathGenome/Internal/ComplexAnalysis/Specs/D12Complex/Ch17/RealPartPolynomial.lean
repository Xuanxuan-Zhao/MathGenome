import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.TaylorSmoothness
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Specs.D12Complex.Ch17.RealPartPolynomial
open _root_.D12Complex

/-- The real-part angular coefficient identity, written as a circle average.
On z = r exp(iθ), division by z^n is r^(-n) exp(-inθ).
Thus this is exactly c_n r^n = π⁻¹ ∫ Re h(r exp(iθ)) exp(-inθ) dθ. -/
def real_part_coefficient_identity_type : Prop :=
  ∀ (h : ℂ → ℂ), HolomorphicOn univ h → ∀ (r : ℝ), 0 < r →
    ∀ (n : ℕ), 1 ≤ n →
    2 * Real.circleAverage (fun z => ((h z).re : ℂ) / z^n) 0 r =
      Taylor.coefficients h 0 n

/-- Any one-sided boundary bound gives the sharp coefficient estimate. -/
def real_part_coefficient_bound_type : Prop :=
  ∀ (h : ℂ → ℂ), HolomorphicOn univ h → ∀ (r B : ℝ), 0 < r →
    (∀ z ∈ sphere (0 : ℂ) r, (h z).re ≤ B) → ∀ (n : ℕ), 1 ≤ n →
    ‖Taylor.coefficients h 0 n‖ * r^n ≤ 2 * (B - (h 0).re)

/-- The maximum exists on each circle, and satisfies the same estimate. -/
def real_part_coefficient_bound_max_type : Prop :=
  ∀ (h : ℂ → ℂ), HolomorphicOn univ h → ∀ (r : ℝ), 0 < r →
    ∃ b ∈ sphere (0 : ℂ) r, (∀ z ∈ sphere (0 : ℂ) r, (h z).re ≤ (h b).re) ∧
      ∀ (n : ℕ), 1 ≤ n →
        ‖Taylor.coefficients h 0 n‖ * r^n ≤ 2 * ((h b).re - (h 0).re)

/-- Bounds only on the selected radii suffice. The exponent need not be integral. -/
def polynomial_of_real_part_growth_type : Prop :=
  ∀ (h : ℂ → ℂ), HolomorphicOn univ h → ∀ (p : ℕ) (t C : ℝ) (r : ℕ → ℝ),
    t < (p : ℝ) + 1 → Tendsto r atTop atTop →
    (∀ k, ∀ z ∈ sphere (0 : ℂ) (r k), (h z).re ≤ C * (r k)^t) →
    (∀ n : ℕ, p < n → Taylor.coefficients h 0 n = 0) ∧
      ∃ Q : Polynomial ℂ, Q.natDegree ≤ p ∧ ∀ z, h z = Q.eval z

/-- Explicit specialization to the finite-order Hadamard parameters. -/
def polynomial_of_finite_order_real_part_growth_type : Prop :=
  ∀ (h : ℂ → ℂ), HolomorphicOn univ h → ∀ (ρ t C : ℝ) (r : ℕ → ℝ),
    0 ≤ ρ → ρ < t → t < (⌊ρ⌋₊ : ℝ) + 1 →
    Tendsto r atTop atTop →
    (∀ k, ∀ z ∈ sphere (0 : ℂ) (r k), (h z).re ≤ C * (r k)^t) →
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ ⌊ρ⌋₊ ∧ ∀ z, h z = Q.eval z

end Specs.D12Complex.Ch17.RealPartPolynomial
