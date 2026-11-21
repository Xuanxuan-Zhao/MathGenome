import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LocalExtr

/-! The coordinate with natural index `n` is positive coordinate `j = n + 1`
in the manuscript. In particular there is no extra zeroth coordinate. -/
noncomputable section
open scoped ContDiff

namespace VariationalNotes.Ch06.InfiniteHessian

abbrev H := lp (fun _ : ℕ => ℝ) 2

/-- `2⁻ʲ`, with `j = n + 1`. -/
def weight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

def quadratic (x : H) : ℝ := ∑' n, weight n * (x n) ^ 2

def F (x : H) : ℝ := (1 / 2 : ℝ) * quadratic x - ‖x‖ ^ 4

/-- `2^(-j/2) e_j`, with `j = n + 1`. -/
def witness (n : ℕ) : H := lp.single 2 n (Real.sqrt (weight n))

namespace Specs

/-- The full infinite dimensional Hessian counterexample, including convergence
of the defining series and a bounded continuous bilinear representation. -/
def properties : Prop :=
  ¬ FiniteDimensional ℝ H ∧
  (∀ n : ℕ, weight n = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) ∧
  (∀ n : ℕ, Real.sqrt (weight n) = (2 : ℝ) ^ (-((n : ℝ) + 1) / 2)) ∧
  (∀ x : H, Summable (fun n => weight n * (x n) ^ 2)) ∧
  (∃ B : H →L[ℝ] H →L[ℝ] ℝ,
    (∀ x y, B x y = ∑' n, weight n * x n * y n) ∧
    (∀ x y, B x y = B y x) ∧
    (∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) ∧
    (∀ x, quadratic x = B x x)) ∧
  Continuous quadratic ∧
  (∀ x, 0 ≤ quadratic x ∧ quadratic x ≤ ‖x‖ ^ 2) ∧
  ContDiff ℝ ∞ F ∧
  fderiv ℝ F 0 = 0 ∧
  (∀ h : H, fderiv ℝ (fderiv ℝ F) 0 h h = quadratic h) ∧
  (∀ h : H, h ≠ 0 → 0 < quadratic h) ∧
  F 0 = 0 ∧
  (∀ n, F (witness n) = -(weight n) ^ 2 / 2 ∧
    F (witness n) = -(2 : ℝ) ^ (-((2 * (n + 1) : ℕ) : ℤ)) / 2 ∧
    F (witness n) < F 0) ∧
  Filter.Tendsto witness Filter.atTop (nhds 0) ∧
  ¬ IsLocalMin F 0 ∧
  ¬ (∃ m : ℝ, 0 < m ∧ ∀ h : H,
    m * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) 0 h h)

end Specs
end VariationalNotes.Ch06.InfiniteHessian
