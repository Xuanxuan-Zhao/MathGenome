import MathGenome.Internal.ExtremalOptimization.Specs.P205.LinearProgramming.Certificates

/-! The unboundedness clause of paper.tex, Theorem p205:W31.
The primal is Ax = b, x ≥ 0. All index types are finite and may be empty.
The feasible starting point is essential for the implication from a direction.
-/
noncomputable section
open Matrix
universe u v
namespace P205.LinearProgramming.UnboundedDirection.Specs
open VariationalNotes.Ch05.LinearProgramModels.Specs

/-- Arbitrarily low feasible objective values are equivalent to a nonnegative
null direction with strictly negative cost. -/
def unbounded_iff_direction : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ),
    (∃ x, primalFeasible A b x) →
    ((∀ K : ℝ, ∃ x, primalFeasible A b x ∧ primalObjective c x < K) ↔
      ∃ d : n → ℝ, (∀ i, 0 ≤ d i) ∧ A *ᵥ d = 0 ∧ c ⬝ᵥ d < 0)

/-- The same certificate characterizes the canonical infimum being −∞. -/
def value_eq_bot_iff_direction : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ),
    (∃ x, primalFeasible A b x) →
    (primalValue A b c = ⊥ ↔
      ∃ d : n → ℝ, (∀ i, 0 ≤ d i) ∧ A *ᵥ d = 0 ∧ c ⬝ᵥ d < 0)

end P205.LinearProgramming.UnboundedDirection.Specs
