import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramModels

/-! Independent statements for paper.tex, Corollary `cor:lp-alternatives`.
Rows and columns are arbitrary finite types, including empty types. Unboundedness
uses the canonical definitions of arbitrarily low or high feasible real objectives.
-/
noncomputable section
open Matrix
universe u v
namespace VariationalNotes.Ch05.LinearProgramAlternatives.Specs
open VariationalNotes.Ch05.LinearProgramModels.Specs

def both_feasible : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ),
    (∃ x, primalFeasible A b x) → (∃ y, dualFeasible A c y) →
    ∃ p : ℝ, PrimalAttains A b c p ∧ DualAttains A b c p ∧
      primalValue A b c = (p : EReal) ∧ dualValue A b c = (p : EReal)

def primal_only_unbounded : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ),
    (∃ x, primalFeasible A b x) → (¬ ∃ y, dualFeasible A c y) →
    PrimalUnbounded A b c

def dual_only_unbounded : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ),
    (¬ ∃ x, primalFeasible A b x) → (∃ y, dualFeasible A c y) →
    DualUnbounded A b c

/-- The manuscript's explicit one-dimensional example A = 0, b = 1, c = -1. -/
def both_infeasible_example : Prop :=
  (¬ ∃ x : Fin 1 → ℝ,
    primalFeasible (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1) x) ∧
  (¬ ∃ y : Fin 1 → ℝ,
    dualFeasible (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => -1) y)

end VariationalNotes.Ch05.LinearProgramAlternatives.Specs
