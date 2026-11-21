import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramModels

/-! Independent statements for paper.tex, Theorem 5.1 (2238–2272).
The types indexing rows and columns are arbitrary finite types, possibly empty.
The hypothesis says that the canonical extended-real primal infimum is real.
No dual feasibility, rank condition, or bounded feasible region is assumed. -/
noncomputable section
open Matrix
universe u v
namespace VariationalNotes.Ch05.LinearProgramDuality.Specs
open VariationalNotes.Ch05.LinearProgramModels.Specs

def strong_duality : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (p : ℝ),
    (∃ x, primalFeasible A b x) → primalValue A b c = (p : EReal) →
    PrimalAttains A b c p ∧ DualAttains A b c p ∧
      primalValue A b c = dualValue A b c ∧ dualValue A b c = (p : EReal)

def feasible_pair_gap : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ),
    primalFeasible A b x → dualFeasible A c y →
    primalObjective c x - dualObjective b y = ∑ i, x i * (c i - (Aᵀ *ᵥ y) i)

def gap_zero_iff_complementarity : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ),
    primalFeasible A b x → dualFeasible A c y →
    (primalObjective c x - dualObjective b y = 0 ↔
      ∀ i, x i * (c i - (Aᵀ *ᵥ y) i) = 0)

def zero_gap_certificate : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ),
    primalFeasible A b x → dualFeasible A c y →
    primalObjective c x - dualObjective b y = 0 →
    PrimalOptimal A b c x ∧ DualOptimal A b c y

end VariationalNotes.Ch05.LinearProgramDuality.Specs
