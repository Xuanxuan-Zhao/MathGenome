import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramModels

/-! Independent statements for the finite-optimum and infeasibility clauses of
paper.tex, Theorem p205:W31. The canonical model is Ax = b, x ≥ 0, with
unrestricted dual variable y and Aᵀy ≤ c. All finite index types may be empty.
A finite infimum is equality of the extended-real value to a real number. -/

noncomputable section
open Matrix
universe u v
namespace P205.LinearProgramming.Certificates.Specs
open VariationalNotes.Ch05.LinearProgramModels.Specs

def gap_identity : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c x : n → ℝ) (y : m → ℝ),
    primalFeasible A b x →
    primalObjective c x - dualObjective b y = ∑ i, x i * (c i - (Aᵀ *ᵥ y) i)

def gap_nonnegative : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c x : n → ℝ) (y : m → ℝ),
    primalFeasible A b x → dualFeasible A c y →
    0 ≤ primalObjective c x - dualObjective b y

def weak_duality : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c x : n → ℝ) (y : m → ℝ),
    primalFeasible A b x → dualFeasible A c y →
    dualObjective b y ≤ primalObjective c x

def objective_eq_iff_complementarity : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c x : n → ℝ) (y : m → ℝ),
    primalFeasible A b x → dualFeasible A c y →
    (primalObjective c x = dualObjective b y ↔
      ∀ i, x i * (c i - (Aᵀ *ᵥ y) i) = 0)

/-- Either equality of objectives or coordinatewise complementarity suffices.
Optimality means feasibility and attainment of the canonical infimum/supremum,
so it compares with every feasible point, without a bounded-region hypothesis. -/
def optimality_certificate : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c x : n → ℝ) (y : m → ℝ),
    primalFeasible A b x → dualFeasible A c y →
    (primalObjective c x = dualObjective b y ∨
      ∀ i, x i * (c i - (Aᵀ *ᵥ y) i) = 0) →
    PrimalOptimal A b c x ∧ DualOptimal A b c y

def finite_infimum_attained : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (p : ℝ),
    (∃ x, primalFeasible A b x) → primalValue A b c = (p : EReal) →
    ∃ x y, PrimalOptimal A b c x ∧ DualOptimal A b c y ∧
      primalObjective c x = p ∧ dualObjective b y = p

def infeasible_iff_certificate : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ),
    (¬ ∃ x, primalFeasible A b x) ↔
      ∃ u : m → ℝ, 0 ≤ Aᵀ *ᵥ u ∧ b ⬝ᵥ u < 0

end P205.LinearProgramming.Certificates.Specs
