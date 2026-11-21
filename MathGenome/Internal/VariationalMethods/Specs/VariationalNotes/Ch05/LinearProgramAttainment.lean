import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramModels

/-! Primal-attainment part of paper.tex, Theorem 5.1 (lines 2238–2272).
The finite index types may be empty. The value is the canonical extended-real
infimum, and its being real is stated by equality to the coercion of `p`.
No rank, boundedness, or strict-feasibility assumption is imposed. -/

noncomputable section
universe u v
namespace VariationalNotes.Ch05.LinearProgramAttainment.Specs

open VariationalNotes.Ch05.LinearProgramModels.Specs

def primal_attainment : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (p : ℝ),
    (∃ x, primalFeasible A b x) →
    primalValue A b c = (p : EReal) → PrimalAttains A b c p

end VariationalNotes.Ch05.LinearProgramAttainment.Specs
