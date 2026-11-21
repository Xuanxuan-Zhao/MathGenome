import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramStandardForm

/-! The corrected standard-form correspondence in paper.tex, following W31.
All four finite index types may be empty. Lower rows are negated before the
canonical MathGenome construction splits free coordinates and adds slacks.
The real objective-value sets retain infeasible and unbounded cases. -/
noncomputable section
open Matrix Set
universe u v w z
namespace P205.LinearProgramming.StandardForm
open VariationalNotes.Ch05

structure Problem (E : Type u) (U : Type v) (L : Type w) (N : Type z) where
  equality : Matrix E N ℝ
  equalityBound : E → ℝ
  upper : Matrix U N ℝ
  upperBound : U → ℝ
  lower : Matrix L N ℝ
  lowerBound : L → ℝ
  cost : N → ℝ

variable {E : Type u} {U : Type v} {L : Type w} {N : Type z}
variable [Fintype E] [Fintype U] [Fintype L] [Fintype N]

def feasible (P : Problem E U L N) (x : N → ℝ) : Prop :=
  P.equality *ᵥ x = P.equalityBound ∧
  (∀ i, (P.upper *ᵥ x) i ≤ P.upperBound i) ∧
  (∀ i, P.lowerBound i ≤ (P.lower *ᵥ x) i)

def objective (P : Problem E U L N) (x : N → ℝ) : ℝ := P.cost ⬝ᵥ x

def toProblem (P : Problem E U L N) : LinearProgramStandardForm.Problem (U ⊕ L) E N where
  ineq := Sum.elim P.upper (-P.lower)
  ineqBound := Sum.elim P.upperBound (-P.lowerBound)
  eqn := P.equality
  eqBound := P.equalityBound
  cost := P.cost

abbrev standardMatrix (P : Problem E U L N) := LinearProgramStandardForm.standardMatrix (toProblem P)
abbrev standardBound (P : Problem E U L N) := LinearProgramStandardForm.standardBound (toProblem P)
abbrev standardCost (P : Problem E U L N) := LinearProgramStandardForm.standardCost (toProblem P)
abbrev lift (P : Problem E U L N) (x : N → ℝ) := LinearProgramStandardForm.lift (toProblem P) x
abbrev decode (q : (N ⊕ (N ⊕ (U ⊕ L))) → ℝ) := LinearProgramStandardForm.decode q

def values (P : Problem E U L N) : Set ℝ := objective P '' {x | feasible P x}
def infimum (P : Problem E U L N) : EReal := sInf ((fun t : ℝ => (t : EReal)) '' values P)
def supremum (P : Problem E U L N) : EReal := sSup ((fun t : ℝ => (t : EReal)) '' values P)
def Minimizes (P : Problem E U L N) (x : N → ℝ) : Prop :=
  feasible P x ∧ ∀ y, feasible P y → objective P x ≤ objective P y
def Maximizes (P : Problem E U L N) (x : N → ℝ) : Prop :=
  feasible P x ∧ ∀ y, feasible P y → objective P y ≤ objective P x

def negateCost (P : Problem E U L N) : Problem E U L N := { P with cost := -P.cost }

/-- In the maximization convention upper multipliers are ≥ 0, lower
multipliers are ≤ 0, and equality multipliers have no sign restriction. -/
def maxDualFeasible (P : Problem E U L N) (a : U → ℝ) (d : L → ℝ) (e : E → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∀ i, d i ≤ 0) ∧
  P.upperᵀ *ᵥ a + P.lowerᵀ *ᵥ d + P.equalityᵀ *ᵥ e = P.cost

def maxDualObjective (P : Problem E U L N) (a : U → ℝ) (d : L → ℝ) (e : E → ℝ) : ℝ :=
  P.upperBound ⬝ᵥ a + P.lowerBound ⬝ᵥ d + P.equalityBound ⬝ᵥ e

def maxJoinDual (a : U → ℝ) (d : L → ℝ) (e : E → ℝ) : ((U ⊕ L) ⊕ E) → ℝ :=
  LinearProgramStandardForm.joinDual (Sum.elim (-a) d) (-e)

/-- Append one identity slack column per upper row. -/
def withSlacks {R : Type u} {C : Type v} (A : Matrix R C ℝ) : Matrix R (C ⊕ R) ℝ := by
  classical
  exact fun i => Sum.elim (A i) (fun k => if i = k then 1 else 0)

namespace Specs

def normalization : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, LinearProgramStandardForm.feasible (toProblem P) x ↔ feasible P x

def decode_lift : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, decode (lift P x) = x

def standard_feasible_iff : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) q,
    LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q ↔
    (∀ j, 0 ≤ q j) ∧ feasible P (decode q) ∧
      ∀ i, q (.inr (.inr i)) = (toProblem P).ineqBound i - ((toProblem P).ineq *ᵥ decode q) i

def lift_feasible : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, feasible P x →
    LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) (lift P x)

def feasible_correspondence : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, feasible P x ↔
    ∃ q, LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q ∧ decode q = x

def objective_preserved : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) q,
    LinearProgramModels.Specs.primalObjective (standardCost P) q = objective P (decode q)

def objective_range_eq : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N), values P =
    LinearProgramModels.Specs.primalObjective (standardCost P) '' {q | LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q}

def infimum_preserved : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N), infimum P =
    LinearProgramModels.Specs.primalValue (standardMatrix P) (standardBound P) (standardCost P)

def optimal_correspondence : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) q,
    LinearProgramModels.Specs.PrimalOptimal (standardMatrix P) (standardBound P) (standardCost P) q ↔
    LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q ∧ Minimizes P (decode q)

def attainment_correspondence : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) (p : ℝ),
    (∃ x, Minimizes P x ∧ objective P x = p) ↔
    LinearProgramModels.Specs.PrimalAttains (standardMatrix P) (standardBound P) (standardCost P) p

def infeasible_correspondence : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N), (¬ ∃ x, feasible P x) ↔
    ¬ ∃ q, LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q

def unbounded_correspondence : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N),
    (∀ r : ℝ, ∃ x, feasible P x ∧ objective P x < r) ↔
    LinearProgramModels.Specs.PrimalUnbounded (standardMatrix P) (standardBound P) (standardCost P)

def negation_feasible : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, feasible (negateCost P) x ↔ feasible P x

def negation_objective : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, objective (negateCost P) x = -objective P x

def negation_range : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N), values (negateCost P) = Neg.neg '' values P

/-- Extended-real equality includes the empty set and both infinite values. -/
def negation_value : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N), infimum (negateCost P) = -supremum P

def negation_optimal : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, Minimizes (negateCost P) x ↔ Maximizes P x

def maximization_attainment : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) (p : ℝ),
    (∃ x, Maximizes P x ∧ objective P x = p) ↔
    LinearProgramModels.Specs.PrimalAttains (standardMatrix P) (standardBound P) (standardCost (negateCost P)) (-p)

def maximization_unbounded : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N),
    (∀ r : ℝ, ∃ x, feasible P x ∧ r < objective P x) ↔
    LinearProgramModels.Specs.PrimalUnbounded (standardMatrix P) (standardBound P) (standardCost (negateCost P))

/-- An iff, quantified over every real equality multiplier, makes its freedom
explicit. For a lower row the sign is reversed; for an upper row it is positive. -/
def maximization_dual : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) a d e,
    LinearProgramModels.Specs.dualFeasible (standardMatrix P) (standardCost (negateCost P)) (maxJoinDual a d e) ↔
    maxDualFeasible P a d e

/-- Every canonical dual vector is represented by signed original row
multipliers; the dual sign correspondence loses no points. -/
def max_dual_surjective : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (_P : Problem E U L N) (r : ((U ⊕ L) ⊕ E) → ℝ),
    ∃ a d e, maxJoinDual a d e = r

def maximization_dual_objective : Prop :=
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) a d e,
    LinearProgramModels.Specs.dualObjective (standardBound P) (maxJoinDual a d e) = -maxDualObjective P a d e

/-- Covers the signs used when variables of a matching model are already
nonnegative, rather than free: max c·x, Ax+s=b gives potentials p≥0,
Aᵀp≥c; with no slack, p is free. -/
def nonnegative_max_dual : Prop :=
  ∀ {R : Type u} {C : Type v} [Fintype R] [Fintype C]
    (A : Matrix R C ℝ) (c : C → ℝ) (p : R → ℝ),
    (LinearProgramModels.Specs.dualFeasible (withSlacks A)
      (Sum.elim (-c) 0) (-p) ↔ (∀ i, 0 ≤ p i) ∧ ∀ j, c j ≤ (Aᵀ *ᵥ p) j) ∧
    (LinearProgramModels.Specs.dualFeasible A (-c) (-p) ↔ ∀ j, c j ≤ (Aᵀ *ᵥ p) j)

end Specs
end P205.LinearProgramming.StandardForm
