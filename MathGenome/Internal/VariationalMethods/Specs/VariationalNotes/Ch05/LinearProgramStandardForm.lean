import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramModels
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolyhedraElimination
import Mathlib.Data.Fintype.Sum

/-!
The reduction in paper.tex §v05-01, following Corollary 5.2.
A general coordinate LP has free real variables, finitely many affine
inequalities A x ≤ b, and affine equalities D x = e. All index types may
be empty. Both ≥ inequalities and additional sign constraints are included
by changing a row's sign or adding rows. The objective is cᵀx.

Canonical data and constructions live here so that all theorem specifications
are independent of the implementation. Standard variables are (x⁺,x⁻,s),
with equations A(x⁺−x⁻)+s=b and D(x⁺−x⁻)=e. The dual uses y≤0 for
these ≤ constraints; the usual nonnegative Lagrangian multipliers are −y.
-/
noncomputable section
open Matrix Set
universe u v w
namespace VariationalNotes.Ch05.LinearProgramStandardForm

structure Problem (ι : Type u) (κ : Type v) (ν : Type w) where
  ineq : Matrix ι ν ℝ
  ineqBound : ι → ℝ
  eqn : Matrix κ ν ℝ
  eqBound : κ → ℝ
  cost : ν → ℝ

variable {ι : Type u} {κ : Type v} {ν : Type w}
variable [Fintype ι] [Fintype κ] [Fintype ν]

def feasible (P : Problem ι κ ν) (x : ν → ℝ) : Prop :=
  (∀ i, (P.ineq *ᵥ x) i ≤ P.ineqBound i) ∧ P.eqn *ᵥ x = P.eqBound

def objective (P : Problem ι κ ν) (x : ν → ℝ) : ℝ := P.cost ⬝ᵥ x

def value (P : Problem ι κ ν) : EReal :=
  sInf ((fun x => (objective P x : EReal)) '' {x | feasible P x})

def dualFeasible (P : Problem ι κ ν) (y : ι → ℝ) (z : κ → ℝ) : Prop :=
  (∀ i, y i ≤ 0) ∧ P.ineqᵀ *ᵥ y + P.eqnᵀ *ᵥ z = P.cost

def dualObjective (P : Problem ι κ ν) (y : ι → ℝ) (z : κ → ℝ) : ℝ :=
  P.ineqBound ⬝ᵥ y + P.eqBound ⬝ᵥ z

def dualValue (P : Problem ι κ ν) : EReal :=
  sSup ((fun yz => (dualObjective P yz.1 yz.2 : EReal)) ''
    {yz : (ι → ℝ) × (κ → ℝ) | dualFeasible P yz.1 yz.2})

/-- The two copies of ν are the positive and negative parts; ι indexes slacks. -/
def standardMatrix (P : Problem ι κ ν) : Matrix (ι ⊕ κ) (ν ⊕ (ν ⊕ ι)) ℝ := by
  classical
  exact fun r c => match r, c with
  | .inl i, .inl j => P.ineq i j
  | .inl i, .inr (.inl j) => -P.ineq i j
  | .inl i, .inr (.inr k) => if i = k then 1 else 0
  | .inr i, .inl j => P.eqn i j
  | .inr i, .inr (.inl j) => -P.eqn i j
  | .inr _, .inr (.inr _) => 0

def standardBound (P : Problem ι κ ν) : (ι ⊕ κ) → ℝ :=
  Sum.elim P.ineqBound P.eqBound

def standardCost (P : Problem ι κ ν) : (ν ⊕ (ν ⊕ ι)) → ℝ :=
  Sum.elim P.cost (Sum.elim (-P.cost) 0)

def decode (q : (ν ⊕ (ν ⊕ ι)) → ℝ) : ν → ℝ :=
  fun j => q (.inl j) - q (.inr (.inl j))

/-- A chosen representation; splitting is deliberately not asserted injective. -/
def lift (P : Problem ι κ ν) (x : ν → ℝ) : (ν ⊕ (ν ⊕ ι)) → ℝ :=
  Sum.elim (fun j => max (x j) 0)
    (Sum.elim (fun j => max (-x j) 0) (fun i => P.ineqBound i - (P.ineq *ᵥ x) i))

def joinDual (y : ι → ℝ) (z : κ → ℝ) : (ι ⊕ κ) → ℝ := Sum.elim y z

namespace Specs

-- Closed propositions: all parameters and instances are quantified here.

def decode_lift : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (x : ν → ℝ), decode (lift P x) = x

def standard_feasible_iff : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (q : (ν ⊕ (ν ⊕ ι)) → ℝ),
    LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q ↔
      (∀ j, 0 ≤ q j) ∧ feasible P (decode q) ∧
      ∀ i, q (.inr (.inr i)) = P.ineqBound i - (P.ineq *ᵥ decode q) i

def lift_feasible : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (x : ν → ℝ), feasible P x →
    LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) (lift P x)

def feasible_correspondence : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (x : ν → ℝ), feasible P x ↔
    ∃ q, LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q ∧ decode q = x

def objective_preserved : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (q : (ν ⊕ (ν ⊕ ι)) → ℝ),
    LinearProgramModels.Specs.primalObjective (standardCost P) q = objective P (decode q)

def objective_range_eq : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν),
    (objective P '' {x | feasible P x}) =
    (LinearProgramModels.Specs.primalObjective (standardCost P) ''
      {q | LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q})

def value_preserved : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν),
    value P = LinearProgramModels.Specs.primalValue (standardMatrix P) (standardBound P) (standardCost P)

def optimal_correspondence : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (q : (ν ⊕ (ν ⊕ ι)) → ℝ),
    LinearProgramModels.Specs.PrimalOptimal (standardMatrix P) (standardBound P) (standardCost P) q ↔
    LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q ∧
      feasible P (decode q) ∧ value P = (objective P (decode q) : EReal)

def attainment_correspondence : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (p : ℝ),
    (∃ x, feasible P x ∧ value P = (p : EReal) ∧ objective P x = p) ↔
    LinearProgramModels.Specs.PrimalAttains (standardMatrix P) (standardBound P) (standardCost P) p

def dual_feasible_iff : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (y : ι → ℝ) (z : κ → ℝ),
    LinearProgramModels.Specs.dualFeasible (standardMatrix P) (standardCost P) (joinDual y z) ↔
      dualFeasible P y z

def dual_objective_preserved : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (y : ι → ℝ) (z : κ → ℝ),
    LinearProgramModels.Specs.dualObjective (standardBound P) (joinDual y z) = dualObjective P y z

def dual_value_preserved : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν),
    dualValue P = LinearProgramModels.Specs.dualValue (standardMatrix P) (standardBound P) (standardCost P)

def dual_attainment_correspondence : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ν : Type w} [Fintype ι] [Fintype κ] [Fintype ν],
  ∀ (P : Problem ι κ ν) (p : ℝ),
    (∃ y z, dualFeasible P y z ∧ dualValue P = (p : EReal) ∧ dualObjective P y z = p) ↔
    LinearProgramModels.Specs.DualAttains (standardMatrix P) (standardBound P) (standardCost P) p

/-- Any finite affine-halfspace description in coordinates has the input form.
Equalities, if present, can be left as separate rows in Problem. -/
def polyhedron_representation : Prop :=
  ∀ {ν : Type w} [Fintype ν],
  ∀ (C : Set (ν → ℝ)), ConvexGeometry.Specs.IsPolyhedron C →
    ∃ (m : ℕ) (A : Matrix (Fin m) ν ℝ) (b : Fin m → ℝ),
      C = {x | ∀ i, (A *ᵥ x) i ≤ b i}

/-- Specialize the construction to every polyhedron in finite coordinates,
with no assumptions of feasibility or boundedness. -/
def polyhedron_standard_form : Prop :=
  ∀ {ν : Type w} [Fintype ν] (C : Set (ν → ℝ)) (c : ν → ℝ),
    ConvexGeometry.Specs.IsPolyhedron C →
    ∃ (m : ℕ) (P : Problem (Fin m) Empty ν),
      P.cost = c ∧ {x | feasible P x} = C ∧
      ((fun x => c ⬝ᵥ x) '' C) =
        (LinearProgramModels.Specs.primalObjective (standardCost P) ''
          {q | LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q})

end Specs
end VariationalNotes.Ch05.LinearProgramStandardForm
