import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.ConvexProgramModels
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Independent statements for paper.tex, Examples `ex:nonattained-dual`
and `ex:positive-gap` (2211–2230). These are concrete real-data versions
of the common-domain model: real Lagrangians on the stated domain, infima
and suprema in `EReal`. In particular the domain does not change at λ = 0.
The scalar subtype `{λ : ℝ // 0 ≤ λ}` is exactly the admissible multiplier
space for one nonlinear inequality and no affine constraints. -/
noncomputable section
open scoped Classical
open Set
namespace VariationalNotes.Ch04.BoundaryExamplesSpecs

def squareFeasible : Set ℝ := {x | x ^ 2 ≤ 0}
def squareLagrangian (lam x : ℝ) : ℝ := x + lam * x ^ 2
def squarePrimal : EReal := ⨅ x : squareFeasible, (x.val : EReal)
def squareDualFunction (lam : ℝ) : EReal :=
  ⨅ x : ℝ, (squareLagrangian lam x : EReal)
def squareDual : EReal := ⨆ lam : {lam : ℝ // 0 ≤ lam}, squareDualFunction lam

/-- The `WithTop` data use exactly the upstream epigraph convention. -/
def squareObjectiveExtended (x : ℝ) : WithTop ℝ := x
def squareConstraintExtended (x : ℝ) : WithTop ℝ := ((x ^ 2 : ℝ) : WithTop ℝ)

def positiveDomain : Set (ℝ × ℝ) := {z | 0 < z.2}
def exponentialObjective (z : ℝ × ℝ) : ℝ := Real.exp (-z.1)
def perspectiveConstraint (z : ℝ × ℝ) : ℝ := z.1 ^ 2 / z.2
def perspectiveFeasible : Set (ℝ × ℝ) :=
  {z | z ∈ positiveDomain ∧ perspectiveConstraint z ≤ 0}
def perspectiveLagrangian (lam : ℝ) (z : ℝ × ℝ) : ℝ :=
  exponentialObjective z + lam * perspectiveConstraint z
def perspectivePrimal : EReal :=
  ⨅ z : perspectiveFeasible, (exponentialObjective z : EReal)
def perspectiveDualFunction (lam : ℝ) : EReal :=
  ⨅ z : positiveDomain, (perspectiveLagrangian lam z : EReal)
def perspectiveDual : EReal :=
  ⨆ lam : {lam : ℝ // 0 ≤ lam}, perspectiveDualFunction lam

def exponentialObjectiveExtended (z : ℝ × ℝ) : WithTop ℝ :=
  if z ∈ positiveDomain then (exponentialObjective z : WithTop ℝ) else ⊤
def perspectiveConstraintExtended (z : ℝ × ℝ) : WithTop ℝ :=
  if z ∈ positiveDomain then (perspectiveConstraint z : WithTop ℝ) else ⊤

def square_extended_data : Prop :=
  VariationalNotes.ConvexAnalysis.Specs.IsConvex squareObjectiveExtended ∧
  VariationalNotes.ConvexAnalysis.Specs.IsConvex squareConstraintExtended ∧
  VariationalNotes.ConvexAnalysis.Specs.effectiveDomain squareObjectiveExtended = univ ∧
  VariationalNotes.ConvexAnalysis.Specs.effectiveDomain squareConstraintExtended = univ

def perspective_extended_data : Prop :=
  VariationalNotes.ConvexAnalysis.Specs.IsConvex exponentialObjectiveExtended ∧
  VariationalNotes.ConvexAnalysis.Specs.IsConvex perspectiveConstraintExtended ∧
  VariationalNotes.ConvexAnalysis.Specs.effectiveDomain exponentialObjectiveExtended = positiveDomain ∧
  VariationalNotes.ConvexAnalysis.Specs.effectiveDomain perspectiveConstraintExtended = positiveDomain

/-- Feasibility already singles out the unique primal minimizer. -/
def square_primal_solution : Prop :=
  squareFeasible = {0} ∧ squarePrimal = 0 ∧
  (∀ x ∈ squareFeasible, ∀ y ∈ squareFeasible, x ≤ y)

def square_convex_data : Prop :=
  ConvexOn ℝ univ (fun x : ℝ => x) ∧ ConvexOn ℝ univ (fun x : ℝ => x ^ 2)

def square_dual_positive : Prop :=
  ∀ lam : ℝ, 0 < lam → squareDualFunction lam = ((-1 / (4 * lam) : ℝ) : EReal)

def square_dual_zero : Prop := squareDualFunction 0 = ⊥

def square_dual_value : Prop := squareDual = 0

def square_dual_not_attained : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → squareDualFunction lam < squareDual

def perspective_convex_data : Prop :=
  Convex ℝ positiveDomain ∧
  ConvexOn ℝ positiveDomain exponentialObjective ∧
  ConvexOn ℝ positiveDomain perspectiveConstraint

/-- Every feasible point is a minimizer and the entire open ray is retained. -/
def perspective_primal_solution : Prop :=
  (∀ z : ℝ × ℝ, z ∈ perspectiveFeasible ↔ z.1 = 0 ∧ 0 < z.2) ∧
  perspectivePrimal = 1 ∧
  (∀ z ∈ perspectiveFeasible, exponentialObjective z = 1) ∧
  (∀ z ∈ perspectiveFeasible, ∀ w ∈ perspectiveFeasible,
    exponentialObjective z ≤ exponentialObjective w)

def perspective_curve_limit : Prop :=
  ∀ lam : ℝ, Filter.Tendsto
    (fun t : ℝ => perspectiveLagrangian lam (t, t ^ 3))
    Filter.atTop (nhds 0)

def perspective_dual_function : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → perspectiveDualFunction lam = 0

def perspective_dual_value_attained : Prop :=
  perspectiveDual = 0 ∧
  (∀ lam : ℝ, 0 ≤ lam → perspectiveDualFunction lam = perspectiveDual) ∧
  perspectivePrimal - perspectiveDual = 1

end VariationalNotes.Ch04.BoundaryExamplesSpecs
