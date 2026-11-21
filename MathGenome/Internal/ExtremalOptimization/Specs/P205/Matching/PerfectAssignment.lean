import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.BipartiteHulls
import MathGenome.Internal.ExtremalOptimization.Specs.P205.LinearProgramming.Certificates

/-! Independent statements for paper.tex W40. All coordinates are actual allowed
edges. The degree equations include both entire vertex parts. Potentials and
edge weights are arbitrary real numbers; finite types may be empty. -/
universe u v
noncomputable section
open scoped BigOperators
open Matrix
namespace P205.Matching.AssignmentSpecs
open Specs.P205.Matching
open VariationalNotes.Ch05.LinearProgramModels.Specs

variable {L : Type u} {R : Type v} [Fintype L] [Fintype R]

def matrix (G : BipartiteGraph L R) : Matrix (L ⊕ R) (Edge G) ℝ :=
  (incidence G).map (Int.cast : ℤ → ℝ)

def multiplier (u : L → ℝ) (v : R → ℝ) : L ⊕ R → ℝ :=
  Sum.elim (fun i => -u i) (fun j => -v j)

def degree_lp : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R],
  ∀ (G : BipartiteGraph L R) (x : Edge G → ℝ),
    primalFeasible (matrix G) (fun _ => 1) x ↔
      (∀ e, 0 ≤ x e) ∧ ∀ z, load x z = 1

def dual_sign : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R],
  ∀ (G : BipartiteGraph L R) (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ),
    dualFeasible (matrix G) (fun e => -w e) (multiplier u v) ↔ FreeFeasible w u v

def objective_bridge : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R],
  ∀ (G : BipartiteGraph L R) (w x : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ),
    primalObjective (fun e => -w e) x = -totalWeight w x ∧
      dualObjective (fun _ => 1) (multiplier u v) = -potentialSum u v

def lp_optimizer : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R],
  ∀ (G : BipartiteGraph L R) (w : Edge G → ℝ),
    (∃ M : Set (Edge G), IsPerfectMatching M) →
    ∃ M : Set (Edge G), IsPerfectMatching M ∧
      ∀ x : Edge G → ℝ, (∀ e, 0 ≤ x e) → (∀ z, load x z = 1) →
        totalWeight w x ≤ matchingWeight w M

def weak_duality : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R],
  ∀ (G : BipartiteGraph L R) (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ),
    IsPerfectMatching M → FreeFeasible w u v → matchingWeight w M ≤ potentialSum u v

def gap_identity : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R],
  ∀ (G : BipartiteGraph L R) (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ),
    IsPerfectMatching M →
      potentialSum u v - matchingWeight w M = ∑ e, indicator M e * slack w u v e

def equality_iff_tight : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R],
  ∀ (G : BipartiteGraph L R) (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ),
    IsPerfectMatching M → FreeFeasible w u v →
      (matchingWeight w M = potentialSum u v ↔ UsesTightEdges w M u v)

/-- Attained max/min, with bounds against every competing matching and every
feasible pair of unrestricted vertex potentials. -/
def attained_duality : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R],
  ∀ (G : BipartiteGraph L R) (w : Edge G → ℝ),
    (∃ M : Set (Edge G), IsPerfectMatching M) →
    ∃ (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ),
      IsPerfectMatching M ∧ FreeFeasible w u v ∧
      matchingWeight w M = potentialSum u v ∧
      (∀ N : Set (Edge G), IsPerfectMatching N → matchingWeight w N ≤ matchingWeight w M) ∧
      (∀ (a : L → ℝ) (b : R → ℝ), FreeFeasible w a b → potentialSum u v ≤ potentialSum a b)

def joint_optimal_iff_tight : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R],
  ∀ (G : BipartiteGraph L R) (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ),
    IsPerfectMatching M → FreeFeasible w u v →
      (((∀ N : Set (Edge G), IsPerfectMatching N → matchingWeight w N ≤ matchingWeight w M) ∧
        (∀ (a : L → ℝ) (b : R → ℝ), FreeFeasible w a b → potentialSum u v ≤ potentialSum a b)) ↔
      UsesTightEdges w M u v)

end P205.Matching.AssignmentSpecs
