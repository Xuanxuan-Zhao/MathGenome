import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.Models
import MathGenome.Internal.ExtremalOptimization.Specs.P205.LinearProgramming.Certificates

/-! W41 (paper.tex 1902--1920). All vertices and allowed edges are retained.
There is no perfect matching or nonnegative weight hypothesis. The standard
primal minimizes the negative weight, with one nonnegative degree slack per
vertex. The dual variable is the negative of the nonnegative vertex potential. -/
noncomputable section
open scoped BigOperators
open Matrix
universe u v
namespace P205.Matching.WeightedSpecs
open Specs.P205.Matching
open VariationalNotes.Ch05.LinearProgramModels.Specs

variable {L : Type u} {R : Type v} [Fintype L] [Fintype R]

/-- Columns consist of allowed edges and all vertex slacks. -/
def standardMatrix (G : BipartiteGraph L R) :
    Matrix (L ⊕ R) (Edge G ⊕ (L ⊕ R)) ℝ := by
  classical
  exact fun z => Sum.elim (fun e => (incidence G z e : ℝ))
    (fun t => if z = t then 1 else 0)

def standardCost {G : BipartiteGraph L R} (w : Edge G → ℝ) :
    Edge G ⊕ (L ⊕ R) → ℝ := Sum.elim (-w) (fun _ => 0)

def lift {G : BipartiteGraph L R} (x : Edge G → ℝ) :
    Edge G ⊕ (L ⊕ R) → ℝ := Sum.elim x (fun z => 1 - load x z)

/-- Both sides are quantified over all matchings / all feasible potentials. -/
def JointOptimal {G : BipartiteGraph L R} (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ) : Prop :=
  (∀ N, IsMatching N → matchingWeight w N ≤ matchingWeight w M) ∧
  ∀ a b, NonnegativeFeasible w a b → potentialSum u v ≤ potentialSum a b

def Certificate {G : BipartiteGraph L R} (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ) : Prop :=
  UsesTightEdges w M u v ∧
    (∀ i, ¬ Covered M (.inl i) → u i = 0) ∧
    ∀ j, ¬ Covered M (.inr j) → v j = 0

def primal_correspondence : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (q : Edge G ⊕ (L ⊕ R) → ℝ),
    primalFeasible (standardMatrix G) (fun _ => 1) q ↔
      (∀ e, 0 ≤ q (.inl e)) ∧
      (∀ z, load (fun e => q (.inl e)) z ≤ 1) ∧
      ∀ z, q (.inr z) = 1 - load (fun e => q (.inl e)) z

def dual_correspondence : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ),
    dualFeasible (standardMatrix G) (standardCost w) (-Sum.elim u v) ↔
      NonnegativeFeasible w u v

def objective_correspondence : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (w : Edge G → ℝ)
    (q : Edge G ⊕ (L ⊕ R) → ℝ) (u : L → ℝ) (v : R → ℝ),
    primalObjective (standardCost w) q = -totalWeight w (fun e => q (.inl e)) ∧
    dualObjective (fun _ : L ⊕ R => 1) (-Sum.elim u v) = -potentialSum u v

def weak_duality : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ),
    IsMatching M → NonnegativeFeasible w u v →
      matchingWeight w M ≤ potentialSum u v

/-- Existence of equal-valued, globally optimal witnesses states both the
maximum matching weight and the attained minimum over feasible potentials. -/
def attained_duality : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (w : Edge G → ℝ),
    ∃ M u v, IsMatching M ∧ NonnegativeFeasible w u v ∧
      matchingWeight w M = potentialSum u v ∧ JointOptimal w M u v

def equality_iff_certificate : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ),
    IsMatching M → NonnegativeFeasible w u v →
      (matchingWeight w M = potentialSum u v ↔ Certificate w M u v)

def joint_optimality_iff_certificate : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ),
    IsMatching M → NonnegativeFeasible w u v →
      (JointOptimal w M u v ↔ Certificate w M u v)

end P205.Matching.WeightedSpecs
