import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.SmoothConstraintModels
import Mathlib.Order.Filter.Extr

/-! Independent statements for paper.tex:2964–2981. All examples have domain ℝ,
no equality constraints, and the shared convention g ≤ 0 and L = f + ∑ λᵢgᵢ.
The finite function space of inequality multipliers is the usual coordinate
space; the equality multiplier space is the singleton (Fin 0 → ℝ). -/
noncomputable section
universe u v
namespace VariationalNotes.Ch06.Specs

/-- Nonnegative, zero-product complementary coefficients, positive on every
active inequality. This adds strictness to ordinary complementarity. -/
def StrictComplementarity {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} (g : I → X → ℝ) (x : X) (lam : I → ℝ) : Prop :=
  (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i x = 0) ∧
    ∀ i ∈ activeSet g x, 0 < lam i

def StrictComplementarityType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} (g : I → X → ℝ) (x : X) (lam : I → ℝ), Prop

def boundary_examples_smooth : Prop :=
  SmoothConstraintData Set.univ (fun x : ℝ => -x) (fun (_ : Fin 2) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) ∧
  SmoothConstraintData Set.univ (fun x : ℝ => x ^ 2) (fun (_ : Fin 1) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) ∧
  SmoothConstraintData Set.univ (fun x : ℝ => x) (fun (_ : Fin 1) (x : ℝ) => x ^ 2) (fun (_ : Fin 0) (_ : ℝ) => 0)

def duplicate_minimum : Prop :=
  IsMinOn (fun x : ℝ => -x) (feasibleSet Set.univ (fun (_ : Fin 2) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0)) 0

def duplicate_mfcq : Prop :=
  MFCQ Set.univ (fun (_ : Fin 2) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) 0

def duplicate_kkt_iff : Prop :=
  ∀ lam : Fin 2 → ℝ,
  KKT Set.univ (fun x : ℝ => -x) (fun (_ : Fin 2) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) 0 lam (fun (_ : Fin 0) => (0 : ℝ)) ↔
    (∀ i, 0 ≤ lam i) ∧ lam 0 + lam 1 = 1

def duplicate_multiplier_compact_nonunique : Prop :=
  IsCompact {lam : Fin 2 → ℝ | KKT Set.univ (fun x : ℝ => -x) (fun (_ : Fin 2) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) 0 lam (fun (_ : Fin 0) => (0 : ℝ))} ∧
  ∃ lam mu : Fin 2 → ℝ, KKT Set.univ (fun x : ℝ => -x) (fun (_ : Fin 2) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) 0 lam (fun (_ : Fin 0) => (0 : ℝ)) ∧
    KKT Set.univ (fun x : ℝ => -x) (fun (_ : Fin 2) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) 0 mu (fun (_ : Fin 0) => (0 : ℝ)) ∧ lam ≠ mu

def squareObjective_minimum : Prop :=
  IsMinOn (fun x : ℝ => x ^ 2) (feasibleSet Set.univ (fun (_ : Fin 1) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0)) 0

def squareObjective_licq : Prop :=
  LICQ Set.univ (fun (_ : Fin 1) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) 0

def squareObjective_kkt_iff : Prop :=
  ∀ lam : Fin 1 → ℝ,
  KKT Set.univ (fun x : ℝ => x ^ 2) (fun (_ : Fin 1) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) 0 lam (fun (_ : Fin 0) => (0 : ℝ)) ↔ lam = 0

def squareObjective_not_strict : Prop :=
  KKT Set.univ (fun x : ℝ => x ^ 2) (fun (_ : Fin 1) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0) 0 0 (fun (_ : Fin 0) => (0 : ℝ)) ∧
  ¬ StrictComplementarity (fun (_ : Fin 1) (x : ℝ) => x) 0 (0 : Fin 1 → ℝ)

def squaredConstraint_feasible : Prop :=
  feasibleSet Set.univ (fun (_ : Fin 1) (x : ℝ) => x ^ 2) (fun (_ : Fin 0) (_ : ℝ) => 0) = {0}

def squaredConstraint_minimum : Prop :=
  IsMinOn (fun x : ℝ => x) (feasibleSet Set.univ (fun (_ : Fin 1) (x : ℝ) => x ^ 2) (fun (_ : Fin 0) (_ : ℝ) => 0)) 0

def squaredConstraint_no_kkt : Prop :=
  ∀ lam : Fin 1 → ℝ, ¬ KKT Set.univ (fun x : ℝ => x) (fun (_ : Fin 1) (x : ℝ) => x ^ 2) (fun (_ : Fin 0) (_ : ℝ) => 0) 0 lam (fun (_ : Fin 0) => (0 : ℝ))

def squaredConstraint_abnormal : Prop :=
  FritzJohn Set.univ (fun x : ℝ => x) (fun (_ : Fin 1) (x : ℝ) => x ^ 2) (fun (_ : Fin 0) (_ : ℝ) => 0) 0 0
  (fun (_ : Fin 1) => 1) (fun (_ : Fin 0) => (0 : ℝ))

end VariationalNotes.Ch06.Specs
