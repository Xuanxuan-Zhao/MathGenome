import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.ReflexiveWeakCompactness
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.PNat.Equiv
import Mathlib.Topology.Semicontinuity.Basic

/-! The example “Norm continuity alone”, paper.tex 1441–1454.
`positiveIndex n = n+1` explicitly identifies the ℕ coordinates with the
manuscript's positive integer coordinates. All series below are ordinary real
series on the actual square-summable sequence space. -/
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
namespace VariationalNotes.Existence.NormContinuousNonattainment.Specs

abbrev Space := lp (fun _ : ℕ => ℝ) 2

def positiveIndex : ℕ ≃ ℕ+ := Equiv.pnatEquivNat.symm

def weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def quadratic (x : Space) : ℝ := ∑' n : ℕ, (x n) ^ 2 / ((n : ℝ) + 1)

def objective (x : Space) : ℝ := 1 - ‖x‖ ^ 2 + quadratic x

def feasible : Set Space := {x | ‖x‖ ≤ 1}

def unitVector (n : ℕ) : Space := lp.single 2 n 1

abbrev positiveIndexType := ℕ ≃ ℕ+
abbrev weightType := ℕ → ℝ
abbrev quadraticType := Space → ℝ
abbrev objectiveType := Space → ℝ
abbrev feasibleType := Set Space
abbrev unitVectorType := ℕ → Space

def index_shift : Prop := ∀ n, (positiveIndex n : ℕ) = n + 1

def positive_index_formula : Prop := ∀ x : Space,
  quadratic x = ∑' j : ℕ+, (x (positiveIndex.symm j)) ^ 2 / (j : ℝ)

def series_and_diagonal : Prop :=
  (∀ x : Space, Summable (fun n : ℕ => (x n) ^ 2 / ((n : ℝ) + 1))) ∧
  ∃ D : Space →L[ℝ] Space, ‖D‖ ≤ 1 ∧
    (∀ x n, D x n = weight n * x n) ∧
    (∀ x, quadratic x = inner ℝ x (D x))

def quadratic_bounds : Prop := ∀ x : Space,
  0 ≤ quadratic x ∧ quadratic x ≤ ‖x‖ ^ 2 ∧ (quadratic x = 0 ↔ x = 0)

def norm_continuous : Prop := Continuous objective

def positive_on_ball : Prop := ∀ x ∈ feasible, 0 < objective x

def unit_values : Prop := ∀ n, unitVector n ∈ feasible ∧
  objective (unitVector n) = 1 / ((n : ℝ) + 1)

def infimum_zero : Prop := IsGLB (objective '' feasible) 0 ∧ sInf (objective '' feasible) = 0

def no_minimum : Prop := ¬ ∃ x ∈ feasible, ∀ y ∈ feasible, objective x ≤ objective y

def weak_unit_limit : Prop :=
  Tendsto (fun n => toWeakSpace ℝ Space (unitVector n)) atTop
    (𝓝 (toWeakSpace ℝ Space 0))

def zero_and_value_limit : Prop := objective 0 = 1 ∧
  Tendsto (fun n => objective (unitVector n)) atTop (𝓝 0)

/-- Failure even of lower semicontinuity relative to the feasible ball. -/
def not_weak_lowerSemicontinuous : Prop :=
  ¬ LowerSemicontinuousOn
    (fun x : WeakSpace ℝ Space => objective ((toWeakSpace ℝ Space).symm x))
    ((toWeakSpace ℝ Space) '' feasible)

def ball_geometry : Prop :=
  IsClosed feasible ∧ Bornology.IsBounded feasible ∧
    IsCompact ((toWeakSpace ℝ Space) '' feasible)

end VariationalNotes.Existence.NormContinuousNonattainment.Specs
