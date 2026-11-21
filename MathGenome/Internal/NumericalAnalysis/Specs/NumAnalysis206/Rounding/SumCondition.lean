import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Exact componentwise conditioning of a finite real sum (paper W08).
A vector `Fin n → ℝ` represents the ordered input list, including `n = 0`.
All operations here are exact real operations; no rounding model is assumed. -/
namespace NumAnalysis206.Rounding.SumCondition

open scoped BigOperators

/-- The exact sum of the input list. -/
def exactSum {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i

/-- Sum of the componentwise input scales. -/
def sumMagnitude {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, |x i|

/-- Each input is allowed an absolute perturbation at most `ε` times its magnitude. -/
def IsComponentwisePerturbation {n : ℕ} (x : Fin n → ℝ) (ε : ℝ)
    (δ : Fin n → ℝ) : Prop := ∀ i, |δ i| ≤ ε * |x i|

/-- Actual change of the exact sum when the input is perturbed. -/
def sumChange {n : ℕ} (x δ : Fin n → ℝ) : ℝ :=
  exactSum (fun i => x i + δ i) - exactSum x

/-- A specified perturbation with all changes aligned positively. -/
def alignedPerturbation {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) : Fin n → ℝ :=
  fun i => ε * |x i|

/-- All attainable absolute changes for the specified perturbation budget. -/
def absoluteChanges {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) : Set ℝ :=
  {a | ∃ δ, IsComponentwisePerturbation x ε δ ∧ a = |sumChange x δ|}

/-- All attainable relative output changes divided by the relative input budget.
The relative theorems use this only when `ε > 0` and `exactSum x ≠ 0`. -/
def relativeAmplifications {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) : Set ℝ :=
  {r | ∃ δ, IsComponentwisePerturbation x ε δ ∧
    r = |sumChange x δ| / (ε * |exactSum x|)}

/-- Worst-case componentwise relative amplification at unit budget.
The relative-maximum theorem establishes the same maximum at every positive
budget, so this definition also gives the arbitrarily small-budget condition. -/
noncomputable def componentwiseSumCondition {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (relativeAmplifications x 1)

namespace SumConditionSpecs

def absoluteBound : Prop :=
  ∀ {n : ℕ} (x : Fin n → ℝ) (ε : ℝ), 0 ≤ ε →
    ∀ δ, IsComponentwisePerturbation x ε δ → |sumChange x δ| ≤ ε * sumMagnitude x

def alignedAttains : Prop :=
  ∀ {n : ℕ} (x : Fin n → ℝ) (ε : ℝ), 0 ≤ ε →
    IsComponentwisePerturbation x ε (alignedPerturbation x ε) ∧
      |sumChange x (alignedPerturbation x ε)| = ε * sumMagnitude x

def absoluteMaximum : Prop :=
  ∀ {n : ℕ} (x : Fin n → ℝ) (ε : ℝ), 0 ≤ ε →
    IsGreatest (absoluteChanges x ε) (ε * sumMagnitude x)

def relativeMaximum : Prop :=
  ∀ {n : ℕ} (x : Fin n → ℝ), exactSum x ≠ 0 →
    ∀ ε : ℝ, 0 < ε →
      IsGreatest (relativeAmplifications x ε) (sumMagnitude x / |exactSum x|)

def conditionFormula : Prop :=
  ∀ {n : ℕ} (x : Fin n → ℝ), exactSum x ≠ 0 →
    componentwiseSumCondition x = sumMagnitude x / |exactSum x|

/-- At a zero output scale we retain the absolute statement and its witness. -/
def zeroSumMaximum : Prop :=
  ∀ {n : ℕ} (x : Fin n → ℝ), exactSum x = 0 →
    ∀ ε : ℝ, 0 ≤ ε →
      IsGreatest (absoluteChanges x ε) (ε * sumMagnitude x) ∧
      IsComponentwisePerturbation x ε (alignedPerturbation x ε) ∧
      |exactSum (fun i => x i + alignedPerturbation x ε i)| = ε * sumMagnitude x

end SumConditionSpecs
end NumAnalysis206.Rounding.SumCondition
