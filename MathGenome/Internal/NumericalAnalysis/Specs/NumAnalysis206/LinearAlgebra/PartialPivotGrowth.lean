import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.PivotedLU
import Mathlib.Basic.NNReal.Basic

/-! Exact partial pivoting, including skipped columns. The history contains the
whole matrix at each scan stage, hence both its trailing matrix and all rows
already stored in U. Exchanges record (destination row, selected source row).
No growth estimate or factorization is assumed in the execution relation. -/
noncomputable section
namespace NumAnalysis206.PartialPivotGrowth
open NumAnalysis206.MatrixDefinitions NumAnalysis206.PivotedLU

/-- Largest absolute input entry, zero for the empty matrix. -/
def maxAbs {n : ℕ} (A : Mat ℝ n n) : ℝ :=
  (Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) : NNReal)

/-- A nonzero largest-magnitude available pivot; optionally the first maximizer. -/
def PivotChoice {n : ℕ} (first : Bool) (A : Mat ℝ n n)
    (r q d : Fin n) : Prop :=
  r ≤ q ∧ A q d ≠ 0 ∧
  (∀ i, r ≤ i → |A i d| ≤ |A q d|) ∧
  (first = true → ∀ i, r ≤ i → |A i d| = |A q d| → q ≤ i)

/-- A complete exact partial-pivoting scan, with its actual matrices and swaps. -/
inductive PartialRun {n : ℕ} (first : Bool) : ℕ → ℕ → Mat ℝ n n →
    Mat ℝ n n → List (Mat ℝ n n) → List (Fin n × Fin n) → Prop where
  | stop {r c A} (hz : ∀ i : Fin n, r ≤ i.val → ∀ j, A i j = 0) :
      PartialRun first r c A A [A] []
  | skip {r c A U history swaps} (hc : c < n)
      (hz : ∀ i : Fin n, r ≤ i.val → A i ⟨c, hc⟩ = 0)
      (tail : PartialRun first r (c + 1) A U history swaps) :
      PartialRun first r c A U (A :: history) swaps
  | pivot {r c A U history swaps} (hr : r < n) (hc : c < n) (q : Fin n)
      (choice : PivotChoice first A ⟨r, hr⟩ q ⟨c, hc⟩)
      (tail : PartialRun first (r + 1) (c + 1)
        (eliminate A ⟨r, hr⟩ q ⟨c, hc⟩) U history swaps) :
      PartialRun first r c A U (A :: history) ((⟨r, hr⟩, q) :: swaps)

/-- Wilkinson's matrix: ones on the diagonal and in the last column,
minus ones below the diagonal outside the last column, zero elsewhere. -/
def wilkinson (n : ℕ) : Mat ℝ n n := fun i j =>
  if j.val + 1 = n then 1 else if i = j then 1 else if j < i then -1 else 0
end NumAnalysis206.PartialPivotGrowth

namespace Specs.NumAnalysis206.PartialPivotGrowth
open _root_.NumAnalysis206.MatrixDefinitions _root_.NumAnalysis206.PivotedLU
  _root_.NumAnalysis206.PartialPivotGrowth

/-- W23 first half: all intermediate entries and all final U entries. -/
def partial_pivot_growth : Prop :=
  ∀ {n : ℕ} (A : Mat ℝ n n), A ≠ 0 →
    ∀ (first : Bool) (U : Mat ℝ n n) history swaps,
      PartialRun first 0 0 A U history swaps →
      (∀ B ∈ history, ∀ i j, |B i j| ≤ 2 ^ (n - 1) * maxAbs A) ∧
      (∀ i j, |U i j| ≤ 2 ^ (n - 1) * maxAbs A)

/-- This refinement genuinely performs the upstream exact elimination. -/
def partial_run_to_lu : Prop :=
  ∀ {n : ℕ} {first r c A U history swaps},
    PartialRun (n := n) first r c A U history swaps →
    ∃ p L ps, Run r c A p L U ps

/-- Partial pivoting exists for every input, with either tie convention. -/
def partial_run_exists : Prop :=
  ∀ {n : ℕ} (first : Bool) (A : Mat ℝ n n),
    ∃ U history swaps, PartialRun first 0 0 A U history swaps

/-- The stated bound is attained in every positive dimension under first-row
 tie breaking, with no row exchanges and input maximum exactly one. -/
def wilkinson_sharpness : Prop :=
  ∀ n : ℕ, ∀ hn : 0 < n,
    wilkinson n ≠ 0 ∧ maxAbs (wilkinson n) = 1 ∧
    ∃ U history swaps,
      PartialRun true 0 0 (wilkinson n) U history swaps ∧
      (∀ s ∈ swaps, s.1 = s.2) ∧
      U ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = (2 : ℝ) ^ (n - 1)
end Specs.NumAnalysis206.PartialPivotGrowth
