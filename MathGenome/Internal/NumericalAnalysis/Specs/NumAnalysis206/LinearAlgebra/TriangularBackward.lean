import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Operations
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.GammaProducts
import Mathlib.Data.Finset.Sort

/-! W21, paper.tex 775–803. A trace records actual rounded primitives and their
safe exact results. `forward = true` means lower triangular forward substitution;
`false` means upper triangular backward substitution. A row may enumerate its
already determined coordinates in any order, each exactly once. This includes
both usual sequential orders. No error factors or backward certificate are
assumed in the execution predicate. All dimensions, including zero, are allowed.
-/
noncomputable section
open scoped BigOperators
namespace NumAnalysis206.LinearAlgebra.TriangularSolve
open MatrixDefinitions

/-- Coordinates available before row i is solved. -/
def predecessors {n : ℕ} (forward : Bool) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => if forward then j < i else i < j)

/-- A one-based column lookup, with an unused default outside 1,...,k. -/
def column {n : ℕ} {forward : Bool} {i : Fin n}
    (e : Fin (predecessors forward i).card ≃ ↥(predecessors forward i))
    (t : ℕ) : Fin n :=
  if h : t - 1 < (predecessors forward i).card then (e ⟨t - 1, h⟩).val else i

/-- An actual safe sequential multiply-subtract trace, followed by one division.
The quotient denominator is separately required nonzero in the theorem. -/
def SafeRun {n : ℕ} (round : ℝ → ℝ) (D : Set ℝ) (forward : Bool)
    (T : Mat ℝ n n) (b x : Fin n → ℝ) : Prop :=
  ∀ i, ∃ (e : Fin (predecessors forward i).card ≃ ↥(predecessors forward i))
      (s : ℕ → ℝ),
    s 0 = b i ∧
    (∀ t ∈ Finset.Icc 1 (predecessors forward i).card,
      T i (column e t) * x (column e t) ∈ D ∧
      s (t - 1) - round (T i (column e t) * x (column e t)) ∈ D ∧
      s t = round (s (t - 1) - round (T i (column e t) * x (column e t)))) ∧
    s (predecessors forward i).card / T i i ∈ D ∧
    x i = round (s (predecessors forward i).card / T i i)

end NumAnalysis206.LinearAlgebra.TriangularSolve

namespace Specs.NumAnalysis206.LinearAlgebra.TriangularBackward
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.LinearAlgebra.TriangularSolve

/-- The complete componentwise backward error statement, with the shared W06
budget's real value written explicitly so the Specs are implementation independent. -/
def backwardError : Prop :=
  ∀ {n : ℕ} (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ) (forward : Bool)
    (T : Mat ℝ n n) (b x : Fin n → ℝ),
    _root_.NumAnalysis206.Rounding.Specs.RelativeModelValue round u D →
    (if forward then IsLowerTriangular T else IsUpperTriangular T) →
    (∀ i, T i i ≠ 0) →
    SafeRun round D forward T b x → (n : ℝ) * u < 1 →
    ∃ Δ : Mat ℝ n n,
      (T + Δ).mulVec x = b ∧
      (∀ i j, |Δ i j| ≤ ((n : ℝ) * u / (1 - (n : ℝ) * u)) * |T i j|) ∧
      (∀ i j, T i j = 0 → Δ i j = 0) ∧
      (if forward then IsLowerTriangular Δ else IsUpperTriangular Δ)

end Specs.NumAnalysis206.LinearAlgebra.TriangularBackward
