import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

noncomputable section
namespace NumAnalysis206.MatrixConditionDefinitions
open MatrixDefinitions

/-- Euclidean condition number of a rectangular matrix, using its canonical
Moore–Penrose inverse. The theorem below applies to full column rank. -/
def conditionNumber {m n : ℕ} (A : Mat ℝ m n) : ℝ :=
  operatorNorm A * operatorNorm (pseudoinverse A)

/-- For an invertible square matrix the ordinary inverse defines κ₂. -/
def squareConditionNumber {n : ℕ} (A : Mat ℝ n n) : ℝ :=
  operatorNorm A * operatorNorm A⁻¹
end NumAnalysis206.MatrixConditionDefinitions

namespace Specs.NumAnalysis206.GramConditionSquared
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.MatrixConditionDefinitions

def conditionNumber_type := ∀ {m n : ℕ}, Mat ℝ m n → ℝ
def conditionNumber_value : conditionNumber_type := @conditionNumber

def squareConditionNumber_type := ∀ {n : ℕ}, Mat ℝ n n → ℝ
def squareConditionNumber_value : squareConditionNumber_type := @squareConditionNumber

/-- W31, condition-number assertion. The smallest singular value is the last
DOMAIN singular value, even when the matrix is tall. Square κ uses the actual
matrix inverse and both norms are Euclidean operator norms. -/
def gram_condition_squared : Prop :=
  ∀ {m n : ℕ} (A : Mat ℝ m n), 0 < n → FullColumnRank A →
    0 < singularValue A n ∧
    conditionNumber A = singularValue A 1 / singularValue A n ∧
    squareConditionNumber (adjoint A * A) = conditionNumber A ^ 2
end Specs.NumAnalysis206.GramConditionSquared
