import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! P206 W34. All matrices and directions are real, with arbitrary natural
 dimensions, including zero. Matrices act on Euclidean coordinate spaces.
 The total ring inverse agrees with the genuine inverse when the Gram operator
 is a unit; invertibility is a conclusion under full column rank. -/
noncomputable section
open scoped Matrix.Norms.L2Operator

namespace NumAnalysis206.LeastSquaresDefinitions
open NumAnalysis206.MatrixDefinitions

def operator {m n : ℕ} (A : Mat ℝ m n) : Vec ℝ n →L[ℝ] Vec ℝ m :=
  A.toEuclideanLin.toContinuousLinearMap

def gram {m n : ℕ} (A : Mat ℝ m n) : Vec ℝ n →L[ℝ] Vec ℝ n :=
  (operator A).adjoint.comp (operator A)

def inverseGram {m n : ℕ} (A : Mat ℝ m n) : Vec ℝ n →L[ℝ] Vec ℝ n :=
  Ring.inverse (gram A)

/-- Full-column-rank left pseudoinverse `(A* A)⁻¹ A*`. -/
def leftInverse {m n : ℕ} (A : Mat ℝ m n) : Vec ℝ m →L[ℝ] Vec ℝ n :=
  (inverseGram A).comp (operator A).adjoint

def solution {m n : ℕ} (p : Mat ℝ m n × Vec ℝ m) : Vec ℝ n :=
  leftInverse p.1 p.2

def residual {m n : ℕ} (A : Mat ℝ m n) (b : Vec ℝ m) : Vec ℝ m :=
  b - operator A (solution (A, b))

end NumAnalysis206.LeastSquaresDefinitions

namespace Specs.NumAnalysis206.LeastSquaresDerivative
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.LeastSquaresDefinitions

def gram_invertible : Prop :=
  ∀ {m n : ℕ} (A : Mat ℝ m n), FullColumnRank A →
    IsUnit (gram A) ∧ (inverseGram A) * gram A = 1 ∧ gram A * inverseGram A = 1

/-- Identify the operator representation with the ordinary normal-equation
 formula using the canonical adjoint on linear maps. -/
def solution_eq_normal_formula : Prop :=
  ∀ {m n : ℕ} (A : Mat ℝ m n) (b : Vec ℝ m), FullColumnRank A →
    solution (A, b) =
      Ring.inverse ((LinearMap.adjoint A.toEuclideanLin).comp A.toEuclideanLin)
        (LinearMap.adjoint A.toEuclideanLin b)

def fullColumnRank_nearby : Prop :=
  ∀ {m n : ℕ} (A : Mat ℝ m n), FullColumnRank A →
    ∀ᶠ B in nhds A, FullColumnRank B

/-- A bounded real-linear derivative on BOTH matrix and rhs directions. Its
 value is the residual formula in W34, without a positive-dimension assumption. -/
def hasFDerivAt_solution : Prop :=
  ∀ {m n : ℕ} (A : Mat ℝ m n) (b : Vec ℝ m), FullColumnRank A →
    ∃ L : (Mat ℝ m n × Vec ℝ m) →L[ℝ] Vec ℝ n,
      HasFDerivAt solution L (A, b) ∧
      ∀ (E : Mat ℝ m n) (f : Vec ℝ m),
        L (E, f) =
          leftInverse A (f - operator E (solution (A, b))) +
          inverseGram A ((operator E).adjoint (residual A b))

end Specs.NumAnalysis206.LeastSquaresDerivative
