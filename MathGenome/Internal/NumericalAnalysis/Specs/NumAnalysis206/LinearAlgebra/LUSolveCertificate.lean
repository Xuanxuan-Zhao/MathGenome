import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.DoolittleBackward
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.TriangularBackward

/-! W23, solve certificate and its Chapter 2 forward corollary.
All vector norms below are Euclidean and matrix norms are their subordinate
operator norms. An equivalence E with the displayed matrix action represents
an invertible A, including the unique map in dimension zero. -/
noncomputable section
namespace Specs.NumAnalysis206.LinearAlgebra.LUSolveCertificate
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.LinearAlgebra.Doolittle
open _root_.NumAnalysis206.LinearAlgebra.TriangularSolve
open _root_.NumAnalysis206.PivotedLU

/-- The full direct forward bound, with no division by a zero solution scale. -/
def ForwardGuarantee {n : ℕ} (A Δ : Mat ℝ n n) (b xhat : Fin n → ℝ) : Prop :=
  ∀ E : Vec ℝ n ≃L[ℝ] Vec ℝ n,
    E.toContinuousLinearMap = A.toEuclideanLin.toContinuousLinearMap →
    let β := ‖E.symm.toContinuousLinearMap‖ * operatorNorm Δ
    β < 1 →
    let x := E.symm (WithLp.toLp 2 b)
    ‖WithLp.toLp 2 xhat - x‖ ≤ β * ‖x‖ / (1 - β) ∧
    (b ≠ 0 → ‖WithLp.toLp 2 xhat - x‖ / ‖x‖ ≤ β / (1 - β)) ∧
    (b = 0 → xhat = 0 ∧ x = 0)

/-- Specialization of W11 to zero right-hand-side perturbation. -/
def forward_error : Prop :=
  ∀ {n : ℕ} (A Δ : Mat ℝ n n) (b xhat : Fin n → ℝ),
    (A + Δ).mulVec xhat = b → ForwardGuarantee A Δ b xhat

/-- A safe actual factorization and two actual triangular executions give one
certificate, in both permuted and original coordinates, and the direct forward
corollary. There is no pivot-growth assumption. -/
def solve_certificate : Prop :=
  ∀ {n : ℕ} (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ) (A : Mat ℝ n n),
    _root_.NumAnalysis206.Rounding.Specs.RelativeModelValue round u D →
    (R : Run round D A) → (3 * (n : ℝ)) * u < 1 →
    (b y xhat : Fin n → ℝ) →
    (∀ i, R.upper i i ≠ 0) →
    SafeRun round D true R.lower
      ((permutationMatrix R.permutation).mulVec b) y →
    SafeRun round D false R.upper y xhat →
    ∃ Δsolve : Mat ℝ n n,
      (permutationMatrix R.permutation * A + Δsolve).mulVec xhat =
        (permutationMatrix R.permutation).mulVec b ∧
      EntrywiseLE (entrywiseAbs Δsolve)
        ((Specs.NumAnalysis206.Rounding.gammaValue (3 * n) u +
          2 * Specs.NumAnalysis206.Rounding.gammaValue n u +
          Specs.NumAnalysis206.Rounding.gammaValue n u ^ 2) •
          (entrywiseAbs R.lower * entrywiseAbs R.upper)) ∧
      (A + permutationMatrix R.permutation.symm * Δsolve).mulVec xhat = b ∧
      ForwardGuarantee A (permutationMatrix R.permutation.symm * Δsolve) b xhat

end Specs.NumAnalysis206.LinearAlgebra.LUSolveCertificate
