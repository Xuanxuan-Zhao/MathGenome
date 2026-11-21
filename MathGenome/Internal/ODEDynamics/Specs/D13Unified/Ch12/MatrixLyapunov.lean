import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.MatrixExponential
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator

namespace D13Unified.Ch12

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- All complex eigenvalues of a real matrix are in the open left half-plane. -/
def IsHurwitz (A : Matrix n n ℝ) : Prop :=
  ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) μ →
    μ.re < 0

/-- The integrand uses exactly the Chapter 7 exponential. -/
def lyapunovIntegrand (A Q : Matrix n n ℝ) (t : ℝ) : Matrix n n ℝ :=
  Specs.D13Unified.Ch07.MatrixExponential.exponentialValue A.transpose t * Q *
    Specs.D13Unified.Ch07.MatrixExponential.exponentialValue A t

/-- Lebesgue integral on the positive half-line; convergence is a separate conclusion. -/
def lyapunovIntegral (A Q : Matrix n n ℝ) : Matrix n n ℝ :=
  ∫ t : ℝ in Set.Ioi 0, lyapunovIntegrand A Q t

end D13Unified.Ch12

namespace Specs.D13Unified.Ch12.MatrixLyapunov
open _root_.D13Unified.Ch12
universe u

/-- Over the reals `Matrix.PosDef` includes symmetry and strict positivity
of the quadratic form for every nonzero real vector. There is no assumed
stability or candidate solution certificate. -/
def equivalenceType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ),
    IsHurwitz A ↔ ∀ Q : Matrix n n ℝ, Q.PosDef →
      ∃ P : Matrix n n ℝ, P.PosDef ∧ A.transpose * P + P * A = -Q

/-- For each prescribed positive definite Q the convergent integral gives the
positive definite solution, unique even among all real matrices. -/
def integralType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (A Q : Matrix n n ℝ),
    IsHurwitz A → Q.PosDef →
      IntegrableOn (lyapunovIntegrand A Q) (Set.Ioi 0) ∧
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, lyapunovIntegrand A Q t)
        atTop (𝓝 (lyapunovIntegral A Q)) ∧
      (lyapunovIntegral A Q).PosDef ∧
      A.transpose * lyapunovIntegral A Q + lyapunovIntegral A Q * A = -Q ∧
      ∀ P : Matrix n n ℝ, A.transpose * P + P * A = -Q →
        P = lyapunovIntegral A Q

/-- The converse also holds for a single prescribed positive definite Q. -/
def converseType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (A P Q : Matrix n n ℝ),
    P.PosDef → Q.PosDef → A.transpose * P + P * A = -Q → IsHurwitz A

end Specs.D13Unified.Ch12.MatrixLyapunov
