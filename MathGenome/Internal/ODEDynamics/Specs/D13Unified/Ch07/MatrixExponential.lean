import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

namespace D13Unified.Ch07

variable {𝕂 n E : Type*} [RCLike 𝕂] [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace 𝕂 E] [FiniteDimensional 𝕂 E]

/-- Interpret a matrix in a basis of the state space with its fixed, arbitrary norm. -/
def matrixOperatorEquiv (b : Module.Basis n 𝕂 E) :
    Matrix n n 𝕂 ≃ₐ[𝕂] (E →L[𝕂] E) :=
  (Matrix.toLinAlgEquiv b).trans (Module.End.toContinuousLinearMap (𝕜 := 𝕂) E)

/-- The induced operator norm, rather than an entrywise matrix norm. -/
def matrixOperatorNorm (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂) : ℝ :=
  ‖matrixOperatorEquiv b A‖

end D13Unified.Ch07

namespace Specs.D13Unified.Ch07.MatrixExponential

universe u v w

/-- Square matrices over either real or complex scalars, with real time. -/
def exponentialType :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n],
    Matrix n n 𝕂 → ℝ → Matrix n n 𝕂

/-- The chosen exponential is the existing topological-algebra exponential. -/
def exponentialValue : exponentialType :=
  fun A t => NormedSpace.exp (t • A)

/-- The source series converges to the chosen exponential. -/
def seriesType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) (t : ℝ),
    HasSum (fun j : ℕ => (t ^ j / (Nat.factorial j : ℝ)) • A ^ j)
      (exponentialValue A t)

/-- The defining equality as an infinite sum. -/
def tsumType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) (t : ℝ),
    exponentialValue A t = ∑' j : ℕ, (t ^ j / (Nat.factorial j : ℝ)) • A ^ j

/-- Changing from matrices to operators preserves the chosen exponential.
The norm on the state space is arbitrary, and completeness follows from finite dimension. -/
def operatorType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [FiniteDimensional 𝕂 E]
    (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂) (t : ℝ),
    D13Unified.Ch07.matrixOperatorEquiv b (exponentialValue A t) =
      NormedSpace.exp ((algebraMap ℝ 𝕂 t) • D13Unified.Ch07.matrixOperatorEquiv b A)

/-- The operator realization has exactly the usual coordinate matrix action. -/
def actionType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [FiniteDimensional 𝕂 E]
    (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂) (x : E),
    b.equivFun (D13Unified.Ch07.matrixOperatorEquiv b A x) = A.mulVec (b.equivFun x)

/-- Compatibility of the fixed vector norm and its induced matrix norm. -/
def normType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [FiniteDimensional 𝕂 E]
    (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂) (x : E),
    ‖D13Unified.Ch07.matrixOperatorEquiv b A x‖ ≤
      D13Unified.Ch07.matrixOperatorNorm b A * ‖x‖

end Specs.D13Unified.Ch07.MatrixExponential
