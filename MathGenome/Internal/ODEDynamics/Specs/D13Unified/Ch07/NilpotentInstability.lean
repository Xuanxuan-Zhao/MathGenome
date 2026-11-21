import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.ExponentialCalculus
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section

namespace D13Unified.Ch07

/-- The size-two nilpotent Jordan block. Over `ℂ` this is the complexification
of the real matrix in the example. -/
def nilpotentMatrix (𝕂 : Type*) [RCLike 𝕂] : Matrix (Fin 2) (Fin 2) 𝕂 :=
  !![0, 1; 0, 0]

/-- The exponential orbit, expressed in a basis of a space with its fixed norm. -/
def nilpotentFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Module.Basis (Fin 2) ℝ E) (x : E) (t : ℝ) : E :=
  matrixOperatorEquiv b
    (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue (nilpotentMatrix ℝ) t) x

end D13Unified.Ch07

namespace Specs.D13Unified.Ch07.NilpotentInstability

open _root_.D13Unified.Ch07

universe u

/-- The exponential formula, including its real specialization. -/
def exponentialType : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] (t : ℝ),
    MatrixExponential.exponentialValue (nilpotentMatrix 𝕂) t =
      !![1, algebraMap ℝ 𝕂 t; 0, 1]

/-- Zero is an eigenvalue and there are no others, over either scalar field. -/
def eigenvalueType : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] (μ : 𝕂),
    Module.End.HasEigenvalue (Matrix.toLin' (nilpotentMatrix 𝕂)) μ ↔ μ = 0

/-- The same exponential gives a global classical solution for every initial state. -/
def solutionType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Module.Basis (Fin 2) ℝ E) (x : E),
    nilpotentFlow b x 0 = x ∧ ContDiff ℝ 1 (nilpotentFlow b x) ∧
      ∀ t : ℝ, HasDerivAt (nilpotentFlow b x)
        (matrixOperatorEquiv b (nilpotentMatrix ℝ) (nilpotentFlow b x t)) t

/-- An escape from one fixed neighborhood from arbitrarily small positive
second-coordinate initial data, in any fixed norm. -/
def escapeType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Module.Basis (Fin 2) ℝ E),
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧ ‖η • b 1‖ < δ ∧
        0 ≤ 1 / η ∧
        b.equivFun (nilpotentFlow b (η • b 1) (1 / η)) 0 = 1 ∧
        ε₀ ≤ ‖nilpotentFlow b (η • b 1) (1 / η)‖

/-- One actual forward solution is unbounded. Together with `eigenvalueType`
this is the counterexample to the nonpositive real-part test. -/
def unboundedType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Module.Basis (Fin 2) ℝ E),
    ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ M < ‖nilpotentFlow b (b 1) t‖

end Specs.D13Unified.Ch07.NilpotentInstability
